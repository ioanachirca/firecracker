// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.

use libc::{c_int, c_void, siginfo_t};
use std::cell::Cell;
use std::fmt::{Display, Formatter};
use std::io;
use std::result;
use std::sync::atomic::{fence, Ordering};
use std::sync::{Arc, Barrier};

use super::TimestampUs;
use arch;
#[cfg(target_arch = "aarch64")]
use arch::aarch64::gic::GICDevice;
#[cfg(target_arch = "x86_64")]
use cpuid::{c3, filter_cpuid, t2, VmSpec};
use default_syscalls;
#[cfg(target_arch = "x86_64")]
use kvm_bindings::{kvm_pit_config, CpuId, KVM_MAX_CPUID_ENTRIES, KVM_PIT_SPEAKER_DUMMY};
use kvm_bindings::{kvm_userspace_memory_region, KVM_API_VERSION};
use kvm_ioctls::*;
use logger::{LogOption, Metric, LOGGER, METRICS};
use memory_model::{Address, GuestAddress, GuestMemory, GuestMemoryError};
use utils::eventfd::EventFd;
use utils::signal::{register_signal_handler, SignalHandler};
use vmm_config::machine_config::CpuFeaturesTemplate;

const KVM_MEM_LOG_DIRTY_PAGES: u32 = 0x1;

#[cfg(target_arch = "x86_64")]
const MAGIC_IOPORT_SIGNAL_GUEST_BOOT_COMPLETE: u64 = 0x03f0;
#[cfg(target_arch = "aarch64")]
const MAGIC_IOPORT_SIGNAL_GUEST_BOOT_COMPLETE: u64 = 0x40000000;
const MAGIC_VALUE_SIGNAL_GUEST_BOOT_COMPLETE: u8 = 123;

pub(crate) const VCPU_RTSIG_OFFSET: i32 = 0;

/// Errors associated with the wrappers over KVM ioctls.
#[derive(Debug)]
pub enum Error {
    #[cfg(target_arch = "x86_64")]
    /// A call to cpuid instruction failed.
    CpuId(cpuid::Error),
    /// Invalid guest memory configuration.
    GuestMemory(GuestMemoryError),
    /// Hyperthreading flag is not initialized.
    HTNotInitialized,
    /// The host kernel reports an invalid KVM API version.
    KvmApiVersion(i32),
    /// Cannot initialize the KVM context due to missing capabilities.
    KvmCap(kvm_ioctls::Cap),
    /// vCPU count is not initialized.
    VcpuCountNotInitialized,
    /// Cannot open the VM file descriptor.
    VmFd(kvm_ioctls::Error),
    /// Cannot open the VCPU file descriptor.
    VcpuFd(kvm_ioctls::Error),
    /// Cannot configure the microvm.
    VmSetup(kvm_ioctls::Error),
    /// Cannot run the VCPUs.
    VcpuRun(kvm_ioctls::Error),
    /// The call to KVM_SET_CPUID2 failed.
    SetSupportedCpusFailed(kvm_ioctls::Error),
    /// The number of configured slots is bigger than the maximum reported by KVM.
    NotEnoughMemorySlots,
    #[cfg(target_arch = "x86_64")]
    /// Cannot set the local interruption due to bad configuration.
    LocalIntConfiguration(arch::x86_64::interrupts::Error),
    /// Cannot set the memory regions.
    SetUserMemoryRegion(kvm_ioctls::Error),
    #[cfg(target_arch = "x86_64")]
    /// Error configuring the MSR registers
    MSRSConfiguration(arch::x86_64::regs::Error),
    #[cfg(target_arch = "aarch64")]
    /// Error configuring the general purpose aarch64 registers.
    REGSConfiguration(arch::aarch64::regs::Error),
    #[cfg(target_arch = "x86_64")]
    /// Error configuring the general purpose registers
    REGSConfiguration(arch::x86_64::regs::Error),
    #[cfg(target_arch = "x86_64")]
    /// Error configuring the special registers
    SREGSConfiguration(arch::x86_64::regs::Error),
    #[cfg(target_arch = "x86_64")]
    /// Error configuring the floating point related registers
    FPUConfiguration(arch::x86_64::regs::Error),
    /// Cannot configure the IRQ.
    Irq(kvm_ioctls::Error),
    /// Cannot spawn a new vCPU thread.
    VcpuSpawn(io::Error),
    /// Cannot clean init vcpu TLS.
    VcpuTlsInit,
    /// Vcpu not present in TLS.
    VcpuTlsNotPresent,
    /// Unexpected KVM_RUN exit reason
    VcpuUnhandledKvmExit,
    #[cfg(target_arch = "aarch64")]
    /// Error setting up the global interrupt controller.
    SetupGIC(arch::aarch64::gic::Error),
    #[cfg(target_arch = "aarch64")]
    /// Error getting the Vcpu preferred target on Arm.
    VcpuArmPreferredTarget(kvm_ioctls::Error),
    #[cfg(target_arch = "aarch64")]
    /// Error doing Vcpu Init on Arm.
    VcpuArmInit(kvm_ioctls::Error),
}

extern "C" {
    fn __libc_current_sigrtmin() -> c_int;
}

pub fn sigrtmin() -> c_int {
    unsafe { __libc_current_sigrtmin() }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use self::Error::*;

        match self {
            #[cfg(target_arch = "x86_64")]
            CpuId(e) => write!(f, "Cpuid error: {:?}", e),
            GuestMemory(e) => write!(f, "Guest memory error: {:?}", e),
            HTNotInitialized => write!(f, "Hyperthreading flag is not initialized"),
            KvmApiVersion(v) => write!(
                f,
                "The host kernel reports an invalid KVM API version: {}",
                v
            ),
            KvmCap(cap) => write!(f, "Missing KVM capabilities: {:?}", cap),
            VcpuCountNotInitialized => write!(f, "vCPU count is not initialized"),
            VmFd(e) => write!(f, "Cannot open the VM file descriptor: {}", e),
            VcpuFd(e) => write!(f, "Cannot open the VCPU file descriptor: {}", e),
            VmSetup(e) => write!(f, "Cannot configure the microvm: {}", e),
            VcpuRun(e) => write!(f, "Cannot run the VCPUs: {}", e),
            SetSupportedCpusFailed(e) => write!(f, "The call to KVM_SET_CPUID2 failed: {}", e),
            NotEnoughMemorySlots => write!(
                f,
                "The number of configured slots is bigger than the maximum reported by KVM"
            ),
            #[cfg(target_arch = "x86_64")]
            LocalIntConfiguration(e) => write!(
                f,
                "Cannot set the local interruption due to bad configuration: {:?}",
                e
            ),
            SetUserMemoryRegion(e) => write!(f, "Cannot set the memory regions: {}", e),
            #[cfg(target_arch = "x86_64")]
            MSRSConfiguration(e) => write!(f, "Error configuring the MSR registers: {:?}", e),
            #[cfg(target_arch = "aarch64")]
            REGSConfiguration(e) => write!(
                f,
                "Error configuring the general purpose aarch64 registers: {:?}",
                e
            ),
            #[cfg(target_arch = "x86_64")]
            REGSConfiguration(e) => write!(
                f,
                "Error configuring the general purpose registers: {:?}",
                e
            ),
            #[cfg(target_arch = "x86_64")]
            SREGSConfiguration(e) => write!(f, "Error configuring the special registers: {:?}", e),
            #[cfg(target_arch = "x86_64")]
            FPUConfiguration(e) => write!(
                f,
                "Error configuring the floating point related registers: {:?}",
                e
            ),
            Irq(e) => write!(f, "Cannot configure the IRQ: {}", e),
            VcpuSpawn(e) => write!(f, "Cannot spawn a new vCPU thread: {}", e),
            VcpuTlsInit => write!(f, "Cannot clean init vcpu TLS"),
            VcpuTlsNotPresent => write!(f, "Vcpu not present in TLS"),
            VcpuUnhandledKvmExit => write!(f, "Unexpected KVM_RUN exit reason"),
            #[cfg(target_arch = "aarch64")]
            SetupGIC(e) => write!(
                f,
                "Error setting up the global interrupt controller: {:?}",
                e
            ),
            #[cfg(target_arch = "aarch64")]
            VcpuArmPreferredTarget(e) => {
                write!(f, "Error getting the Vcpu preferred target on Arm: {}", e)
            }
            #[cfg(target_arch = "aarch64")]
            VcpuArmInit(e) => write!(f, "Error doing Vcpu Init on Arm: {}", e),
        }
    }
}

pub type Result<T> = result::Result<T, Error>;

/// Describes a KVM context that gets attached to the microVM.
/// It gives access to the functionality of the KVM wrapper as
/// long as every required KVM capability is present on the host.
pub struct KvmContext {
    kvm: Kvm,
    max_memslots: usize,
}

impl KvmContext {
    pub fn new() -> Result<Self> {
        use kvm_ioctls::Cap::*;
        let kvm = Kvm::new().expect("Error creating the Kvm object");

        // Check that KVM has the correct version.
        if kvm.get_api_version() != KVM_API_VERSION as i32 {
            return Err(Error::KvmApiVersion(kvm.get_api_version()));
        }

        // A list of KVM capabilities we want to check.
        #[cfg(target_arch = "x86_64")]
        let capabilities = vec![Irqchip, Ioeventfd, Irqfd, UserMemory, SetTssAddr];

        #[cfg(target_arch = "aarch64")]
        let capabilities = vec![Irqchip, Ioeventfd, Irqfd, UserMemory, ArmPsci02];

        // Check that all desired capabilities are supported.
        match capabilities
            .iter()
            .find(|&capability| !kvm.check_extension(*capability))
        {
            None => {
                let max_memslots = kvm.get_nr_memslots();
                Ok(KvmContext { kvm, max_memslots })
            }

            Some(c) => Err(Error::KvmCap(*c)),
        }
    }

    pub fn fd(&self) -> &Kvm {
        &self.kvm
    }

    /// Get the maximum number of memory slots reported by this KVM context.
    pub fn max_memslots(&self) -> usize {
        self.max_memslots
    }
}

/// A wrapper around creating and using a VM.
pub struct Vm {
    fd: VmFd,

    // X86 specific fields.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    supported_cpuid: CpuId,

    // Arm specific fields.
    // On aarch64 we need to keep around the fd obtained by creating the VGIC device.
    #[cfg(target_arch = "aarch64")]
    irqchip_handle: Option<Box<dyn GICDevice>>,
}

impl Vm {
    /// Constructs a new `Vm` using the given `Kvm` instance.
    pub fn new(kvm: &Kvm) -> Result<Self> {
        //create fd for interacting with kvm-vm specific functions
        let vm_fd = kvm.create_vm().map_err(Error::VmFd)?;

        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        let supported_cpuid = kvm
            .get_supported_cpuid(KVM_MAX_CPUID_ENTRIES)
            .map_err(Error::VmFd)?;
        Ok(Vm {
            fd: vm_fd,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            supported_cpuid,
            #[cfg(target_arch = "aarch64")]
            irqchip_handle: None,
        })
    }

    /// Returns a ref to the supported `CpuId` for this Vm.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    pub fn supported_cpuid(&self) -> &CpuId {
        &self.supported_cpuid
    }

    /// Initializes the guest memory.
    pub fn memory_init(&mut self, guest_mem: &GuestMemory, kvm_max_memslots: usize) -> Result<()> {
        if guest_mem.num_regions() > kvm_max_memslots {
            return Err(Error::NotEnoughMemorySlots);
        }
        guest_mem
            .with_regions(|index, guest_addr, size, host_addr| {
                info!("Guest memory starts at {:x?}", host_addr);

                let flags = if LOGGER.flags() & LogOption::LogDirtyPages as usize > 0 {
                    KVM_MEM_LOG_DIRTY_PAGES
                } else {
                    0
                };

                let memory_region = kvm_userspace_memory_region {
                    slot: index as u32,
                    guest_phys_addr: guest_addr.raw_value() as u64,
                    memory_size: size as u64,
                    userspace_addr: host_addr as u64,
                    flags,
                };
                // Safe because we mapped the memory region, we made sure that the regions
                // are not overlapping.
                unsafe { self.fd.set_user_memory_region(memory_region) }
            })
            .map_err(Error::SetUserMemoryRegion)?;

        #[cfg(target_arch = "x86_64")]
        self.fd
            .set_tss_address(arch::x86_64::layout::KVM_TSS_ADDRESS as usize)
            .map_err(Error::VmSetup)?;

        Ok(())
    }

    /// Creates the irq chip and an in-kernel device model for the PIT.
    #[cfg(target_arch = "x86_64")]
    pub fn setup_irqchip(&self) -> Result<()> {
        self.fd.create_irq_chip().map_err(Error::VmSetup)?;
        let mut pit_config = kvm_pit_config::default();
        // We need to enable the emulation of a dummy speaker port stub so that writing to port 0x61
        // (i.e. KVM_SPEAKER_BASE_ADDRESS) does not trigger an exit to user space.
        pit_config.flags = KVM_PIT_SPEAKER_DUMMY;
        self.fd.create_pit2(pit_config).map_err(Error::VmSetup)
    }

    /// Creates the GIC (Global Interrupt Controller).
    #[cfg(target_arch = "aarch64")]
    pub fn setup_irqchip(&mut self, vcpu_count: u8) -> Result<()> {
        self.irqchip_handle = Some(
            arch::aarch64::gic::create_gic(&self.fd, vcpu_count.into()).map_err(Error::SetupGIC)?,
        );
        Ok(())
    }

    /// Gets a reference to the irqchip of the VM
    #[cfg(target_arch = "aarch64")]
    pub fn get_irqchip(&self) -> &Box<dyn GICDevice> {
        &self.irqchip_handle.as_ref().unwrap()
    }

    /// Gets a reference to the kvm file descriptor owned by this VM.
    pub fn fd(&self) -> &VmFd {
        &self.fd
    }
}

/// Encapsulates configuration parameters for the guest vCPUS.
pub struct VcpuConfig {
    /// Number of guest VCPUs.
    pub vcpu_count: u8,
    /// Enable hyperthreading in the CPUID configuration.
    pub ht_enabled: bool,
    /// CPUID template to use.
    pub cpu_template: Option<CpuFeaturesTemplate>,
}

// Using this for easier explicit type-casting to help IDEs interpret the code.
type VcpuCell = Cell<Option<*const Vcpu>>;

/// A wrapper around creating and using a kvm-based VCPU.
pub struct Vcpu {
    #[cfg(target_arch = "x86_64")]
    cpuid: CpuId,
    fd: VcpuFd,
    id: u8,
    #[cfg(target_arch = "x86_64")]
    io_bus: devices::Bus,
    mmio_bus: Option<devices::Bus>,
    create_ts: TimestampUs,
    #[cfg(target_arch = "aarch64")]
    mpidr: u64,
}

impl Vcpu {
    thread_local!(static TLS_VCPU_PTR: VcpuCell = Cell::new(None));

    /// Associates `self` with the current thread.
    ///
    /// It is a prerequisite to successfully run `init_thread_local_data()` before using
    /// `run_on_thread_local()` on the current thread.
    /// This function will return an error if there already is a `Vcpu` present in the TLS.
    fn init_thread_local_data(&mut self) -> Result<()> {
        Self::TLS_VCPU_PTR.with(|cell: &VcpuCell| {
            if cell.get().is_some() {
                return Err(Error::VcpuTlsInit);
            }
            cell.set(Some(self as *const Vcpu));
            Ok(())
        })
    }

    /// Deassociates `self` from the current thread.
    ///
    /// Should be called if the current `self` had called `init_thread_local_data()` and
    /// now needs to move to a different thread.
    ///
    /// Fails if `self` was not previously associated with the current thread.
    fn reset_thread_local_data(&mut self) -> Result<()> {
        // Best-effort to clean up TLS. If the `Vcpu` was moved to another thread
        // _before_ running this, then there is nothing we can do.
        Self::TLS_VCPU_PTR.with(|cell: &VcpuCell| {
            if let Some(vcpu_ptr) = cell.get() {
                if vcpu_ptr == self as *const Vcpu {
                    Self::TLS_VCPU_PTR.with(|cell: &VcpuCell| cell.take());
                    return Ok(());
                }
            }
            Err(Error::VcpuTlsNotPresent)
        })
    }

    /// Runs `func` for the `Vcpu` associated with the current thread.
    ///
    /// It requires that `init_thread_local_data()` was run on this thread.
    ///
    /// Fails if there is no `Vcpu` associated with the current thread.
    ///
    /// # Safety
    ///
    /// This is marked unsafe as it allows temporary aliasing through
    /// dereferencing from pointer an already borrowed `Vcpu`.
    unsafe fn run_on_thread_local<F>(func: F) -> Result<()>
    where
        F: FnOnce(&Vcpu),
    {
        Self::TLS_VCPU_PTR.with(|cell: &VcpuCell| {
            if let Some(vcpu_ptr) = cell.get() {
                // Dereferencing here is safe since `TLS_VCPU_PTR` is populated/non-empty,
                // and it is being cleared on `Vcpu::drop` so there is no dangling pointer.
                let vcpu_ref: &Vcpu = &*vcpu_ptr;
                func(vcpu_ref);
                Ok(())
            } else {
                Err(Error::VcpuTlsNotPresent)
            }
        })
    }

    /// Registers a signal handler which makes use of TLS and kvm immediate exit to
    /// kick the vcpu running on the current thread, if there is one.
    pub fn register_kick_signal_handler() {
        extern "C" fn handle_signal(_: c_int, _: *mut siginfo_t, _: *mut c_void) {
            // This is safe because it's temporarily aliasing the `Vcpu` object, but we are
            // only reading `vcpu.fd` which does not change for the lifetime of the `Vcpu`.
            unsafe {
                let _ = Vcpu::run_on_thread_local(|vcpu| {
                    vcpu.fd.set_kvm_immediate_exit(1);
                    fence(Ordering::Release);
                });
            }
        }
        register_signal_handler(sigrtmin() + VCPU_RTSIG_OFFSET, handle_signal)
            .expect("Failed to register vcpu signal handler");
    }

    /// Constructs a new VCPU for `vm`.
    ///
    /// # Arguments
    ///
    /// * `id` - Represents the CPU number between [0, max vcpus).
    /// * `vm_fd` - The kvm `VmFd` for the virtual machine this vcpu will get attached to.
    /// * `cpuid` - The `CpuId` listing the supported capabilities of this vcpu.
    /// * `io_bus` - The io-bus used to access port-io devices.
    /// * `create_ts` - A timestamp used by the vcpu to calculate its lifetime.
    #[cfg(target_arch = "x86_64")]
    pub fn new_x86_64(
        id: u8,
        vm_fd: &VmFd,
        cpuid: CpuId,
        io_bus: devices::Bus,
        create_ts: TimestampUs,
    ) -> Result<Self> {
        let kvm_vcpu = vm_fd.create_vcpu(id).map_err(Error::VcpuFd)?;

        // Initially the cpuid per vCPU is the one supported by this VM.
        Ok(Vcpu {
            cpuid,
            fd: kvm_vcpu,
            id,
            io_bus,
            mmio_bus: None,
            create_ts,
        })
    }

    /// Constructs a new VCPU for `vm`.
    ///
    /// # Arguments
    ///
    /// * `id` - Represents the CPU number between [0, max vcpus).
    /// * `vm_fd` - The kvm `VmFd` for the virtual machine this vcpu will get attached to.
    /// * `create_ts` - A timestamp used by the vcpu to calculate its lifetime.
    #[cfg(target_arch = "aarch64")]
    pub fn new_aarch64(id: u8, vm_fd: &VmFd, create_ts: TimestampUs) -> Result<Self> {
        let kvm_vcpu = vm_fd.create_vcpu(id).map_err(Error::VcpuFd)?;
        Ok(Vcpu {
            fd: kvm_vcpu,
            id,
            mmio_bus: None,
            create_ts,
            mpidr: 0,
        })
    }

    /// Gets the MPIDR register value.
    #[cfg(target_arch = "aarch64")]
    pub fn get_mpidr(&self) -> u64 {
        self.mpidr
    }

    /// Sets a MMIO bus for this vcpu.
    pub fn set_mmio_bus(&mut self, mmio_bus: devices::Bus) {
        self.mmio_bus = Some(mmio_bus);
    }

    #[cfg(target_arch = "x86_64")]
    /// Configures a x86_64 specific vcpu and should be called once per vcpu.
    ///
    /// # Arguments
    ///
    /// * `machine_config` - The machine configuration of this microvm needed for the CPUID configuration.
    /// * `guest_mem` - The guest memory used by this microvm.
    /// * `kernel_start_addr` - Offset from `guest_mem` at which the kernel starts.
    pub fn configure_x86_64(
        &mut self,
        guest_mem: &GuestMemory,
        kernel_start_addr: GuestAddress,
        vcpu_config: &VcpuConfig,
    ) -> Result<()> {
        let cpuid_vm_spec = VmSpec::new(self.id, vcpu_config.vcpu_count, vcpu_config.ht_enabled)
            .map_err(Error::CpuId)?;

        filter_cpuid(&mut self.cpuid, &cpuid_vm_spec).map_err(|e| {
            METRICS.vcpu.filter_cpuid.inc();
            error!("Failure in configuring CPUID for vcpu {}: {:?}", self.id, e);
            Error::CpuId(e)
        })?;

        if let Some(template) = vcpu_config.cpu_template {
            match template {
                CpuFeaturesTemplate::T2 => {
                    t2::set_cpuid_entries(&mut self.cpuid, &cpuid_vm_spec).map_err(Error::CpuId)?
                }
                CpuFeaturesTemplate::C3 => {
                    c3::set_cpuid_entries(&mut self.cpuid, &cpuid_vm_spec).map_err(Error::CpuId)?
                }
            }
        }

        self.fd
            .set_cpuid2(&self.cpuid)
            .map_err(Error::SetSupportedCpusFailed)?;

        arch::x86_64::regs::setup_msrs(&self.fd).map_err(Error::MSRSConfiguration)?;
        arch::x86_64::regs::setup_regs(&self.fd, kernel_start_addr.raw_value() as u64)
            .map_err(Error::REGSConfiguration)?;
        arch::x86_64::regs::setup_fpu(&self.fd).map_err(Error::FPUConfiguration)?;
        arch::x86_64::regs::setup_sregs(guest_mem, &self.fd).map_err(Error::SREGSConfiguration)?;
        arch::x86_64::interrupts::set_lint(&self.fd).map_err(Error::LocalIntConfiguration)?;
        Ok(())
    }

    #[cfg(target_arch = "aarch64")]
    /// Configures an aarch64 specific vcpu.
    ///
    /// # Arguments
    ///
    /// * `vm_fd` - The kvm `VmFd` for this microvm.
    /// * `guest_mem` - The guest memory used by this microvm.
    /// * `kernel_load_addr` - Offset from `guest_mem` at which the kernel is loaded.
    pub fn configure_aarch64(
        &mut self,
        vm_fd: &VmFd,
        guest_mem: &GuestMemory,
        kernel_load_addr: GuestAddress,
    ) -> Result<()> {
        let mut kvi: kvm_bindings::kvm_vcpu_init = kvm_bindings::kvm_vcpu_init::default();

        // This reads back the kernel's preferred target type.
        vm_fd
            .get_preferred_target(&mut kvi)
            .map_err(Error::VcpuArmPreferredTarget)?;
        // We already checked that the capability is supported.
        kvi.features[0] |= 1 << kvm_bindings::KVM_ARM_VCPU_PSCI_0_2;
        // Non-boot cpus are powered off initially.
        if self.id > 0 {
            kvi.features[0] |= 1 << kvm_bindings::KVM_ARM_VCPU_POWER_OFF;
        }

        self.fd.vcpu_init(&kvi).map_err(Error::VcpuArmInit)?;
        arch::aarch64::regs::setup_regs(&self.fd, self.id, kernel_load_addr.raw_value(), guest_mem)
            .map_err(Error::REGSConfiguration)?;

        self.mpidr = arch::aarch64::regs::read_mpidr(&self.fd).map_err(Error::REGSConfiguration)?;

        Ok(())
    }

    fn check_boot_complete_signal(&self, addr: u64, data: &[u8]) {
        if addr == MAGIC_IOPORT_SIGNAL_GUEST_BOOT_COMPLETE
            && data[0] == MAGIC_VALUE_SIGNAL_GUEST_BOOT_COMPLETE
        {
            super::Vmm::log_boot_time(&self.create_ts);
        }
    }

    /// Runs the vCPU in KVM context and handles the kvm exit reason.
    ///
    /// Returns error or enum specifying whether emulation was handled or interrupted.
    fn run_emulation(&mut self) -> Result<VcpuEmulation> {
        match self.fd.run() {
            Ok(run) => match run {
                #[cfg(target_arch = "x86_64")]
                VcpuExit::IoIn(addr, data) => {
                    self.io_bus.read(u64::from(addr), data);
                    METRICS.vcpu.exit_io_in.inc();
                    Ok(VcpuEmulation::Handled)
                }
                #[cfg(target_arch = "x86_64")]
                VcpuExit::IoOut(addr, data) => {
                    self.check_boot_complete_signal(u64::from(addr), data);

                    self.io_bus.write(u64::from(addr), data);
                    METRICS.vcpu.exit_io_out.inc();
                    Ok(VcpuEmulation::Handled)
                }
                VcpuExit::MmioRead(addr, data) => {
                    if let Some(ref mmio_bus) = self.mmio_bus {
                        mmio_bus.read(addr, data);
                        METRICS.vcpu.exit_mmio_read.inc();
                    }
                    Ok(VcpuEmulation::Handled)
                }
                VcpuExit::MmioWrite(addr, data) => {
                    if let Some(ref mmio_bus) = self.mmio_bus {
                        #[cfg(target_arch = "aarch64")]
                        self.check_boot_complete_signal(addr, data);

                        mmio_bus.write(addr, data);
                        METRICS.vcpu.exit_mmio_write.inc();
                    }
                    Ok(VcpuEmulation::Handled)
                }
                VcpuExit::Hlt => {
                    info!("Received KVM_EXIT_HLT signal");
                    Err(Error::VcpuUnhandledKvmExit)
                }
                VcpuExit::Shutdown => {
                    info!("Received KVM_EXIT_SHUTDOWN signal");
                    Err(Error::VcpuUnhandledKvmExit)
                }
                // Documentation specifies that below kvm exits are considered
                // errors.
                VcpuExit::FailEntry => {
                    METRICS.vcpu.failures.inc();
                    error!("Received KVM_EXIT_FAIL_ENTRY signal");
                    Err(Error::VcpuUnhandledKvmExit)
                }
                VcpuExit::InternalError => {
                    METRICS.vcpu.failures.inc();
                    error!("Received KVM_EXIT_INTERNAL_ERROR signal");
                    Err(Error::VcpuUnhandledKvmExit)
                }
                r => {
                    METRICS.vcpu.failures.inc();
                    // TODO: Are we sure we want to finish running a vcpu upon
                    // receiving a vm exit that is not necessarily an error?
                    error!("Unexpected exit reason on vcpu run: {:?}", r);
                    Err(Error::VcpuUnhandledKvmExit)
                }
            },
            // The unwrap on raw_os_error can only fail if we have a logic
            // error in our code in which case it is better to panic.
            Err(ref e) => {
                match e.errno() {
                    libc::EAGAIN => Ok(VcpuEmulation::Handled),
                    libc::EINTR => {
                        self.fd.set_kvm_immediate_exit(0);
                        // Notify that this KVM_RUN was interrupted.
                        Ok(VcpuEmulation::Interrupted)
                    }
                    _ => {
                        METRICS.vcpu.failures.inc();
                        error!("Failure during vcpu run: {}", e);
                        Err(Error::VcpuUnhandledKvmExit)
                    }
                }
            }
        }
    }

    /// Main loop of the vCPU thread.
    ///
    /// Runs the vCPU in KVM context in a loop. Handles KVM_EXITs then goes back in.
    /// Note that the state of the VCPU and associated VM must be setup first for this to do
    /// anything useful.
    pub fn run(
        &mut self,
        thread_barrier: Arc<Barrier>,
        seccomp_level: u32,
        vcpu_exit_evt: EventFd,
    ) {
        self.init_thread_local_data()
            .expect("Cannot cleanly initialize vcpu TLS.");

        // Load seccomp filters for this vCPU thread.
        // Execution panics if filters cannot be loaded, use --seccomp-level=0 if skipping filters
        // altogether is the desired behaviour.
        if let Err(e) = default_syscalls::set_seccomp_level(seccomp_level) {
            panic!(
                "Failed to set the requested seccomp filters on vCPU {}: Error: {}",
                self.id, e
            );
        }

        thread_barrier.wait();

        while self.run_emulation().is_ok() {}

        // Nothing we need do for the success case.
        if let Err(e) = vcpu_exit_evt.write(1) {
            METRICS.vcpu.failures.inc();
            error!("Failed signaling vcpu exit event: {}", e);
        }
    }
}

impl Drop for Vcpu {
    fn drop(&mut self) {
        let _ = self.reset_thread_local_data();
    }
}

enum VcpuEmulation {
    Handled,
    Interrupted,
}

#[cfg(test)]
mod tests {
    use std::fs::File;

    use super::super::devices;
    use super::*;
    use utils::signal::Killable;

    // Auxiliary function being used throughout the tests.
    fn setup_vcpu() -> (Vm, Vcpu, GuestMemory) {
        let kvm = KvmContext::new().unwrap();
        let gm = GuestMemory::new(&[(GuestAddress(0), 0x10000)]).unwrap();
        let mut vm = Vm::new(kvm.fd()).expect("Cannot create new vm");
        assert!(vm.memory_init(&gm, kvm.max_memslots()).is_ok());

        let vcpu;
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            vm.setup_irqchip().unwrap();
            vcpu = Vcpu::new_x86_64(
                1,
                vm.fd(),
                vm.supported_cpuid().clone(),
                devices::Bus::new(),
                super::super::TimestampUs::default(),
            )
            .unwrap();
        }
        #[cfg(target_arch = "aarch64")]
        {
            vcpu = Vcpu::new_aarch64(1, vm.fd(), super::super::TimestampUs::default()).unwrap();
            vm.setup_irqchip(1).expect("Cannot setup irqchip");
        }

        (vm, vcpu, gm)
    }

    #[test]
    fn test_set_mmio_bus() {
        let (_, mut vcpu, _) = setup_vcpu();
        assert!(vcpu.mmio_bus.is_none());
        vcpu.set_mmio_bus(devices::Bus::new());
        assert!(vcpu.mmio_bus.is_some());
    }

    #[test]
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    fn test_get_supported_cpuid() {
        let kvm = KvmContext::new().unwrap();
        let vm = Vm::new(kvm.fd()).expect("Cannot create new vm");
        let cpuid = kvm
            .kvm
            .get_supported_cpuid(KVM_MAX_CPUID_ENTRIES)
            .expect("Cannot get supported cpuid");
        assert_eq!(vm.supported_cpuid().as_slice(), cpuid.as_slice());
    }

    #[test]
    fn test_vm_memory_init() {
        let mut kvm_context = KvmContext::new().unwrap();
        let mut vm = Vm::new(kvm_context.fd()).expect("Cannot create new vm");

        // Create valid memory region and test that the initialization is successful.
        let gm = GuestMemory::new(&[(GuestAddress(0), 0x1000)]).unwrap();
        assert!(vm.memory_init(&gm, kvm_context.max_memslots()).is_ok());

        // Set the maximum number of memory slots to 1 in KvmContext to check the error
        // path of memory_init. Create 2 non-overlapping memory slots.
        kvm_context.max_memslots = 1;
        let gm = GuestMemory::new(&[(GuestAddress(0x0), 0x1000), (GuestAddress(0x1001), 0x2000)])
            .unwrap();
        assert!(vm.memory_init(&gm, kvm_context.max_memslots()).is_err());
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_setup_irqchip() {
        let kvm_context = KvmContext::new().unwrap();
        let vm = Vm::new(kvm_context.fd()).expect("Cannot create new vm");

        vm.setup_irqchip().expect("Cannot setup irqchip");
        // Trying to setup two irqchips will result in EEXIST error. At the moment
        // there is no good way of testing the actual error because io::Error does not implement
        // PartialEq.
        assert!(vm.setup_irqchip().is_err());

        let _vcpu = Vcpu::new_x86_64(
            1,
            vm.fd(),
            vm.supported_cpuid().clone(),
            devices::Bus::new(),
            super::super::TimestampUs::default(),
        )
        .unwrap();
        // Trying to setup irqchip after KVM_VCPU_CREATE was called will result in error.
        assert!(vm.setup_irqchip().is_err());
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_setup_irqchip() {
        let kvm = KvmContext::new().unwrap();

        let mut vm = Vm::new(kvm.fd()).expect("Cannot create new vm");
        let vcpu_count = 1;
        let _vcpu = Vcpu::new_aarch64(1, vm.fd(), super::super::TimestampUs::default()).unwrap();

        vm.setup_irqchip(vcpu_count).expect("Cannot setup irqchip");
        // Trying to setup two irqchips will result in EEXIST error.
        assert!(vm.setup_irqchip(vcpu_count).is_err());
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_configure_vcpu() {
        let (_, mut vcpu, vm_mem) = setup_vcpu();

        let mut vcpu_config = VcpuConfig {
            vcpu_count: 1,
            ht_enabled: false,
            cpu_template: None,
        };

        assert!(vcpu
            .configure_x86_64(&vm_mem, GuestAddress(0), &vcpu_config)
            .is_ok());

        // Test configure while using the T2 template.
        vcpu_config.cpu_template = Some(CpuFeaturesTemplate::T2);
        assert!(vcpu
            .configure_x86_64(&vm_mem, GuestAddress(0), &vcpu_config)
            .is_ok());

        // Test configure while using the C3 template.
        vcpu_config.cpu_template = Some(CpuFeaturesTemplate::C3);
        assert!(vcpu
            .configure_x86_64(&vm_mem, GuestAddress(0), &vcpu_config)
            .is_ok());
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_configure_vcpu() {
        let kvm = KvmContext::new().unwrap();
        let gm = GuestMemory::new(&[(GuestAddress(0), 0x10000)]).unwrap();
        let mut vm = Vm::new(kvm.fd()).expect("new vm failed");
        assert!(vm.memory_init(&gm, kvm.max_memslots()).is_ok());

        // Try it for when vcpu id is 0.
        let mut vcpu = Vcpu::new_aarch64(0, vm.fd(), super::super::TimestampUs::default()).unwrap();

        assert!(vcpu
            .configure_aarch64(vm.fd(), &gm, GuestAddress(0))
            .is_ok());

        // Try it for when vcpu id is NOT 0.
        let mut vcpu = Vcpu::new_aarch64(1, vm.fd(), super::super::TimestampUs::default()).unwrap();

        assert!(vcpu
            .configure_aarch64(vm.fd(), &gm, GuestAddress(0))
            .is_ok());
    }

    #[test]
    #[should_panic]
    fn test_vcpu_run_failed() {
        let (_, mut vcpu, _) = setup_vcpu();
        // Setting an invalid seccomp level should panic.
        vcpu.run(
            Arc::new(Barrier::new(1)),
            seccomp::SECCOMP_LEVEL_ADVANCED + 10,
            EventFd::new(libc::EFD_NONBLOCK).unwrap(),
        );
    }

    #[test]
    fn test_kvm_context() {
        use std::os::unix::fs::MetadataExt;
        use std::os::unix::io::{AsRawFd, FromRawFd};

        let c = KvmContext::new().unwrap();

        assert!(c.max_memslots >= 32);

        let kvm = Kvm::new().unwrap();
        let f = unsafe { File::from_raw_fd(kvm.as_raw_fd()) };
        let m1 = f.metadata().unwrap();
        let m2 = File::open("/dev/kvm").unwrap().metadata().unwrap();

        assert_eq!(m1.dev(), m2.dev());
        assert_eq!(m1.ino(), m2.ino());
    }

    #[test]
    fn test_vcpu_tls() {
        let (_, mut vcpu, _) = setup_vcpu();

        // Running on the TLS vcpu should fail before we actually initialize it.
        unsafe {
            assert!(Vcpu::run_on_thread_local(|_| ()).is_err());
        }

        // Initialize vcpu TLS.
        vcpu.init_thread_local_data().unwrap();

        // Validate TLS vcpu is the local vcpu by changing the `id` then validating against
        // the one in TLS.
        vcpu.id = 12;
        unsafe {
            assert!(Vcpu::run_on_thread_local(|v| assert_eq!(v.id, 12)).is_ok());
        }

        // Reset vcpu TLS.
        assert!(vcpu.reset_thread_local_data().is_ok());

        // Running on the TLS vcpu after TLS reset should fail.
        unsafe {
            assert!(Vcpu::run_on_thread_local(|_| ()).is_err());
        }

        // Second reset should return error.
        assert!(vcpu.reset_thread_local_data().is_err());
    }

    #[test]
    fn test_invalid_tls() {
        let (_, mut vcpu, _) = setup_vcpu();
        // Initialize vcpu TLS.
        vcpu.init_thread_local_data().unwrap();
        // Trying to initialize non-empty TLS should error.
        vcpu.init_thread_local_data().unwrap_err();
    }

    #[test]
    fn test_vcpu_kick() {
        Vcpu::register_kick_signal_handler();
        let (vm, mut vcpu, _mem) = setup_vcpu();

        let kvm_run =
            KvmRunWrapper::mmap_from_fd(&vcpu.fd, vm.fd.run_size()).expect("cannot mmap kvm-run");
        let success = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let vcpu_success = success.clone();
        let barrier = Arc::new(Barrier::new(2));
        let vcpu_barrier = barrier.clone();
        // Start Vcpu thread which will be kicked with a signal.
        let handle = std::thread::Builder::new()
            .name("test_vcpu_kick".to_string())
            .spawn(move || {
                vcpu.init_thread_local_data().unwrap();
                // Notify TLS was populated.
                vcpu_barrier.wait();
                // Loop for max 1 second to check if the signal handler has run.
                for _ in 0..10 {
                    if kvm_run.as_mut_ref().immediate_exit == 1 {
                        // Signal handler has run and set immediate_exit to 1.
                        vcpu_success.store(true, Ordering::Release);
                        break;
                    }
                    std::thread::sleep(std::time::Duration::from_millis(100));
                }
            })
            .expect("cannot start thread");

        // Wait for the vcpu to initialize its TLS.
        barrier.wait();
        // Kick the Vcpu using the custom signal.
        handle
            .kill(sigrtmin() + VCPU_RTSIG_OFFSET)
            .expect("failed to signal thread");
        handle.join().expect("failed to join thread");
        // Verify that the Vcpu saw its kvm immediate-exit as set.
        assert!(success.load(Ordering::Acquire));
    }
}
