// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

extern crate logger;
extern crate utils;

use libc::{_exit, c_int, c_void, siginfo_t, SIGBUS, SIGSEGV, SIGSYS};

use logger::{Metric, LOGGER, METRICS};
use utils::signal::register_signal_handler;

// The offset of `si_syscall` (offending syscall identifier) within the siginfo structure
// expressed as an `(u)int*`.
// Offset `6` for an `i32` field means that the needed information is located at `6 * sizeof(i32)`.
// See /usr/include/linux/signal.h for the C struct definition.
// See https://github.com/rust-lang/libc/issues/716 for why the offset is different in Rust.
const SI_OFF_SYSCALL: isize = 6;

const SYS_SECCOMP_CODE: i32 = 1;

/// Signal handler for `SIGSYS`.
///
/// Increments the `seccomp.num_faults` metric, logs an error message and terminates the process
/// with a specific exit code.
extern "C" fn sigsys_handler(num: c_int, info: *mut siginfo_t, _unused: *mut c_void) {
    // Safe because we're just reading some fields from a supposedly valid argument.
    let si_signo = unsafe { (*info).si_signo };
    let si_code = unsafe { (*info).si_code };

    // Sanity check. The condition should never be true.
    if num != si_signo || num != SIGSYS || si_code != SYS_SECCOMP_CODE as i32 {
        // Safe because we're terminating the process anyway.
        unsafe { _exit(i32::from(super::FC_EXIT_CODE_UNEXPECTED_ERROR)) };
    }

    // Other signals which might do async unsafe things incompatible with the rest of this
    // function are blocked due to the sa_mask used when registering the signal handler.
    let syscall = unsafe { *(info as *const i32).offset(SI_OFF_SYSCALL) as usize };
    METRICS.seccomp.num_faults.inc();
    error!(
        "Shutting down VM after intercepting a bad syscall ({}).",
        syscall
    );
    // Log the metrics before exiting.
    if let Err(e) = LOGGER.log_metrics() {
        error!("Failed to log metrics while stopping: {}", e);
    }

    // Safe because we're terminating the process anyway. We don't actually do anything when
    // running unit tests.
    #[cfg(not(test))]
    unsafe {
        _exit(i32::from(super::FC_EXIT_CODE_BAD_SYSCALL))
    };
}

/// Signal handler for `SIGBUS` and `SIGSEGV`.
///
/// Logs an error message and terminates the process with a specific exit code.
extern "C" fn sigbus_sigsegv_handler(num: c_int, info: *mut siginfo_t, _unused: *mut c_void) {
    // Safe because we're just reading some fields from a supposedly valid argument.
    let si_signo = unsafe { (*info).si_signo };
    let si_code = unsafe { (*info).si_code };

    // Sanity check. The condition should never be true.
    if num != si_signo || (num != SIGBUS && num != SIGSEGV) {
        // Safe because we're terminating the process anyway.
        unsafe { _exit(i32::from(super::FC_EXIT_CODE_UNEXPECTED_ERROR)) };
    }

    // Other signals which might do async unsafe things incompatible with the rest of this
    // function are blocked due to the sa_mask used when registering the signal handler.
    match si_signo {
        SIGBUS => METRICS.signals.sigbus.inc(),
        SIGSEGV => METRICS.signals.sigsegv.inc(),
        _ => (),
    }

    error!(
        "Shutting down VM after intercepting signal {}, code {}.",
        si_signo, si_code
    );
    // Log the metrics before exiting.
    if let Err(e) = LOGGER.log_metrics() {
        error!("Failed to log metrics while stopping: {}", e);
    }

    // Safe because we're terminating the process anyway. We don't actually do anything when
    // running unit tests.
    #[cfg(not(test))]
    unsafe {
        _exit(i32::from(match si_signo {
            SIGBUS => super::FC_EXIT_CODE_SIGBUS,
            SIGSEGV => super::FC_EXIT_CODE_SIGSEGV,
            _ => super::FC_EXIT_CODE_UNEXPECTED_ERROR,
        }))
    };
}

/// Registers all the required signal handlers.
///
/// Custom handlers are installed for: `SIGBUS`, `SIGSEGV`, `SIGSYS`.
pub fn register_signal_handlers() -> utils::errno::Result<()> {
    // Call to unsafe register_signal_handler which is considered unsafe because it will
    // register a signal handler which will be called in the current thread and will interrupt
    // whatever work is done on the current thread, so we have to keep in mind that the registered
    // signal handler must only do async-signal-safe operations.
    register_signal_handler(SIGSYS, sigsys_handler)?;
    register_signal_handler(SIGBUS, sigbus_sigsegv_handler)?;
    register_signal_handler(SIGSEGV, sigbus_sigsegv_handler)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use libc::{cpu_set_t, syscall};
    use std::{mem, process, thread};

    use seccomp::{allow_syscall, SeccompAction, SeccompFilter};

    // This function is used when running unit tests, so all the unsafes are safe.
    fn cpu_count() -> usize {
        let mut cpuset: cpu_set_t = unsafe { mem::zeroed() };
        unsafe {
            libc::CPU_ZERO(&mut cpuset);
        }
        let ret = unsafe {
            libc::sched_getaffinity(
                0,
                mem::size_of::<cpu_set_t>(),
                &mut cpuset as *mut cpu_set_t,
            )
        };
        assert_eq!(ret, 0);

        let mut num = 0;
        for i in 0..libc::CPU_SETSIZE as usize {
            if unsafe { libc::CPU_ISSET(i, &cpuset) } {
                num += 1;
            }
        }
        num
    }

    #[test]
    fn test_signal_handler() {
        let child = thread::spawn(move || {
            assert!(register_signal_handlers().is_ok());

            let filter = SeccompFilter::new(
                vec![
                    allow_syscall(libc::SYS_brk),
                    allow_syscall(libc::SYS_exit),
                    allow_syscall(libc::SYS_futex),
                    allow_syscall(libc::SYS_getpid),
                    allow_syscall(libc::SYS_munmap),
                    allow_syscall(libc::SYS_kill),
                    allow_syscall(libc::SYS_rt_sigprocmask),
                    allow_syscall(libc::SYS_rt_sigreturn),
                    allow_syscall(libc::SYS_sched_getaffinity),
                    allow_syscall(libc::SYS_set_tid_address),
                    allow_syscall(libc::SYS_sigaltstack),
                    allow_syscall(libc::SYS_write),
                ]
                .into_iter()
                .collect(),
                SeccompAction::Trap,
            )
            .unwrap();

            assert!(filter.apply().is_ok());
            assert_eq!(METRICS.seccomp.num_faults.count(), 0);

            // Call the blacklisted `SYS_mkdirat`.
            unsafe { syscall(libc::SYS_mkdirat, "/foo/bar\0") };

            // Call SIGBUS signal handler.
            assert_eq!(METRICS.signals.sigbus.count(), 0);
            unsafe {
                syscall(libc::SYS_kill, process::id(), SIGBUS);
            }

            // Call SIGSEGV signal handler.
            assert_eq!(METRICS.signals.sigsegv.count(), 0);
            unsafe {
                syscall(libc::SYS_kill, process::id(), SIGSEGV);
            }
        });
        assert!(child.join().is_ok());

        // Sanity check.
        assert!(cpu_count() > 0);
        // Kcov somehow messes with our handler getting the SIGSYS signal when a bad syscall
        // is caught, so the following assertion no longer holds. Ideally, we'd have a surefire
        // way of either preventing this behaviour, or detecting for certain whether this test is
        // run by kcov or not. The best we could do so far is to look at the perceived number of
        // available CPUs. Kcov seems to make a single CPU available to the process running the
        // tests, so we use this as an heuristic to decide if we check the assertion.
        if cpu_count() > 1 {
            // The signal handler should let the program continue during unit tests.
            assert!(METRICS.seccomp.num_faults.count() >= 1);
        }
        assert!(METRICS.signals.sigbus.count() >= 1);
        assert!(METRICS.signals.sigsegv.count() >= 1);
    }
}
