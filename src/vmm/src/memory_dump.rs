// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Defines functionality for creating guest memory snapshots.

use std::fmt::{Display, Formatter};
use std::io::SeekFrom;

use versionize::{VersionMap, Versionize, VersionizeResult};
use versionize_derive::Versionize;
use vm_memory::{
    Bytes, GuestMemory, GuestMemoryError, GuestMemoryMmap, GuestMemoryRegion, MemoryRegionAddress,
};

use crate::DirtyBitmap;

/// State of a guest memory region saved to file/buffer.
#[derive(Debug, PartialEq, Versionize)]
pub struct GuestMemoryRegionState {
    /// Base address.
    pub base_address: u64,
    /// Region size.
    pub size: usize,
    /// Offset in file/buffer where the region is saved.
    pub offset: u64,
}

/// Guest memory state.
#[derive(Debug, PartialEq, Versionize)]
pub struct GuestMemoryState {
    /// List of regions.
    pub regions: Vec<GuestMemoryRegionState>,
}

/// Defines the interface for dumping memory a file.
pub trait DumpMemory {
    fn dump<T: std::io::Write>(
        &self,
        writer: &mut T,
    ) -> std::result::Result<GuestMemoryState, Error>;
    fn dump_dirty<T: std::io::Write + std::io::Seek>(
        &self,
        writer: &mut T,
        dirty_bitmap: &DirtyBitmap,
    ) -> std::result::Result<GuestMemoryState, Error>;
}

/// Errors associated with dumping guest memory to file.
#[derive(Debug)]
pub enum Error {
    WriteMemory(GuestMemoryError),
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use self::Error::*;
        match self {
            WriteMemory(err) => write!(f, "Unable to dump memory: {:?}", err),
        }
    }
}

impl DumpMemory for GuestMemoryMmap {
    fn dump<T: std::io::Write>(
        &self,
        writer: &mut T,
    ) -> std::result::Result<GuestMemoryState, Error> {
        let mut guest_memory_state = GuestMemoryState {
            regions: Vec::new(),
        };
        let mut offset = 0;
        self.with_regions_mut(|_, region| {
            region
                .write_to(MemoryRegionAddress(0), writer, region.len() as usize)
                .map(|_| ())?;

            guest_memory_state.regions.push(GuestMemoryRegionState {
                base_address: region.start_addr().0,
                size: region.len() as usize,
                offset,
            });

            offset += region.len();
            Ok(())
        })
        .map_err(Error::WriteMemory)?;

        Ok(guest_memory_state)
    }

    fn dump_dirty<T: std::io::Write + std::io::Seek>(
        &self,
        writer: &mut T,
        dirty_bitmap: &DirtyBitmap,
    ) -> std::result::Result<GuestMemoryState, Error> {
        let page_size = sysconf::page::pagesize();
        let mut guest_memory_state = GuestMemoryState {
            regions: Vec::new(),
        };
        let mut writer_offset = 0;

        self.with_regions_mut(|slot, region| {
            let bitmap = dirty_bitmap.get(&slot).unwrap();
            let mut write_size = 0;
            let mut dirty_batch_start: u64 = 0;

            for (i, v) in bitmap.iter().enumerate() {
                for j in 0..64 {
                    let is_dirty_page = ((v >> j) & 1u64) != 0u64;
                    if is_dirty_page {
                        let page_offset = ((i * 64) + j) * page_size;
                        // We are at the start of a new batch of dirty pages.
                        if write_size == 0 {
                            // Seek forward over the unmodified pages.
                            writer
                                .seek(SeekFrom::Start(writer_offset + page_offset as u64))
                                .unwrap();
                            dirty_batch_start = page_offset as u64;
                        }
                        write_size += page_size;
                    } else if write_size > 0 {
                        // We are at the end of a batch of dirty pages.
                        region
                            .write_to(MemoryRegionAddress(dirty_batch_start), writer, write_size)
                            .map(|_| ())?;
                        write_size = 0;
                    }
                }
            }

            if write_size > 0 {
                region
                    .write_to(MemoryRegionAddress(dirty_batch_start), writer, write_size)
                    .map(|_| ())?;
            }

            guest_memory_state.regions.push(GuestMemoryRegionState {
                base_address: region.start_addr().0,
                size: region.len() as usize,
                offset: writer_offset,
            });

            writer_offset += region.len();
            Ok(())
        })
        .map_err(Error::WriteMemory)?;

        Ok(guest_memory_state)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use utils::tempfile::TempFile;
    use vm_memory::GuestAddress;

    #[test]
    fn test_full_dump_state() {
        let page_size: usize = sysconf::page::pagesize();
        // Two regions of one page each, with a one page gap between them.
        let mem_regions = [
            (GuestAddress(0), page_size),
            (GuestAddress(page_size as u64 * 2), page_size),
        ];
        let guest_memory = GuestMemoryMmap::from_ranges(&mem_regions[..]).unwrap();

        let expected_memory_state = GuestMemoryState {
            regions: vec![
                GuestMemoryRegionState {
                    base_address: 0,
                    size: page_size,
                    offset: 0,
                },
                GuestMemoryRegionState {
                    base_address: page_size as u64 * 2,
                    size: page_size,
                    offset: page_size as u64,
                },
            ],
        };

        let mut buffer = vec![0u8; page_size * 2];
        let actual_memory_state = guest_memory.dump(&mut buffer.as_mut_slice()).unwrap();
        assert_eq!(expected_memory_state, actual_memory_state);
    }

    #[test]
    fn test_dirty_dump_state() {
        let page_size: usize = sysconf::page::pagesize();
        // Two regions of three pages each, with a one page gap between them.
        let mem_regions = [
            (GuestAddress(0), page_size * 3),
            (GuestAddress(page_size as u64 * 4), page_size * 3),
        ];
        let guest_memory = GuestMemoryMmap::from_ranges(&mem_regions[..]).unwrap();

        // First region pages: [clean, dirty, clean]
        // Second region pages: [clean, dirty, dirty]
        let mut dirty_bitmap: DirtyBitmap = HashMap::new();
        dirty_bitmap.insert(0, vec![0b10; 1]);
        dirty_bitmap.insert(1, vec![0b110; 1]);

        let expected_memory_state = GuestMemoryState {
            regions: vec![
                GuestMemoryRegionState {
                    base_address: 0,
                    size: page_size * 3,
                    offset: 0,
                },
                GuestMemoryRegionState {
                    base_address: page_size as u64 * 4,
                    size: page_size * 3,
                    offset: page_size as u64 * 3,
                },
            ],
        };

        let file = TempFile::new().unwrap();
        let actual_memory_state = guest_memory
            .dump_dirty(&mut file.as_file(), &dirty_bitmap)
            .unwrap();
        assert_eq!(expected_memory_state, actual_memory_state);
    }
}
