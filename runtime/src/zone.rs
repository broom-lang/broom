use std::mem;
use std::ptr::{self, NonNull};
#[cfg(unix)]
use nix::libc::c_void;
#[cfg(unix)]
use nix::sys::mman::{mmap, munmap, ProtFlags, MapFlags};

/// A big slab of memory that we split into `Page`s and `Block`s.
struct Zone;

impl Zone {
    /// A number such that `Self::SIZE = 2^SHIFT`.
    const SHIFT: usize = 20;

    /// The size of a `Zone` in bytes.
    const SIZE: usize = 1 << Self::SHIFT;

    /// `ptr & MASK` gives the index of the pointed byte in the containing `Zone`.
    /// `ptr & !MASK` gives the pointer to the start of the containing `Zone`.
    const MASK: usize = Self::SIZE - 1;
}

/// Allocates `Zone`s.
pub struct ZoneAllocator {
    max_heap: usize,
    allocated: usize
}

impl ZoneAllocator {
    /// Make a `ZoneAllocator` that allocates zones up to a total of `max_heap` bytes.
    pub fn new (max_heap: usize) -> Self { ZoneAllocator { max_heap, allocated: 0 } }

    /// Allocate a contiguous array of `Zone`s big enough to fit `nbytes` of memory.
    pub fn allocate(&mut self, nbytes: usize) -> Option<NonNull<u8>> {
        // FIXME: Round nbytes up to nearest multiple of `Zone::SIZE`.
        if self.allocated + nbytes <= self.max_heap {
            unsafe {
                let ptr = os_allocate(nbytes);
                self.allocated += nbytes;
	        Some(NonNull::new_unchecked(ptr))
            }
        } else {
            None
        }
    }

    /// Deallocate a contiguous array of `Zone`s that is `nbytes` long.
    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, nbytes: usize) {
        os_deallocate(ptr.as_ptr(), nbytes);
	self.allocated -= nbytes;
    }
}  

#[cfg(unix)]
unsafe fn os_allocate(size: usize) -> *mut u8 {
    let inflated_size = size + Zone::SIZE;

    let addr = mmap(ptr::null::<()>() as *mut c_void, inflated_size,
                    ProtFlags::PROT_READ | ProtFlags::PROT_WRITE,
                    MapFlags::MAP_ANON | MapFlags::MAP_PRIVATE,
                    -1, 0)
                   .expect("out of memory");

    let offset = addr as usize & Zone::MASK;
    munmap(addr, Zone::SIZE - offset)
        .and_then(|()| if offset > 0 {
            munmap(addr.offset(inflated_size as isize).offset(-(offset as isize)), offset)
        } else {
            Ok(())
        })
        .expect("munmap() failed");

    addr.offset(Zone::SIZE as isize).offset(-(offset as isize)) as *mut u8
}

#[cfg(unix)]
unsafe fn os_deallocate(ptr: *mut u8, nbytes: usize) {
    munmap(mem::transmute(ptr), nbytes).expect("munmap() failed");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_allocate() {
        let mut zones = ZoneAllocator::new(1 << 20);
        assert!(zones.allocate(1 << 20).is_some());
    }
}

