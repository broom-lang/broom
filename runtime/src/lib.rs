extern crate nix;
#[macro_use]
extern crate lazy_static;

mod zone;

use std::slice;
use std::mem;
use std::ptr::NonNull;
use std::ops::Deref;
use std::convert::TryFrom;
use std::sync::{Mutex, MutexGuard, LockResult};

use zone::ZoneAllocator;

const HEAP_SIZE: usize = 1 << 20; // 1 MiB

// ---

struct MemoryManager {
    zones: ZoneAllocator,
    start: *mut u8,
    end: *mut u8,
    prev: *mut u8 
}

impl MemoryManager {
    fn new() -> Self {
        let mut zones = ZoneAllocator::new(HEAP_SIZE);
        let start = zones.allocate(HEAP_SIZE)
            .expect("could not obtain initial heap")
            .as_ptr();
        let end = unsafe { start.offset(HEAP_SIZE as isize) };
        Self { zones, start, end, prev: end }
    }

    // FIXME: Zeroing:
    fn allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        let mut address: usize = self.prev as _;
        address = address.checked_sub(layout.size)?; // bump down
        address = address & !(layout.align as usize - 1); // ensure alignment
        address = address.checked_sub(mem::size_of::<*const Layout>())?; // space for layout
        if address < self.start as usize {
            None // does not fit
        } else {
            self.prev = address as _;
            unsafe { (self.prev as *mut *const Layout).write(layout); }
            let obj = unsafe {
                self.prev.add(mem::size_of::<*const Layout>()) // back to start of fields
            };
            Some(unsafe { NonNull::new_unchecked(obj) })
        }
    }

    fn mark<T>(&mut self, oref: ORef<T>) -> ORef<T> {
        unimplemented!()
    }
}

/// Newtype to implement `Sync` on.
struct MutexMemoryManager(Mutex<MemoryManager>);

unsafe impl Sync for MutexMemoryManager {}

impl MutexMemoryManager {
    fn new() -> Self { MutexMemoryManager(Mutex::new(MemoryManager::new())) }

    fn lock(&self) -> LockResult<MutexGuard<MemoryManager>> { self.0.lock() }
}

// ---

/// Object reference
struct ORef<T>(NonNull<T>);

impl<T> Clone for ORef<T> {
    fn clone(&self) -> Self { *self }
}

impl<T> Copy for ORef<T> {}

impl<T> Deref for ORef<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { 
            let ptr: *const ORef<Layout> = mem::transmute(self);
            mem::transmute(ptr.offset(-1)) // ORef points to start of actual fields
        }
    }
}

impl<T> TryFrom<*mut T> for ORef<T> {
    type Error = ();

    fn try_from(ptr: *mut T) -> Result<Self, Self::Error> {
        NonNull::new(ptr).map(ORef).ok_or(())
    }
}

impl<T> TryFrom<VRef> for ORef<T> {
    type Error = ();

    fn try_from(vref: VRef) -> Result<Self, Self::Error> {
        if vref.is_oref() {
            Self::try_from(vref.0 as *mut T)
        } else {
            Err(())
        }
    }
}

impl ORef<Object> {
    fn mark(self, mem: &mut MemoryManager) -> Self { mem.mark(self) }

    fn scan(&mut self, mem: &mut MemoryManager) {
        unsafe { self.layout.as_ref().scan(mem::transmute(self.0), mem) }
    }
}

// ---

/// Tagged pointer (`ORef` or immediate scalar)
#[derive(Clone, Copy)]
struct VRef(usize);

impl VRef {
    const COUNT: usize = mem::size_of::<usize>();
    const MASK: usize = Self::COUNT - 1;

    fn is_oref(self) -> bool { self.0 & Self::MASK != 0 }

    fn mark(self, mem: &mut MemoryManager) -> Self {
        if let Ok(oref) = ORef::<Object>::try_from(self) {
            VRef(oref.mark(mem).0.as_ptr() as usize)
        } else {
            self
        }
    }
}

// ---

/// Heap object
#[repr(C)]
struct Object {
    layout: NonNull<Layout>
}

impl Object {
    fn field_layout(&self, index: usize) -> NonNull<Layout> {
        unsafe { (&self.layout.as_ref().fields()[index]).layout }
    }

    fn field_data<'a>(&'a self, index: usize) -> &'a [u8] {
        unsafe {
            let ptr: *const u8 = mem::transmute(self);
            let field_lo = &self.layout.as_ref().fields()[index];
            slice::from_raw_parts(ptr.offset(field_lo.offset as isize), field_lo.layout.as_ref().size)
        }
    }
}

// ---

/// Object layout / runtime type
#[repr(C)]
struct FieldLayout {
    offset: usize,
    layout: NonNull<Layout>
}

impl FieldLayout {
    fn is_oref(&self) -> bool { !unsafe { self.layout.as_ref() }.inlineable }

    fn scan(&self, obj: *mut u8, mem: &mut MemoryManager) {
        if self.is_oref() {
            unsafe {
                let field_ref: &mut *mut Object = mem::transmute(obj.offset(self.offset as isize));
                if let Some(field) = NonNull::new(*field_ref) {
                    *mem::transmute::<&mut *mut Object, &mut ORef<Object>>(field_ref) = ORef(field).mark(mem);
                }
            }
        }
        // FIXME: Scan inside inlined fields
    }
}

#[repr(C)]
pub struct Layout {
    size: usize, // TODO: separate .stride
    align: u16,
    inlineable: bool,
    is_array: bool,
    field_count: usize
}

impl Layout {
    fn fields<'a>(&'a self) -> &'a [FieldLayout] {
        unsafe {
            let ptr: *const Self = mem::transmute(self);
            let ptr = mem::transmute(ptr.offset(1));
            slice::from_raw_parts(ptr, self.field_count)
        }
    }

    fn scan(&self, obj: *mut u8, mem: &mut MemoryManager) {
        for field_lo in self.fields() {
            field_lo.scan(obj, mem);
        }
    }
}

// ---

// HACK: Global variable, makes `Broom_allocate` easier to call initially:
lazy_static! {
    static ref MANAGER: MutexMemoryManager = MutexMemoryManager::new();
}

#[no_mangle]
pub extern fn Broom_allocate(layout: *const Layout) -> Option<NonNull<u8>> {
    MANAGER.lock().unwrap().allocate(unsafe { mem::transmute(layout) })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::{size_of, align_of};

    #[test]
    fn test_allocate() {
        assert!(Broom_allocate(size_of::<usize>(), align_of::<usize>()).is_some());
    }
}

