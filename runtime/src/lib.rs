extern crate nix;
#[macro_use]
extern crate lazy_static;

mod zone;
mod twobit_slice;

use std::slice;
use std::mem::{self, MaybeUninit};
use std::ptr::{self, NonNull};
use std::ops::Deref;
use std::convert::TryFrom;
use std::sync::{Mutex, MutexGuard, LockResult};

use zone::ZoneAllocator;
use twobit_slice::TwobitSlice;

const HEAP_SIZE: usize = 1 << 20; // 1 MiB
const SEMISPACE_SIZE: usize = HEAP_SIZE / 2;

// ---

struct SpanMut {
    start: *mut u8,
    end: *mut u8
}

// ---

struct MemoryManager {
    zones: ZoneAllocator,
    fromspace: SpanMut,
    tospace: SpanMut,
    prev: *mut u8,
    greys: Vec<ORef>
}

impl MemoryManager {
    fn new() -> Self {
        let mut zones = ZoneAllocator::new(HEAP_SIZE);
        let fromspace = {
            let start = zones.allocate(SEMISPACE_SIZE)
                .expect("could not obtain initial heap")
                .as_ptr();
            let end = unsafe { start.offset(SEMISPACE_SIZE as isize) };
            SpanMut {start, end}
        };
        let tospace = {
            let start = zones.allocate(SEMISPACE_SIZE)
                .expect("could not obtain initial heap")
                .as_ptr();
            let end = unsafe { start.offset(SEMISPACE_SIZE as isize) };
            SpanMut {start, end}
        };
        let prev = tospace.end;
        Self { zones, fromspace, tospace, prev, greys: vec![] }
    }

    // FIXME: Zeroing:
    fn allocate(&mut self, layout: *const Layout) -> Option<NonNull<u8>> {
        let layout = unsafe { &*layout };
        let mut address: usize = self.prev as _;
        address = address.checked_sub(layout.size)?; // bump down
        let align = (layout.align as usize).max(mem::align_of::<NonNull<Layout>>());
        address = address & !(align - 1); // ensure alignment
        address = address.checked_sub(mem::size_of::<NonNull<Layout>>())?; // space for layout
        if address < self.tospace.start as usize {
            None // does not fit
        } else {
            self.prev = address as *mut u8;
            let obj: *mut MaybeUninit<Object> = address as _;
            unsafe {
                obj.write(MaybeUninit::new(Object {header: Header::layout(layout)}));
                Some(NonNull::new_unchecked(obj.offset(1) as _)) // back to start of fields
            }
        }
    }

    fn mark(&mut self, oref: ORef) -> ORef {
        unsafe {
            // Allocate and memcpy to tospace copy:
            let new_data = self.allocate(oref.layout()).unwrap();
            ptr::copy_nonoverlapping(oref.data(), new_data.as_ptr(), (*oref.layout()).size);
            let new_oref = ORef(new_data.cast());
            
            // Make `oref` grey:
            oref.header = Header::forwarding(new_oref);
            self.greys.push(oref);

            new_oref
        }
    }

    fn gc(&mut self, slots: &mut[usize], slot_map: TwobitSlice) {
        // Swap semispaces:
        mem::swap(&mut self.fromspace, &mut self.tospace);
        self.prev = self.tospace.end;

        // Mark roots:
        for (slot, kind) in slots.iter_mut().zip(slot_map.iter()) {
            match kind {
                0 => (),
                1 => {
                    let slot: &mut ORef = unsafe { mem::transmute(slot) };
                    *slot = slot.mark(self);
                },
                3 => unimplemented!(),
                _ => unreachable!()
            }
        }

        // Scan tospace:
        while let Some(mut oref) = self.greys.pop() {
            oref.scan(self);
        }
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
struct ORef(NonNull<Object>);

impl Clone for ORef {
    fn clone(&self) -> Self { *self }
}

impl Copy for ORef {}

impl Deref for ORef {
    type Target = Object;

    fn deref(&self) -> &Self::Target {
        unsafe { 
            let ptr: *const *const Layout = mem::transmute(self);
            mem::transmute(ptr.offset(-1)) // ORef points to start of actual fields
        }
    }
}

impl TryFrom<*mut Object> for ORef {
    type Error = ();

    fn try_from(ptr: *mut Object) -> Result<Self, Self::Error> {
        NonNull::new(ptr).map(ORef).ok_or(())
    }
}

impl TryFrom<VRef> for ORef {
    type Error = ();

    fn try_from(vref: VRef) -> Result<Self, Self::Error> {
        if vref.is_oref() {
            Self::try_from(vref.0 as *mut Object)
        } else {
            Err(())
        }
    }
}

impl ORef {
    fn data(self) -> *const u8 { self.0.as_ptr() as _ }

    fn mark(self, mem: &mut MemoryManager) -> Self { mem.mark(self) }

    fn scan(&mut self, mem: &mut MemoryManager) {
        unsafe { (*self.layout()).scan(mem::transmute(self.0), mem) }
    }
}

// ---

/// Tagged pointer (`ORef` or immediate scalar)
#[derive(Clone, Copy)]
pub struct VRef(usize);

impl VRef {
    const COUNT: usize = mem::size_of::<usize>();
    const MASK: usize = Self::COUNT - 1;

    fn is_oref(self) -> bool { self.0 & Self::MASK != 0 }

    fn mark(self, mem: &mut MemoryManager) -> Self {
        if let Ok(oref) = ORef::try_from(self) {
            VRef(oref.mark(mem).0.as_ptr() as usize)
        } else {
            self
        }
    }
}

// ---

/// Object header:
#[derive(Clone, Copy)]
struct Header(usize);

impl Header {
    const MASK: usize = mem::size_of::<usize>() - 1;
    const FWD_TAG: usize = 1;

    fn layout(layout: *const Layout) -> Self { Self(layout as usize) }

    fn forwarding(new_oref: ORef) -> Self {
        Self(new_oref.data() as usize & Self::FWD_TAG)
    }

    fn is_forwarding(self) -> bool { self.0 & Self::MASK == 0 }

    unsafe fn as_layout(self) -> *const Layout { self.0 as _ }
}

// ---

/// Heap object
#[repr(C)]
struct Object {
    header: Header
}

impl Object {
    unsafe fn layout(&self) -> *const Layout { self.header.as_layout() }

    fn field_layout(&self, index: usize) -> NonNull<Layout> {
        unsafe { (&(*self.layout()).fields()[index]).layout }
    }

    fn field_data<'a>(&'a self, index: usize) -> &'a [u8] {
        unsafe {
            let ptr: *const u8 = mem::transmute(self);
            let field_lo = &(*self.layout()).fields()[index];
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
                    *mem::transmute::<&mut *mut Object, &mut ORef>(field_ref) = ORef(field).mark(mem);
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
pub unsafe extern fn Broom_allocate(layout: NonNull<Layout>, frame_len: usize, slots: *mut usize, slot_map: *const u8)
    -> NonNull<u8>
{
    let mut manager = MANAGER.lock().unwrap();
    match manager.allocate(layout.as_ref()) {
        Some(res) => res,
        None => {
            let slots = slice::from_raw_parts_mut(slots, frame_len);
            let slot_map = TwobitSlice::from_raw_parts(slot_map, frame_len);
            manager.gc(slots, slot_map);
            manager.allocate(layout.as_ref()).unwrap()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::{size_of, align_of};
    use std::ptr;

    #[test]
    fn test_allocate() {
        let layout = Layout {
            size: 8,
            align: 8,
            inlineable: true,
            is_array: false,
            field_count: 0
        };
        match Broom_allocate(From::from(&layout), 0, ptr::null_mut(), ptr::null_mut()) {
            Some(ptr) => {
                let mut ptr: *const Object = ptr.as_ptr() as _;
                unsafe {
                    ptr = ptr.offset(-1);
                    assert_eq!((*ptr).layout, From::from(&layout));
                }
            }
            None => assert!(false)
        }
    }
}

