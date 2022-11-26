extern crate nix;
#[macro_use]
extern crate lazy_static;

mod zone;
mod twobit_slice;

use std::slice;
use std::mem::{self, MaybeUninit};
use std::ptr::{self, NonNull};
use std::ops::{Deref, DerefMut};
use std::convert::TryFrom;
use std::sync::{Mutex, MutexGuard, LockResult};

use zone::ZoneAllocator;
use twobit_slice::TwobitSlice;

extern {
    static Broom_layout_ORef: Layout;
}

const HEAP_SIZE: usize = 1 << 20; // 1 MiB
const SEMISPACE_SIZE: usize = HEAP_SIZE / 2;

const GC_ALOT: bool = false;

// ---

#[derive(Debug)]
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

    fn allocate(&mut self, layout: *const Layout) -> Option<NonNull<u8>> {
        let layout = unsafe { &*layout };
        let mut address: usize = self.prev as _;
        address = address.checked_sub(layout.size)?; // bump down
        let align = (layout.align as usize).max(mem::align_of::<NonNull<Layout>>());
        address = address & !(align - 1); // ensure alignment
        address = address.checked_sub(mem::size_of::<Header>())?; // space for header
        if address < self.tospace.start as usize {
            None // does not fit
        } else {
            self.prev = address as *mut u8;
            let obj: *mut MaybeUninit<Object> = address as _;
            unsafe {
                obj.write(MaybeUninit::new(Object {header: Header::layout(layout)}));
                let data: *mut u8 = obj.offset(1) as _;
                ptr::write_bytes(data, 0, layout.size);
                Some(NonNull::new_unchecked(data))
            }
        }
    }

    fn mark(&mut self, mut oref: ORef) -> ORef {
        match oref.forwarded() {
            Some(oref) => oref,
            None => {
                // Allocate and memcpy to tospace copy:
                let new_data = unsafe { self.allocate(oref.layout()).unwrap() };
                unsafe {
                    ptr::copy_nonoverlapping(oref.data(), new_data.as_ptr(), (*oref.layout()).size);
                }
                let new_oref = ORef(new_data.cast());
                
                // Make `oref` grey:
                oref.header = Header::forwarding(new_oref);
                self.greys.push(new_oref);

                new_oref
            }
        }
    }

    fn gc(&mut self, slots: &mut[usize], slot_map: TwobitSlice) {
        // Swap semispaces:
        mem::swap(&mut self.fromspace, &mut self.tospace);
        self.prev = self.tospace.end;

        // Evacuate roots:
        for (slot, kind) in slots.iter_mut().zip(slot_map.iter()) {
            match kind {
                0 => (),
                1 => {
                    let slot = unsafe { mem::transmute::<&mut usize, &mut ORef>(slot) };
                    *slot = self.mark(*slot);
                },
                3 => unimplemented!(),
                _ => unreachable!()
            }
        }

        // Evacuate the rest:
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
        let ptr: *const Object = self.0.as_ptr();
        unsafe { 
            mem::transmute(ptr.offset(-1)) // ORef points to start of actual fields
        }
    }
}

impl DerefMut for ORef {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let ptr: *mut Object = self.0.as_ptr();
        unsafe { 
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

// ---

/// Tagged pointer (`ORef` or immediate scalar)
#[derive(Clone, Copy)]
pub struct VRef(usize);

impl VRef {
    const COUNT: usize = mem::size_of::<usize>();
    const MASK: usize = Self::COUNT - 1;

    fn is_oref(self) -> bool { self.0 & Self::MASK == 0 }

    fn mark(self, mem: &mut MemoryManager) -> Self {
        if let Ok(oref) = ORef::try_from(self) {
            VRef(mem.mark(oref).0.as_ptr() as usize)
        } else {
            self
        }
    }
}

// ---

/// Object header:
#[derive(Debug, Clone, Copy)]
struct Header(usize);

impl Header {
    const MASK: usize = mem::size_of::<usize>() - 1;
    const FWD_TAG: usize = 1;

    fn layout(layout: *const Layout) -> Self { Self(layout as usize) }

    fn forwarding(new_oref: ORef) -> Self {
        Self(new_oref.data() as usize | Self::FWD_TAG)
    }

    fn is_forwarding(self) -> bool { self.0 & Self::MASK == Self::FWD_TAG }

    fn forwarded(self) -> Option<ORef> {
        if self.is_forwarding() {
            Some(ORef(unsafe { mem::transmute(self.0 & !Self::MASK) }))
        } else {
            None
        }
    }

    unsafe fn as_layout(self) -> *const Layout { self.0 as _ }
}

// ---

/// Heap object
#[derive(Debug)]
#[repr(C)]
struct Object {
    header: Header
}

impl Object {
    fn data(&self) -> *const u8 { (unsafe { (self as *const Object).offset(1) }) as _ }

    fn forwarded(&self) -> Option<ORef> { self.header.forwarded() }

    fn scan(&mut self, mem: &mut MemoryManager) {
        unsafe { &*self.layout() }.scan(self, mem)
    }

    unsafe fn layout(&self) -> *const Layout { self.header.as_layout() }
}

// ---

/// Object layout / runtime type
#[derive(Debug)]
#[repr(C)]
struct FieldLayout {
    offset: usize,
    layout: NonNull<Layout>
}

impl FieldLayout {
    fn is_oref(&self) -> bool {
        ptr::eq(self.layout.as_ptr(), unsafe { &Broom_layout_ORef })
    }

    fn scan(&self, obj: &mut Object, mem: &mut MemoryManager) {
        if self.is_oref() {
            let obj = obj.data();
            let field: &mut Option<ORef> = unsafe { mem::transmute(obj.offset(self.offset as isize)) };
            if let Some(field) = field {
                *field = mem.mark(*field);
            }
        }
        // FIXME: Scan inside inlined fields
    }
}

#[derive(Debug)]
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
        let ptr: *const Self = self as _;
        unsafe {
            let ptr: *const FieldLayout = ptr.offset(1) as _;
            slice::from_raw_parts(ptr, self.field_count)
        }
    }

    fn scan(&self, obj: &mut Object, mem: &mut MemoryManager) {
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

    if GC_ALOT {
        let slots = slice::from_raw_parts_mut(slots, frame_len);
        let slot_map = TwobitSlice::from_raw_parts(slot_map, frame_len);
        manager.gc(slots, slot_map);
        manager.allocate(layout.as_ref()).unwrap()
    } else {
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
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let ptr = unsafe { Broom_allocate(From::from(&layout), 0, ptr::null_mut(), ptr::null_mut()) };
        let mut ptr: *const Object = ptr.as_ptr() as _;
        unsafe {
            ptr = ptr.offset(-1);
            assert_eq!((*ptr).layout(), &layout as *const Layout);
        }
    }
}

