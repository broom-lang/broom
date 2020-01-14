use std::slice;
use std::mem;
use std::ptr::NonNull;
use std::ops::Deref;
use std::convert::TryFrom;

// ---
struct MemoryManager; // HACK
impl MemoryManager {
    fn mark<T>(&mut self, oref: ORef<T>) -> ORef<T> {
        unimplemented!()
    }
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
        self.layout.scan(unsafe { mem::transmute(self.0) }, mem)
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
    layout: ORef<Layout>
}

impl Object {
    fn field_layout(&self, index: usize) -> ORef<Layout> {
        (&self.layout.fields()[index]).layout
    }

    fn field_data<'a>(&'a self, index: usize) -> &'a [u8] {
        unsafe {
            let ptr: *const u8 = mem::transmute(self);
            let field_lo = &self.layout.fields()[index];
            slice::from_raw_parts(ptr.offset(field_lo.offset as isize), field_lo.size)
        }
    }
}

// ---

// TODO: Sneak bit in for `is_oref`
/// Object layout / runtime type
#[repr(C)]
struct FieldLayout {
    offset: usize, // this always gets cast to isize, so an extra (mutator-slowing?) bit here
    size: usize,
    layout: ORef<Layout> // tag this pointer with oref bit? Or use VRef tag number here for small scalars?
}

impl FieldLayout {
    fn is_oref(&self) -> bool { unimplemented!() }

    fn scan(&self, obj: *mut u8, mem: &mut MemoryManager) {
        if self.is_oref() {
            unsafe {
                let field_ref: &mut *mut Object = mem::transmute(obj.offset(self.offset as isize));
                if let Some(field) = NonNull::new(*field_ref) {
                    *mem::transmute::<&mut *mut Object, &mut ORef<Object>>(field_ref) = ORef(field).mark(mem);
                }
            }
        }
    }
}

#[repr(C)]
struct Layout {
    base: Object, // Layouts are also Objects. Or maybe we just put them in "perm gen" instead?
    size: usize,
    align: u16,
    is_array: bool, // We have at least 15 more bits for expansion here
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

