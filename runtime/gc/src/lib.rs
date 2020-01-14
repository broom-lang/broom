extern crate nix;

use std::mem;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;
use std::slice;

mod util;
mod zone;
mod object;

use util::{IntrSlice, IntrSliceMut};

/// Heap object (really, just the common header part).
#[repr(C)]
pub struct Obj {
    /// Memory managers can use this however they please,
    /// e.g. for mark stacks or broken hearts.
    link: Option<ORef>,
    /// Layout information for the object, statically allocated (or in immortal object space).
    layout: &'static Layout
}

impl Obj {
    /// Pointer to the start of object fields (= right after header).
    fn contents(&self) -> *const () { unsafe { (self as *const Obj).offset(1) as *const () } }
}

/// Object reference.
#[derive(Clone, Copy)]
pub struct ORef(NonNull<Obj>);

impl Deref for ORef {
    type Target = Obj;

    fn deref(&self) -> &Obj { unsafe { self.0.as_ref() } }
}

impl DerefMut for ORef {
    fn deref_mut(&mut self) -> &mut Obj { unsafe { self.0.as_mut() } }
}

impl ORef {
    /// Mark `self` and return the new location of the object.
    /// Idempotent (marking an object that is already grey or black has no effect).
    #[must_use]
    fn mark(self, mem: &mut MemoryManager) -> Self {
        unimplemented!();
        self
    }

    /// Mark the referees of `self`.
    fn scan(self, mem: &mut MemoryManager) {
        for oref in self.layout.refs(&*self) {
            let _ = oref.mark(mem); // Just mark and sweep ATM, so objects never move.
        }
    }
}

/// Runtime layout information for the GC to use.
#[repr(C)]
struct Layout {
    len: usize
}

impl Layout {
    /// Iterator over the referees of `self`.
    fn refs<'a>(&self, obj: &'a Obj) -> impl Iterator<Item=&'a mut ORef> {
        self.ref_slices(obj)
            .flat_map(Into::<&mut [ORef]>::into)
    }

    /// Iterator over the `RefSlice`s of `self` in the `Obj` of `oref`.
    fn ref_slices<'a>(&self, obj: &'a Obj) -> impl Iterator<Item=RefSlice<'a>> {
        RefSlices {
            ranges: unsafe { IntrSlice::from_ref(&*self.ranges()) }.as_slice().iter().cloned(),
            fields: unsafe { mem::transmute::<_, &'a ()>(obj.contents()) }
        }
    }

    /// Pointer to start of ref range table.
    fn ranges(&self) -> *const usize {
        unsafe { (self as *const Layout).offset(1) as *const usize }
    }
}

/// A mutable slice or `IntrSlice` of `ORef`s.
enum RefSlice<'a> {
    Static(&'a mut [ORef]),
    Dynamic(IntrSliceMut<'a, ORef>)
}

impl<'a> Into<&'a mut [ORef]> for RefSlice<'a> {
    fn into(self) -> &'a mut [ORef] {
        match self {
            RefSlice::Static(slice) => slice,
            RefSlice::Dynamic(islice) => islice.as_slice()
        }
    }
}

/// Iterator over the `RefSlice`s of an object.
struct RefSlices<'a, I: Iterator<Item=usize>> {
    ranges: I,
    fields: &'a () 
}

impl<'a, I: Iterator<Item=usize>> Iterator for RefSlices<'a, I> {
    type Item = RefSlice<'a>;

    fn next(&mut self) -> Option<RefSlice<'a>> {
        self.ranges.next()
                   .map(|x| unsafe {
                       let offset = x >> 3;
                       let fields: *const ORef = self.fields as *const () as _;
                       let ptr: *mut ORef = fields.offset(offset as _) as _;
                       match x & 0b111 {
                           1 => {
                               let len = self.ranges.next().unwrap();
                               RefSlice::Static(slice::from_raw_parts_mut(ptr, len))
                           },
                           2 => RefSlice::Dynamic(IntrSliceMut::from_ref(&mut *ptr)),
                           _ => unreachable!()
                       }
                   })
    }
}

/// Use `Obj`:s as a singly-linked stack.
struct GreyStack(Option<ORef>);

impl GreyStack {
    /// The empty stack.
    fn empty() -> Self { GreyStack(None) }

    /// Push an object reference to the stack.
    fn push(&mut self, mut oref: ORef) {
        (&mut*oref).link = self.0;
        self.0 = Some(oref);
    }

    /// Pop an object reference from the stack.
    fn pop(&mut self) -> Option<ORef> {
         let res = self.0;
         if let Some(oref) = self.0 {
             self.0 = oref.link;
         }
         res
    }
}

/// Memory manager (allocator and GC).
pub struct MemoryManager {
    /// How many bytes can be allocated for `self`.
    max_heap: usize,
    /// Mark stack.
    greys: GreyStack
}

impl MemoryManager {
    /// Create a new `MemoryManager` that can use up to `max_heap` bytes of memory.
    pub fn new(max_heap: usize) -> Self {
        MemoryManager { max_heap, greys: GreyStack::empty() }
    }

    /// Allocate `size` bytes aligned to `align` bytes.
    pub unsafe fn allocate(&mut self, align: usize, size: usize) -> Option<ORef> {
        unimplemented!();
        None
    }

    /// Collect garbage.
    ///
    /// # Safety
    ///
    /// Roots must be marked first.
    pub unsafe fn collect(&mut self) {
        self.mark_all();
        self.sweep();
    }

    /// Mark all object references (until mark stack is empty).
    fn mark_all(&mut self) {
        while let Some(oref) = self.greys.pop() {
            oref.scan(self);
        }
    }

    /// Free the memory of unmarked objects.
    fn sweep(&mut self) {
        unimplemented!();
    }
}

