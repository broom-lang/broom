use std::slice;

/// Like `std::slice`, but the len is stored right before the elements themselves.
#[derive(Clone, Copy)]
pub struct IntrSlice<'a, T>(&'a T);

impl<'a, T> IntrSlice<'a, T> {
    pub unsafe fn from_ref(rf: &'a T) -> Self { IntrSlice::<'a>(rf) }

    /// Convert to a regular slice by reading in the size.
    pub fn as_slice(self) -> &'a [T] {
        let ptr: *const T = self.0 as _;
        unsafe {
	    let len = *(ptr as *const usize).offset(-1);
	    slice::from_raw_parts(ptr, len)
        }
    }
}

/// Mutable version of `IntrSlice`.
pub struct IntrSliceMut<'a, T>(&'a mut T);

impl<'a, T> IntrSliceMut<'a, T> {
    pub unsafe fn from_ref(rf: &'a mut T) -> Self { IntrSliceMut::<'a>(rf) }
    
    /// Convert to a regular slice by reading in the size.
    pub fn as_slice(self) -> &'a mut [T] {
        let ptr: *mut T = self.0 as _;
        unsafe {
            let len = *(ptr as *const usize).offset(-1);
            slice::from_raw_parts_mut(ptr, len)
        }
    }
}

