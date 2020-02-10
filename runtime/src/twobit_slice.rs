use std::marker::PhantomData;

#[derive(Clone, Copy)]
pub struct TwobitSlice<'a> {
    len: usize,
    data: *const u8,
    _lifetime: PhantomData<&'a ()>
}

impl<'a> TwobitSlice<'a> {
    const QUAD_LEN: usize = 4;
    const MAX_QUAD_INDEX: usize = Self::QUAD_LEN - 1;
    const QUAD_MASK: u8 = 0b11;

    pub unsafe fn from_raw_parts(data: *const u8, len: usize) -> Self {
        Self {data, len, _lifetime: Default::default()}
    }

    pub fn get(&self, i: usize) -> Option<u8> {
        if i < self.len {
            let quad = unsafe { *self.data.offset((i / Self::QUAD_LEN) as isize) };
            Some(quad >> (Self::MAX_QUAD_INDEX - i % Self::QUAD_LEN) * 2 & Self::QUAD_MASK)
        } else {
            None
        }
    }

    pub fn iter(self) -> TwobitSliceIter<'a> {
        TwobitSliceIter {slice: self, index: 0}
    }
}

pub struct TwobitSliceIter<'a> {
    slice: TwobitSlice<'a>,
    index: usize
}

impl<'a> Iterator for TwobitSliceIter<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        let res = self.slice.get(self.index);
        if res.is_some() {
            self.index += 1;
        }
        res
    }
}

