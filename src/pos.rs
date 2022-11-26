use std::rc::Rc;

pub type Filename = Rc<String>;

#[derive(Debug, Clone)]
pub struct Pos {
    pub filename: Option<Filename>,
    pub byte: usize,
    pub line: usize,
    pub col: usize
}

impl Default for Pos {
    fn default() -> Self { Pos {filename: None, byte: 0, line: 1, col: 1} }
}

impl Pos {
    pub fn start(filename: Option<Filename>) -> Self { Pos {filename, byte: 0, line: 1, col: 1} }

    pub fn advance(&mut self, c: char) {
        let c_len = c.len_utf8();
        self.byte += c_len;

        if c == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
    }
}

#[derive(Debug)]
pub struct Positioned<T> {
    pub v: T,
    pub pos: Pos
}

#[derive(Debug)]
pub struct Span {
    pub start: Pos,
    pub end: Pos
}
