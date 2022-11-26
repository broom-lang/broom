use crate::pos::{Pos, Positioned, Filename, Span, Spanning};

#[derive(Debug)]
pub enum Tok {
    LParen,
    RParen
}

impl Tok {
    fn spanning(self, start: Pos, end: Pos) -> Spanning<Self> { Spanning {v: self, span: Span {start, end}}}
}

#[derive(Debug)]
pub enum Error {
    UnexpectedChar(char)
}

impl Error {
    fn at(self, pos: Pos) -> Positioned<Self> { Positioned {v: self, pos} }
}

pub struct Lexer<'a> {
    chars: &'a str,
    pos: Pos
}

impl<'a> Lexer<'a> {
    pub fn new(chars: &'a str, filename: Option<Filename>) -> Self { Lexer {chars, pos: Pos::start(filename) } }
}

impl<'a> Lexer<'a> {
    fn peek_char(&self) -> Option<char> { self.chars[self.pos.byte..].chars().next() }

    fn pop_char(&mut self) {
        debug_assert!(self.pos.byte < self.chars.len());

        let mut cs = self.chars[self.pos.byte..].chars();
        let c = cs.next().unwrap();
        self.pos.advance(c);
    }

    fn singleton_char_tok(&mut self, start: Pos, tok: Tok) -> Spanning<Tok> {
        self.pop_char();
        tok.spanning(start, self.pos.clone())
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Spanning<Tok>, Positioned<Error>>;

    fn next(&mut self) -> Option<Self::Item> {
        use Tok::*;
        use Error::*;

        let start = self.pos.clone();

        self.peek_char().map(|c| match c {
            '(' => Ok(self.singleton_char_tok(start, LParen)),
            ')' => Ok(self.singleton_char_tok(start, RParen)),
            
            c => Err(UnexpectedChar(c).at(start))
        })
    }
}
