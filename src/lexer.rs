use crate::pos::{Pos, Positioned, Filename};

#[derive(Debug, Clone)]
pub enum Tok<'a> {
    LParen,
    RParen,

    Id(&'a str),

    Int(isize)
}

impl<'a> Tok<'a> {
    fn spanning(self, start: Pos, end: Pos) -> (Pos, Tok<'a>, Pos) { (start, self, end) }
}

#[derive(Debug)]
pub enum Error {
    UnexpectedChar(char),
    IntOverflow
}

impl Error {
    fn at(self, pos: Pos) -> Positioned<Self> { Positioned {v: self, pos} }
}

fn is_initial(c: char) -> bool { c.is_alphabetic() }

fn is_subsequent(c: char) -> bool { is_initial(c) }

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

    fn singleton_char_tok(&mut self, start: Pos, tok: Tok<'a>) -> (Pos, Tok<'a>, Pos) {
        self.pop_char();
        tok.spanning(start, self.pos.clone())
    }

    fn lex_id(&mut self, start: Pos) -> (Pos, Tok<'a>, Pos) {
        debug_assert!(is_initial(self.peek_char().unwrap()));
        self.pop_char();

        loop {
            match self.peek_char() {
                Some(c) if is_subsequent(c) => self.pop_char(),
                _ => break
            }
        }

        let start_index = start.byte;
        (start, Tok::Id(&self.chars[start_index..self.pos.byte]), self.pos.clone())
    }

    fn lex_number(&mut self, start: Pos, radix: u32, first_digit: u32) -> <Self as Iterator>::Item {
        debug_assert!(self.peek_char().unwrap().is_digit(radix));
        self.pop_char();

        let isize_radix = radix as isize;
        let mut n = first_digit as isize;

        loop {
            match self.peek_char() {
                Some(c) => match c.to_digit(radix) {
                    Some(digit) => {
                        self.pop_char();
                        n = isize_radix.checked_mul(n).and_then(|n| n.checked_add(digit as isize))
                            .ok_or_else(|| Error::IntOverflow.at(start.clone()))?;
                    },

                    None => break
                },

                None => break
            }
        }

        Ok((start, Tok::Int(n), self.pos.clone()))
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<(Pos, Tok<'a>, Pos), Positioned<Error>>;

    fn next(&mut self) -> Option<Self::Item> {
        use Tok::*;
        use Error::*;

        let start = self.pos.clone();

        self.peek_char().map(|c| match c {
            '(' => Ok(self.singleton_char_tok(start, LParen)),
            ')' => Ok(self.singleton_char_tok(start, RParen)),

            c if is_initial(c) => Ok(self.lex_id(start)),

            c if c.is_digit(10) => {
                let radix = 10;
                self.lex_number(start, radix, c.to_digit(radix).unwrap())
            },

            c => Err(UnexpectedChar(c).at(start))
        })
    }
}