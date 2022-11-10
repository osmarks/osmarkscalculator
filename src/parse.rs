use std::str::FromStr;
use anyhow::{Result, anyhow, Context};
use std::fmt;
use inlinable_string::{InlinableString, StringExt};

use crate::util::char_to_string;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token { Number(InlinableString), OpenBracket, CloseBracket, Op(char), EOF, Identifier(InlinableString), OpenSqBracket, CloseSqBracket, Comma, Break }
#[derive(Debug)]
enum LexState {
    Number(InlinableString),
    Identifier(InlinableString),
    None
}

// lexer
// converts input InlinableString to tokens
pub fn lex(input: &str) -> Result<Vec<Token>> {
    let mut toks = vec![];
    let mut state = LexState::None;
    for (index, char) in input.chars().enumerate() {
        state = match (char, state) {
            // if digit seen, switch into number state (and commit existing one if relevant)
            ('0'..='9', LexState::None) => LexState::Number(char_to_string(char)),
            ('0'..='9', LexState::Identifier(s)) => {
                toks.push(Token::Identifier(s));
                LexState::Number(char_to_string(char))
            },
            ('0'..='9', LexState::Number(mut n)) => {
                n.push(char);
                LexState::Number(n)
            },
            // if special character seen, commit existing state and push operator/bracket/comma token
            ('#' | '+' | '(' | ')' | '-' | '/' | '*' | '^' | '=' | '[' | ']' | ',', state) => {
                match state {
                    LexState::Number(s) => toks.push(Token::Number(s)),
                    LexState::Identifier(s) => toks.push(Token::Identifier(s)),
                    _ => ()
                };
                toks.push(match char {
                    '(' => Token::OpenBracket, ')' => Token::CloseBracket,
                    '[' => Token::OpenSqBracket, ']' => Token::CloseSqBracket,
                    ',' => Token::Comma,
                    a => Token::Op(a)
                });
                LexState::None  
            },
            // semicolon or newline is break
            (';' | '\n', state) => {
                match state {
                    LexState::Number(s) => toks.push(Token::Number(s)),
                    LexState::Identifier(s) => toks.push(Token::Identifier(s)),
                    _ => ()
                };
                toks.push(Token::Break);
                LexState::None
            },
            // ignore all whitespace
            (' ', state) => state,
            // treat all unknown characters as part of identifiers
            (char, LexState::None) => { LexState::Identifier(char_to_string(char)) },
            (char, LexState::Identifier(mut s)) => {
                s.push(char);
                LexState::Identifier(s)
            }
            (char, state) => return Err(anyhow!("got {} in state {:?} (char {})", char, state, index))
        }
    }
    // commit last thing
    match state {
        LexState::Number(s) => toks.push(Token::Number(s)),
        LexState::Identifier(s) => toks.push(Token::Identifier(s)),
        _ => ()
    };
    toks.push(Token::EOF);
    Ok(toks)
}

#[derive(Debug)]
pub enum ParseError {
    Invalid(Token)
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::Invalid(tok) => write!(f, "invalid token {:?}", tok)
        }
    }
}
impl std::error::Error for ParseError {}

// parser: contains the sequence of tokens being parsed and current position (index in that)
// no lookahead is supported/used
struct Parser {
    tokens: Vec<Token>,
    position: usize
}

// static table of precedence for each operator
pub fn precedence(c: char) -> usize {
    match c {
        '=' => 0,
        '+' => 1,
        '*' => 2,
        '-' => 1,
        '/' => 2,
        '^' => 3,
        '#' => 4,
        c => panic!("invalid operator char {}", c)
    }
}

fn is_left_associative(c: char) -> bool {
    match c {
        '^' => false,
        _ => true
    }
}

impl Parser {
    // Parsing utility functions
    // Get current token
    fn current(&self) -> Token { self.tokens[self.position].clone() }
    // Advance current token
    fn advance(&mut self) { self.position += 1 }

    // Match current token against predicate and propagate error if it is not matched
    fn expect<T, F: Fn(&Token) -> Result<T, ()>>(&mut self, pred: F) -> Result<T, ParseError> {
        let current = self.current();
        match pred(&current) {
            Ok(r) => {
                self.advance();
                Ok(r)
            },
            Err(()) => Err(ParseError::Invalid(current))
        }
    }

    // Parse "leaf" expression: number, arbitrary expression in brackets, identifier, or call (fn[arg1, arg2])
    fn parse_leaf(&mut self) -> Result<Ast, ParseError> {
        let res = match self.current() {
            Token::OpenBracket => {
                self.advance();
                let res = self.parse_expr(0)?;
                self.expect(|t| if *t == Token::CloseBracket { Ok(()) } else { Err(()) })?;
                res
            },
            Token::Number(n) => {
                let x = i128::from_str(&n).unwrap();
                self.advance();
                Ast::Num(x)
            },
            Token::Identifier(s) => {
                self.advance();
                Ast::Identifier(s)
            }
            t => return Err(ParseError::Invalid(t))
        };
        // Detection of call syntax: if [ occurs, try and parse comma-separated arguments until a ]
        if let Token::OpenSqBracket = self.current() {
            self.advance();
            let mut args = vec![];
            loop {
                args.push(self.parse_expr(0)?);
                match self.expect(|t| if *t == Token::CloseSqBracket || *t == Token::Comma { Ok(t.clone()) } else { Err(()) })? {
                    Token::CloseSqBracket => break,
                    _ => ()
                }
            }
            Ok(Ast::Call(Box::new(res), args))
        } else {
            Ok(res)
        }
    }

    // Parse expression including operators, using precedence climbing
    fn parse_expr(&mut self, prec: usize) -> Result<Ast, ParseError> {
        let mut result = self.parse_leaf()?;
        loop {
            match self.current() {
                Token::Op(op) if precedence(op) >= prec => {
                    self.advance();
                    let nested_precedence = if is_left_associative(op) { precedence(op) + 1 } else { precedence(op) };
                    let next = self.parse_expr(nested_precedence)?;
                    result = Ast::Op(op, Box::new(result), Box::new(next))
                },
                // Break out of loop if operator's precedence is lower, or nonoperator thing encountered
                // This means that a lower-precedence operator will become part of the tree enclosing the current one
                _ => break
            };
        };
        Ok(result)
    }
}

pub fn parse(t: Vec<Token>) -> Result<Ast> {
    let mut parser = Parser {
        tokens: t,
        position: 0
    };
    // Provide slightly more helpful error message indicating the token which isn't valid
    let result = parser.parse_expr(0).with_context(|| format!("at token {}", parser.position))?;
    if parser.current() != Token::EOF { return Err(anyhow!("Expected EOF at end of token sequence")) }
    Ok(result)
}

#[derive(Debug)]
pub enum Ast {
    Num(i128),
    Identifier(InlinableString),
    Op(char, Box<Ast>, Box<Ast>),
    Call(Box<Ast>, Vec<Ast>)
}