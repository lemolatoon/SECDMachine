use std::iter::Peekable;
use std::str::Chars;

use crate::LambdaExpression;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    Lambda,
    Dot,
    LParen,
    RParen,
    Identifier(String),
}

#[derive(Debug, Clone)]
pub struct Lexer<'a> {
    chars: Peekable<Chars<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars().peekable(),
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(&c) = self.chars.peek() {
            if c.is_whitespace() {
                self.chars.next();
            } else {
                break;
            }
        }

        match self.chars.next()? {
            'λ' | '\\' => Some(Token::Lambda),
            '.' => Some(Token::Dot),
            '(' => Some(Token::LParen),
            ')' => Some(Token::RParen),
            c if c.is_alphabetic() || c == '\'' => {
                let mut ident = c.to_string();
                while let Some(&c) = self.chars.peek() {
                    if c.is_alphanumeric() || c == '\'' {
                        ident.push(c);
                        self.chars.next();
                    } else {
                        break;
                    }
                }
                Some(Token::Identifier(ident))
            }
            _ => None,
        }
    }
}

pub struct Parser<I: Iterator<Item = Token>> {
    tokens: Peekable<I>,
}

impl<I: Iterator<Item = Token>> Parser<I> {
    pub fn parse(&mut self) -> anyhow::Result<LambdaExpression> {
        self.parse_lambda()
    }

    fn parse_lambda(&mut self) -> anyhow::Result<LambdaExpression> {
        if let Some(Token::Lambda) = self.tokens.peek() {
            // Consume the lambda token
            self.tokens.next();
            let var = if let Some(Token::Identifier(id)) = self.tokens.next() {
                id
            } else {
                return Err(anyhow::anyhow!("Expected identifier after λ"));
            };
            if self.tokens.next() != Some(Token::Dot) {
                return Err(anyhow::anyhow!("Expected '.' after variable in λ"));
            }
            let body = self.parse_lambda()?;
            Ok(LambdaExpression::Lambda(var, Box::new(body)))
        } else {
            self.parse_application()
        }
    }

    fn parse_application(&mut self) -> anyhow::Result<LambdaExpression> {
        let mut expr = self.parse_atom()?;
        while let Some(Token::Identifier(_)) | Some(Token::LParen) = self.tokens.peek() {
            let next = self.parse_atom()?;
            expr = LambdaExpression::Apply(Box::new(expr), Box::new(next));
        }
        Ok(expr)
    }

    fn parse_atom(&mut self) -> anyhow::Result<LambdaExpression> {
        match self.tokens.next() {
            Some(Token::Identifier(id)) => Ok(LambdaExpression::Var(id)),
            Some(Token::LParen) => {
                let expr = self.parse_lambda()?;
                if self.tokens.next() != Some(Token::RParen) {
                    return Err(anyhow::anyhow!("Expected ')'"));
                }
                Ok(expr)
            }
            t => Err(anyhow::anyhow!("Unexpected token: {:?}", t)),
        }
    }
}

pub(crate) fn parse(input: &str) -> anyhow::Result<LambdaExpression> {
    let tokens = Lexer::new(input);
    let mut parser = Parser {
        tokens: tokens.peekable(),
    };
    parser.parse()
}
