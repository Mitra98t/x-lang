//! Title: Lexer
//! Desc: The lexer is responsible for reading the input and returning tokens.
//! Expected: The lexer should return the tokens for the input string.

#[derive(Debug, PartialEq, Clone)]
pub enum TokenType {
    Illegal,
    EOF,
    // Identifiers + literals
    Ident,
    Int,
    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,
    LT,
    LE,
    GT,
    GE,
    EQ,
    NotEQ,
    Or,
    And,
    // Delimiters
    Dot,
    Comma,
    Semicolon,
    LParen,
    RParen,
    LSquare,
    RSquare,
    LBrace,
    RBrace,
    // Keywords
    Class,
    Function,
    Let,
    True,
    False,
    If,
    Else,
    For,
    While,
    Return,
    Print,
    Nil,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Literal {
    Ident(String),
    Integer(i64),
    // Double(f64),
    String(String),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub typ: TokenType,
    pub lexeme: Vec<u8>,
    pub literal: Option<Literal>,
    pub line: usize,
    pub column: usize,
}

pub struct Lexer {
    input: String,
    position: usize,
    read_position: usize,
    ch: char,
    line: usize,
    column: usize,
}

impl Lexer {
    /// Create a new lexer.
    ///
    /// * `input`: A string containing the input to be tokenized.
    pub fn new(input: String) -> Lexer {
        let l = Lexer {
            input,
            position: 0,
            read_position: 0,
            ch: '\0',
            line: 1,
            column: 1,
        };
        l
    }

    /// Read the next character and advance the position.
    /// If the read position is greater than the length of the input, set the character to '\0'.
    fn read_char(&mut self) {
        if self.read_position >= self.input.len() {
            self.ch = '\0';
        } else {
            self.ch = self.input.chars().nth(self.read_position).unwrap();
        }
        if self.ch == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        self.position = self.read_position;
        self.read_position += 1;
    }

    /// Return the next character without advancing the position.
    /// If the read position is greater than the length of the input, return '\0'.
    fn peek_char(&self) -> char {
        if self.read_position >= self.input.len() {
            '\0'
        } else {
            self.input.chars().nth(self.read_position).unwrap()
        }
    }

    /// Skip whitespace characters.
    /// This function advances the position until a non-whitespace character is found.
    fn skip_whitespace(&mut self) {
        while self.ch.is_whitespace() {
            self.read_char();
        }
    }

    /// Read an identifier.
    /// This function advances the position until a non-alphabetic character is found.
    /// TODO: symbols like _ should be allowed in identifiers.
    fn read_identifier(&mut self) -> String {
        let position = self.position;
        while self.ch.is_alphanumeric() || self.ch == '_' {
            self.read_char();
        }
        self.back_one_char();
        self.input[position..self.position].to_string()
    }

    fn back_one_char(&mut self) {
        self.read_position -= 1;
        self.ch = self.input.chars().nth(self.read_position).unwrap();
        if self.ch == '\n' {
            self.line -= 1;
            self.column = 1;
        } else {
            self.column -= 1;
        }
    }

    /// Return the next token.
    /// This function skips whitespace characters and returns the next token.
    /// If the character is a letter, it reads an identifier.
    /// If the character is a digit, it reads a number.
    fn next_token(&mut self) -> Token {
        self.skip_whitespace();
        let mut literal_value: Option<Literal> = None;
        let mut lexeme = Vec::new();
        let tok_type: TokenType = match self.ch {
            '=' => {
                if self.peek_char() == '=' {
                    self.read_char();
                    TokenType::EQ
                } else {
                    TokenType::Assign
                }
            }
            '+' => TokenType::Plus,
            '-' => TokenType::Minus,
            '!' => {
                if self.peek_char() == '=' {
                    self.read_char();
                    TokenType::NotEQ
                } else {
                    TokenType::Bang
                }
            }
            '*' => TokenType::Asterisk,
            '/' => TokenType::Slash,
            '&' => {
                if self.peek_char() == '&' {
                    self.read_char();
                    TokenType::And
                } else {
                    TokenType::Illegal
                }
            }
            '|' => {
                if self.peek_char() == '|' {
                    self.read_char();
                    TokenType::Or
                } else {
                    TokenType::Illegal
                }
            }
            '<' => {
                if self.peek_char() == '=' {
                    self.read_char();
                    TokenType::LE
                } else {
                    TokenType::LT
                }
            }
            '>' => {
                if self.peek_char() == '=' {
                    self.read_char();
                    TokenType::GE
                } else {
                    TokenType::GT
                }
            }
            ';' => TokenType::Semicolon,
            '(' => TokenType::LParen,
            ')' => TokenType::RParen,
            ',' => TokenType::Comma,
            '.' => TokenType::Dot,
            '{' => TokenType::LBrace,
            '}' => TokenType::RBrace,
            '[' => TokenType::LSquare,
            ']' => TokenType::RSquare,
            '\0' => TokenType::EOF,
            _ => {
                if self.ch.is_alphabetic() || self.ch == '_' {
                    let ident = self.read_identifier();
                    match ident.as_str() {
                        "fn" => TokenType::Function,
                        "let" => TokenType::Let,
                        "true" => TokenType::True,
                        "false" => TokenType::False,
                        "if" => TokenType::If,
                        "else" => TokenType::Else,
                        "for" => TokenType::For,
                        "while" => TokenType::While,
                        "return" => TokenType::Return,
                        "null" => TokenType::Nil,
                        "class" => TokenType::Class,
                        "print" => TokenType::Print,
                        _ => {
                            literal_value = Some(Literal::Ident(ident.clone()));
                            lexeme = ident.into_bytes();
                            TokenType::Ident
                        }
                    }
                } else if self.ch.is_digit(10) {
                    literal_value = Some(Literal::Integer(self.read_number()));
                    TokenType::Int
                } else {
                    TokenType::Illegal
                }
            }
        };
        self.read_char();
        Token {
            lexeme,
            literal: literal_value,
            typ: tok_type,
            line: self.line,
            column: self.column,
        }
    }

    /// Read a number.
    /// This function advances the position until a non-digit character is found.
    fn read_number(&mut self) -> i64 {
        let position = self.position;
        while self.ch.is_digit(10) {
            self.read_char();
        }
        self.back_one_char();
        self.input[position..self.position].parse().unwrap()
    }

    /// Run the lexer.
    /// This function reads the input and returns a list of tokens.
    /// @return A list of tokens.
    pub fn run(&mut self) -> Vec<Token> {
        self.read_char();
        let mut tok_list = Vec::new();
        loop {
            let tok = self.next_token();
            if tok.typ == TokenType::EOF {
                break;
            }
            tok_list.push(tok);
        }
        tok_list
    }
}
