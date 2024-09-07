use crate::expressions;
use crate::expressions::BinaryOp;
use crate::expressions::BinaryOpType;
use crate::expressions::Expression;
use crate::expressions::Literal;
use crate::expressions::LogicalOp;
use crate::expressions::Statement;
use crate::expressions::UnaryOp;
use crate::expressions::UnaryOpType;
use crate::lexer;
use crate::lexer::Token;
use crate::lexer::TokenType;

use std::fmt;

#[derive(Clone)]
pub enum Error {
    UnexpectedToken(Token),
    TokenMismatch {
        expected: TokenType,
        found: Token,
        maybe_on_err_string: Option<String>,
    },
    MaxParamsExceeded {
        kind: FunctionKind,
        line: usize,
        column: usize,
    },
    ReturnNotInFun {
        line: usize,
        column: usize,
    },
    InvalidAssignment {
        line: usize,
        column: usize,
    },
    TooManyArguments {
        line: usize,
        column: usize,
    },
    ExpectedExpression {
        token_type: TokenType,
        line: usize,
        column: usize,
    },
    InvalidTokenInUnaryOp {
        token_type: TokenType,
        line: usize,
        column: usize,
    },
    InvalidTokenInBinaryOp {
        token_type: TokenType,
        line: usize,
        column: usize,
    },
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            Error::UnexpectedToken(tok) => write!(
                f,
                "Unexpected token {:?} at line={},col={}",
                tok.typ, tok.line, tok.column
            ),
            Error::InvalidAssignment { line, column } => {
                write!(
                    f,
                    "invalid assignment target at line={},col={}",
                    line, column
                )
            }
            Error::TokenMismatch {
                maybe_on_err_string,
                expected,
                found,
            } => {
                write!(
                    f,
                    "Expected token {:?} but found {:?} at line={},col={}",
                    expected, found.typ, found.line, found.column
                )?;
                if let Some(on_err_string) = maybe_on_err_string {
                    write!(f, ": {}", on_err_string)?;
                }
                fmt::Result::Ok(())
            }
            _ => write!(f, "Unhandled error"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum FunctionKind {
    Function,
    Method,
    Lambda,
}

/*
Recursive descent using the following grammar

program     → declaration* EOF ;

declaration → classDecl
            | funDecl
            | varDecl
            | statement ;

classDecl → "class" IDENTIFIER ( "<" IDENTIFIER )?
            "{" function* "}" ;

funDecl  → "fun" function ;
function → IDENTIFIER "(" parameters? ")" block ;
parameters  → IDENTIFIER ( "," IDENTIFIER )* ;

statement → exprStmt
          | forStmt
          | ifStmt
          | printStmt
          | returnStmt
          | whileStmt
          | block ;

returnStmt → "return" expression? ";" ;

forStmt   → "for" "(" ( varDecl | exprStmt | ";" )
                      expression? ";"
                      expression? ")" statement ;

whileStmt → "while" "(" expression ")" statement ;

ifStmt    → "if" "(" expression ")" statement ( "else" statement )? ;

block     → "{" declaration* "}" ;

varDecl → "var" IDENTIFIER ( "=" expression )? ";" ;

exprStmt  → expression ";" ;
printStmt → "print" expression ";" ;

expression → assignment ;
assignment → ( call "." )? IDENTIFIER "=" assignment
           | logic_or;
logic_or   → logic_and ( "or" logic_and )* ;
logic_and  → equality ( "and" equality )* ;

equality       → comparison ( ( "!=" | "==" ) comparison )* ;
comparison     → addition ( ( ">" | ">=" | "<" | "<=" ) addition )* ;
addition       → multiplication ( ( "-" | "+" ) multiplication )* ;
multiplication → unary ( ( "/" | "*" ) unary )* ;
unary → ( "!" | "-" ) unary | call ;
call → primary ( "(" arguments? ")" | "." IDENTIFIER | "[" expression "]" )* ;
arguments → expression ( "," expression )* ;

primary → "true" | "false" | "nil" | "this"
        | NUMBER | STRING | IDENTIFIER | "(" expression ")"
        | "super" "." IDENTIFIER
        | "[" arguments? "]" ;

*/

#[derive(Debug)]
pub struct Parser {
    tokens: Vec<Token>,
    cur_token: usize,
    in_fundec: bool,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Parser {
        let p = Parser {
            tokens,
            cur_token: 0,
            in_fundec: false,
        };
        p
    }

    fn advance(&mut self) -> Token {
        if self.cur_token < self.tokens.len() {
            self.cur_token += 1;
        }
        self.previous()
    }

    fn peek(&self) -> Token {
        if self.cur_token >= self.tokens.len() {
            panic!("Unexpected end of tokens");
        }
        self.tokens[self.cur_token].clone()
    }

    fn previous(&self) -> Token {
        self.tokens[self.cur_token - 1].clone()
    }

    fn match_token(&mut self, typ: TokenType) -> bool {
        if self.peek().typ == typ {
            self.advance();
            true
        } else {
            false
        }
    }

    fn match_one_of(&mut self, types: Vec<TokenType>) -> bool {
        for typ in types {
            if self.peek().typ == typ {
                self.advance();
                return true;
            }
        }
        false
    }

    fn check(&self, typ: TokenType) -> bool {
        if self.cur_token >= self.tokens.len() {
            return false;
        }
        self.peek().typ == typ
    }

    fn consume(&mut self, typ: TokenType, on_error_str: &str) -> Result<Token, Error> {
        if self.peek().typ == typ {
            return Ok(self.advance());
        } else {
            Err(Error::TokenMismatch {
                expected: typ,
                found: self.peek(),
                maybe_on_err_string: Some(on_error_str.into()),
            })
        }
    }

    pub fn parse(&mut self) -> Result<Vec<Statement>, Error> {
        let mut statements: Vec<Statement> = Vec::new();
        while self.cur_token < self.tokens.len() {
            let stmt = self.declaration()?;
            statements.push(stmt);
        }
        Ok(statements)
    }

    fn declaration(&mut self) -> Result<Statement, Error> {
        if self.match_token(TokenType::Let) {
            return self.let_declaration();
        }
        if self.match_token(TokenType::Function) {
            return Ok(Statement::FunctionDeclaration(
                self.function_declaration(FunctionKind::Function)?,
            ));
        }
        self.statement()
    }

    fn function_declaration(
        &mut self,
        kind: FunctionKind,
    ) -> Result<expressions::FunDeclaration, Error> {
        let name_tok = self
            .consume(
                TokenType::Ident,
                format!("Expected {:?} name", kind).as_ref(),
            )?
            .clone();

        let fun_symbol = expressions::Symbol {
            line: name_tok.line,
            column: name_tok.column,
            name: String::from_utf8(name_tok.lexeme).unwrap(),
        };

        let (parameters, body) = self.parameters_and_body(kind)?;

        Ok(expressions::FunDeclaration {
            name: fun_symbol,
            parameters,
            body,
        })
    }

    fn parameters_and_body(
        &mut self,
        kind: FunctionKind,
    ) -> Result<(Vec<expressions::Symbol>, Vec<Statement>), Error> {
        self.consume(
            TokenType::LParen,
            format!("Expected '(' after {:?} name", kind).as_ref(),
        )?;

        let mut parameters: Vec<expressions::Symbol> = Vec::new();

        if !self.check(TokenType::RParen) {
            loop {
                if parameters.len() >= 255 {
                    let peek = self.peek();
                    return Err(Error::MaxParamsExceeded {
                        kind,
                        line: peek.line,
                        column: peek.column,
                    });
                }

                let tok = self
                    .consume(TokenType::Ident, "Expected parameter name")
                    .unwrap()
                    .clone();

                parameters.push(expressions::Symbol {
                    line: tok.line,
                    column: tok.column,
                    name: String::from_utf8(tok.lexeme).unwrap(),
                });

                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }

        let parameters = parameters;

        self.consume(
            TokenType::RParen,
            format!("Expected ')' after {:?} parameters", kind).as_ref(),
        )?;

        self.consume(
            TokenType::LBrace,
            format!("Expected '{{' before {:?} body", kind).as_ref(),
        )?;

        let saved_is_in_fundec = self.in_fundec;
        self.in_fundec = true;
        let body = self.block()?;
        self.in_fundec = saved_is_in_fundec;

        Ok((parameters, body))
    }

    fn block(&mut self) -> Result<Vec<Statement>, Error> {
        let mut statements: Vec<Statement> = Vec::new();
        while !self.check(TokenType::RBrace) && self.cur_token < self.tokens.len() {
            let stmt = self.declaration()?;
            statements.push(stmt);
        }
        self.consume(TokenType::RBrace, "Expected '}' after block")?;
        Ok(statements)
    }

    fn let_declaration(&mut self) -> Result<Statement, Error> {
        let name = self.consume(TokenType::Ident, "Expected identifier after 'let'")?;
        let maybe_inizializer = if self.match_token(TokenType::Assign) {
            Some(self.expression()?)
        } else {
            None
        };

        self.consume(TokenType::Semicolon, "Expected ';' after let declaration")?;
        Ok(Statement::LetDeclaration(
            expressions::Symbol {
                line: name.line,
                column: name.column,
                name: String::from_utf8(name.lexeme).unwrap(),
            },
            maybe_inizializer,
        ))
    }

    fn statement(&mut self) -> Result<Statement, Error> {
        if self.match_token(TokenType::Print) {
            return self.print_statement();
        }
        if self.match_token(TokenType::Return) {
            return self.return_statement();
        }
        if self.match_token(TokenType::If) {
            return self.if_statement();
        }
        if self.match_token(TokenType::While) {
            return self.while_statement();
        }
        if self.match_token(TokenType::For) {
            return self.for_statement();
        }
        if self.match_token(TokenType::LBrace) {
            return Ok(Statement::Block(self.block()?));
        }

        self.expression_statement()
    }

    fn print_statement(&mut self) -> Result<Statement, Error> {
        self.consume(TokenType::LParen, "Expected '(' after 'print'")?;
        let expr = self.expression()?;
        self.consume(TokenType::RParen, "Expected ')' after expression")?;
        self.consume(TokenType::Semicolon, "Expected ';' after expression")?;
        Ok(Statement::Print(expr))
    }

    fn return_statement(&mut self) -> Result<Statement, Error> {
        let previous = self.previous().clone();
        if !self.in_fundec {
            return Err(Error::ReturnNotInFun {
                line: previous.line,
                column: previous.column,
            });
        }

        let maybe_return_value = if !self.match_token(TokenType::Semicolon) {
            Some(self.expression()?)
        } else {
            None
        };

        if maybe_return_value.is_some() {
            self.consume(TokenType::Semicolon, "Expected ';' after return value")?;
        }

        Ok(Statement::Return(
            expressions::SourceLocation {
                line: previous.line,
                column: previous.column,
            },
            maybe_return_value,
        ))
    }

    fn if_statement(&mut self) -> Result<Statement, Error> {
        self.consume(TokenType::LParen, "Expected '(' after 'if'")?;
        let condition = self.expression()?;
        self.consume(TokenType::RParen, "Expected ')' after if condition")?;

        let then_branch = Box::new(self.statement()?);
        let maybe_else_branch = if self.match_token(TokenType::Else) {
            Some(Box::new(self.statement()?))
        } else {
            None
        };

        Ok(Statement::If(condition, then_branch, maybe_else_branch))
    }

    fn while_statement(&mut self) -> Result<Statement, Error> {
        self.consume(TokenType::LParen, "Expected '(' after 'while'")?;
        let condition = self.expression()?;
        self.consume(TokenType::RParen, "Expected ')' after while condition")?;
        self.consume(TokenType::LBrace, "Expected '{' before while body")?;
        let body = self.block()?;

        Ok(Statement::While(condition, body))
    }

    fn for_statement(&mut self) -> Result<Statement, Error> {
        self.consume(TokenType::LParen, "Expected '(' after 'for'")?;

        let initializer: Option<Statement> = if self.match_token(TokenType::Semicolon) {
            None
        } else if self.match_token(TokenType::Let) {
            Some(self.let_declaration()?)
        } else {
            Some(self.expression_statement()?)
        };

        let condition = if !self.check(TokenType::Semicolon) {
            self.expression()?
        } else {
            Expression::Literal(Literal::True)
        };
        self.consume(TokenType::Semicolon, "Expected ';' after loop condition")?;

        let increment = if !self.check(TokenType::RParen) {
            Some(self.expression()?)
        } else {
            None
        };
        self.consume(TokenType::RParen, "Expected ')' after for clauses")?;

        self.consume(TokenType::LBrace, "Expected '{' before for body")?;
        let mut body = self.block()?;

        if let Some(increment) = increment {
            body.push(Statement::Expression(increment));
        }

        if let Some(initializer) = initializer {
            body.insert(0, initializer);
        }

        Ok(Statement::While(condition, body))
    }

    fn expression_statement(&mut self) -> Result<Statement, Error> {
        let expr = self.expression()?;
        match self.consume(TokenType::Semicolon, "Expected ';' after expression.") {
            Ok(_) => (),
            Err(e) => return Err(e),
        }
        Ok(Statement::Expression(expr))
    }

    fn expression(&mut self) -> Result<Expression, Error> {
        self.assignment()
    }

    fn assignment(&mut self) -> Result<Expression, Error> {
        let expr = self.or()?;
        if self.match_token(TokenType::Assign) {
            let equals = self.previous().clone();
            let new_value = self.assignment()?;
            match expr {
                Expression::Variable(symbol) => Ok(Expression::Assign(symbol, Box::new(new_value))),
                _ => Err(Error::InvalidAssignment {
                    line: equals.line,
                    column: equals.column,
                }),
            }
        } else {
            Ok(expr)
        }
    }

    fn or(&mut self) -> Result<Expression, Error> {
        let mut expr = self.and()?;
        while self.match_token(TokenType::Or) {
            let right = self.and()?;
            expr = Expression::Logical(Box::new(expr), expressions::LogicalOp::Or, Box::new(right));
        }
        Ok(expr)
    }

    fn and(&mut self) -> Result<Expression, Error> {
        let mut expr = self.equality()?;
        while self.match_token(TokenType::And) {
            let right = self.equality()?;
            expr =
                Expression::Logical(Box::new(expr), expressions::LogicalOp::And, Box::new(right));
        }
        Ok(expr)
    }

    fn equality(&mut self) -> Result<Expression, Error> {
        let mut expr = self.comparison()?;
        while self.match_one_of(vec![TokenType::EQ, TokenType::NotEQ]) {
            let op_tok = self.previous().clone();
            let right = Box::new(self.comparison()?);
            let binary_op_maybe = Parser::operator_tok_to_binary_op(op_tok);
            match binary_op_maybe {
                Ok(binary_op) => {
                    expr = Expression::Binary(Box::new(expr), binary_op, right);
                }
                Err(e) => return Err(e),
            }
        }
        Ok(expr)
    }

    fn comparison(&mut self) -> Result<Expression, Error> {
        let mut expr = self.addition()?;
        while self.match_one_of(vec![
            TokenType::LT,
            TokenType::LE,
            TokenType::GT,
            TokenType::GE,
        ]) {
            let op_tok = self.previous().clone();
            let right = Box::new(self.addition()?);
            let binary_op_maybe = Parser::operator_tok_to_binary_op(op_tok);
            match binary_op_maybe {
                Ok(binary_op) => {
                    expr = Expression::Binary(Box::new(expr), binary_op, right);
                }
                Err(e) => return Err(e),
            }
        }
        Ok(expr)
    }

    fn addition(&mut self) -> Result<Expression, Error> {
        let mut expr = self.multiplication()?;
        while self.match_one_of(vec![TokenType::Plus, TokenType::Minus]) {
            let op_tok = self.previous().clone();
            let right = Box::new(self.multiplication()?);
            let binary_op_maybe = Parser::operator_tok_to_binary_op(op_tok);
            match binary_op_maybe {
                Ok(binary_op) => {
                    expr = Expression::Binary(Box::new(expr), binary_op, right);
                }
                Err(e) => return Err(e),
            }
        }
        Ok(expr)
    }

    fn multiplication(&mut self) -> Result<Expression, Error> {
        let mut expr = self.unary()?;
        while self.match_one_of(vec![TokenType::Asterisk, TokenType::Slash]) {
            let op_tok = self.previous().clone();
            let right = Box::new(self.unary()?);
            let binary_op_maybe = Parser::operator_tok_to_binary_op(op_tok);
            match binary_op_maybe {
                Ok(binary_op) => {
                    expr = Expression::Binary(Box::new(expr), binary_op, right);
                }
                Err(e) => return Err(e),
            }
        }
        Ok(expr)
    }

    fn unary(&mut self) -> Result<Expression, Error> {
        if self.match_one_of(vec![TokenType::Bang, TokenType::Minus]) {
            let op_tok = self.previous().clone();
            let right = Box::new(self.unary()?);
            let unary_op_maybe = Parser::operator_tok_to_unary_op(op_tok);
            return match unary_op_maybe {
                Ok(unary_op) => Ok(Expression::Unary(unary_op, right)),
                Err(e) => Err(e),
            };
        }
        self.call()
    }

    fn call(&mut self) -> Result<Expression, Error> {
        let mut expr = self.primary()?;
        loop {
            if self.match_token(TokenType::LParen) {
                expr = self.finish_call(expr)?;
            } else if self.match_token(TokenType::Dot) {
                let name_tok = self
                    .consume(TokenType::Ident, "Expected property name after '.'")?
                    .clone();
                expr = Expression::Get(
                    Box::new(expr),
                    expressions::Symbol {
                        line: name_tok.line,
                        column: name_tok.column,
                        name: String::from_utf8(name_tok.lexeme).unwrap(),
                    },
                );
            } else {
                break;
            }
        }
        Ok(expr)
    }

    fn finish_call(&mut self, callee: Expression) -> Result<Expression, Error> {
        let mut arguments: Vec<Expression> = Vec::new();
        if !self.check(TokenType::RParen) {
            loop {
                if arguments.len() >= 255 {
                    let peek = self.peek();
                    return Err(Error::TooManyArguments {
                        line: peek.line,
                        column: peek.column,
                    });
                }
                arguments.push(self.expression()?);
                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }
        let paren = self.consume(TokenType::RParen, "Expected ')' after arguments")?;
        Ok(Expression::Call(
            Box::new(callee),
            expressions::SourceLocation {
                line: paren.line,
                column: paren.column,
            },
            arguments,
        ))
    }

    fn primary(&mut self) -> Result<Expression, Error> {
        if self.match_token(TokenType::False) {
            return Ok(Expression::Literal(Literal::False));
        }
        if self.match_token(TokenType::True) {
            return Ok(Expression::Literal(Literal::True));
        }
        if self.match_token(TokenType::Nil) {
            return Ok(Expression::Literal(Literal::Nil));
        }
        if self.match_token(TokenType::Int) {
            match &self.previous().literal {
                Some(lexer::Literal::Integer(n)) => {
                    return Ok(Expression::Literal(Literal::Integer(*n)));
                }
                _ => {
                    return Err(Error::UnexpectedToken(self.peek()));
                }
            }
        }
        if self.match_token(TokenType::Ident) {
            match self.previous().literal {
                Some(lexer::Literal::Ident(ident)) => {
                    return Ok(Expression::Variable(expressions::Symbol {
                        line: self.previous().line,
                        column: self.previous().column,
                        name: ident.clone(),
                    }));
                }
                Some(i) => panic!("Internal error when parsing: {:?}", i),
                None => panic!("Internal error when parsing identifier, found no literal"),
            }
        }
        Err(Error::UnexpectedToken(self.peek()))
    }

    fn operator_tok_to_binary_op(op_tok: Token) -> Result<BinaryOp, Error> {
        match op_tok.typ {
            TokenType::Plus => Ok(BinaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: BinaryOpType::Add,
            }),
            TokenType::Minus => Ok(BinaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: BinaryOpType::Sub,
            }),
            TokenType::Asterisk => Ok(BinaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: BinaryOpType::Mul,
            }),
            TokenType::Slash => Ok(BinaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: BinaryOpType::Div,
            }),
            TokenType::LT => Ok(BinaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: BinaryOpType::LessThan,
            }),
            TokenType::LE => Ok(BinaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: BinaryOpType::LessThanEqual,
            }),
            TokenType::GT => Ok(BinaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: BinaryOpType::GreaterThan,
            }),
            TokenType::GE => Ok(BinaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: BinaryOpType::GreaterThanEqual,
            }),
            TokenType::EQ => Ok(BinaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: BinaryOpType::Equal,
            }),
            TokenType::NotEQ => Ok(BinaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: BinaryOpType::NotEqual,
            }),
            _ => Err(Error::InvalidTokenInBinaryOp {
                token_type: op_tok.typ,
                line: op_tok.line,
                column: op_tok.column,
            }),
        }
    }

    fn operator_tok_to_unary_op(op_tok: Token) -> Result<UnaryOp, Error> {
        match op_tok.typ {
            TokenType::Minus => Ok(UnaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: UnaryOpType::Neg,
            }),
            TokenType::Bang => Ok(UnaryOp {
                line: op_tok.line,
                column: op_tok.column,
                typ: UnaryOpType::Bang,
            }),
            _ => Err(Error::InvalidTokenInUnaryOp {
                token_type: op_tok.typ,
                line: op_tok.line,
                column: op_tok.column,
            }),
        }
    }

    pub fn pretty_print_ast(nodes: Vec<Statement>) {
        fn print_indent(indent: i32) {
            for _ in 0..indent {
                print!("  ");
            }
        }
        fn print_expression(node: Expression, indent: i32) {
            print_indent(indent);
            match node {
                Expression::Literal(literal) => match literal {
                    Literal::Integer(n) => {
                        println!("{}", n);
                    }
                    Literal::Double(d) => {
                        println!("{}", d);
                    }
                    Literal::String(s) => {
                        println!("{}", s);
                    }
                    Literal::True => {
                        println!("true");
                    }
                    Literal::False => {
                        println!("false");
                    }
                    Literal::Nil => {
                        println!("nil");
                    }
                },
                Expression::Unary(unary_op, expr) => {
                    match unary_op.typ {
                        UnaryOpType::Neg => {
                            println!("negation(");
                        }
                        UnaryOpType::Bang => {
                            println!("not(");
                        }
                    }
                    print_expression(*expr, indent + 1);
                    print_indent(indent);
                    println!(")");
                }
                Expression::Binary(left, binary_op, right) => {
                    match binary_op.typ {
                        BinaryOpType::Add => {
                            println!("addition(");
                        }
                        BinaryOpType::Sub => {
                            println!("subtraction(");
                        }
                        BinaryOpType::Mul => {
                            println!("multiplication(");
                        }
                        BinaryOpType::Div => {
                            println!("division(");
                        }
                        BinaryOpType::LessThan => {
                            println!("less than(");
                        }
                        BinaryOpType::LessThanEqual => {
                            println!("less than or equal(");
                        }
                        BinaryOpType::GreaterThan => {
                            println!("greater than(");
                        }
                        BinaryOpType::GreaterThanEqual => {
                            println!("greater than or equal(");
                        }
                        BinaryOpType::Equal => {
                            println!("equal(");
                        }
                        BinaryOpType::NotEqual => {
                            println!("not equal(");
                        }
                    }
                    print_expression(*left, indent + 1);
                    print_expression(*right, indent + 1);
                    print_indent(indent);
                    println!(")");
                }
                Expression::Logical(left, logical_op, right) => {
                    match logical_op {
                        LogicalOp::And => {
                            println!("and(");
                        }
                        LogicalOp::Or => {
                            println!("or(");
                        }
                    }
                    print_expression(*left, indent + 1);
                    print_expression(*right, indent + 1);
                    print_indent(indent);
                    println!(")");
                }
                Expression::Variable(symbol) => {
                    println!("{}", symbol.name);
                }
                Expression::Assign(symbol, expr) => {
                    println!("assignment(");
                    print_indent(indent + 1);
                    println!("{}", symbol.name);
                    print_expression(*expr, indent + 1);
                    print_indent(indent);
                    println!(")");
                }
                Expression::Get(expr, symbol) => {
                    println!("get(");
                    print_expression(*expr, indent + 1);
                    print_indent(indent + 1);
                    println!("{}", symbol.name);
                    print_indent(indent);
                    println!(")");
                }
                Expression::Call(callee, _, arguments) => {
                    println!("call(");
                    print_expression(*callee, indent + 1);
                    for arg in arguments {
                        print_expression(arg, indent + 1);
                    }
                    print_indent(indent);
                    println!(")");
                }
            }
        }
        fn print_node(node: Statement, indent: i32) {
            print_indent(indent);
            match node {
                Statement::Expression(expr) => {
                    println!("Expression(");
                    print_expression(expr, indent + 1);
                    print_indent(indent);
                    println!(")");
                }
                Statement::LetDeclaration(symbol, maybe_expr) => {
                    println!("let {} = ", symbol.name);
                    if let Some(expr) = maybe_expr {
                        print_expression(expr, indent + 1);
                    } else {
                        println!("nil");
                    }
                    print_indent(indent);
                    println!(";");
                }
                Statement::FunctionDeclaration(fun_decl) => {
                    println!("FunctionDeclaration(");
                    print_indent(indent + 1);
                    println!("{}", fun_decl.name.name);
                    for param in fun_decl.parameters {
                        print_indent(indent + 1);
                        println!("{}", param.name);
                    }
                    for stmt in fun_decl.body {
                        print_indent(indent + 1);
                        println!("body(");
                        print_node(stmt, indent + 2);
                        print_indent(indent + 1);
                        println!(")");
                    }
                    print_indent(indent);
                    println!(")");
                }
                Statement::If(condition, then_branch, maybe_else_branch) => {
                    println!("If(");
                    print_expression(condition, indent + 1);
                    print_indent(indent + 1);
                    println!("then(");
                    print_node(*then_branch, indent + 2);
                    print_indent(indent + 1);
                    println!(")");
                    if let Some(else_branch) = maybe_else_branch {
                        print_indent(indent + 1);
                        println!("else(");
                        print_node(*else_branch, indent + 2);
                        print_indent(indent + 1);
                        println!(")");
                    }
                    print_indent(indent);
                    println!(")");
                }
                Statement::Return(_, maybe_expr) => {
                    println!("Return(");
                    if let Some(expr) = maybe_expr {
                        print_expression(expr, indent + 1);
                    }
                    print_indent(indent);
                    println!(")");
                }
                Statement::While(condition, body) => {
                    println!("While(");
                    print_indent(indent + 1);
                    println!("condition(");
                    print_expression(condition, indent + 2);
                    print_indent(indent + 1);
                    println!(")");
                    print_indent(indent + 1);
                    println!("body(");
                    for stmt in body {
                        print_node(stmt, indent + 2);
                    }
                    print_indent(indent + 1);
                    println!(")");
                    println!(")");
                }
                Statement::Block(statements) => {
                    println!("Block(");
                    for stmt in statements {
                        print_node(stmt, indent + 1);
                    }
                    print_indent(indent);
                    println!(")");
                }
                Statement::Print(expr) => {
                    println!("Print(");
                    print_expression(expr, indent + 1);
                    print_indent(indent);
                    println!(")");
                }
            }
        }
        for node in nodes {
            print_node(node, 0);
        }
    }
}
