#[derive(Debug)]
pub enum Expression {
    Literal(Literal),
    Unary(UnaryOp, Box<Expression>),
    Binary(Box<Expression>, BinaryOp, Box<Expression>),
    Variable(Symbol),
    Assign(Symbol, Box<Expression>),
    Logical(Box<Expression>, LogicalOp, Box<Expression>),
    Get(Box<Expression>, Symbol),
    Call(Box<Expression>, SourceLocation, Vec<Expression>),
}

#[derive(Debug, Clone)]
pub struct SourceLocation {
    pub line: usize,
    pub column: usize,
}

#[derive(Debug)]
pub enum LogicalOp {
    And,
    Or,
}

#[derive(Debug)]
pub enum Literal {
    Integer(i64),
    Double(f64),
    String(String),
    True,
    False,
    Nil,
}

#[derive(Debug)]
pub struct UnaryOp {
    pub line: usize,
    pub column: usize,
    pub typ: UnaryOpType,
}

#[derive(Debug)]
pub enum UnaryOpType {
    Neg,
    Bang,
}

#[derive(Debug)]
pub struct BinaryOp {
    pub line: usize,
    pub column: usize,
    pub typ: BinaryOpType,
}

#[derive(Debug)]
pub enum BinaryOpType {
    Add,
    Sub,
    Mul,
    Div,
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
    Equal,
    NotEqual,
}

#[derive(Debug)]
pub enum Statement {
    Expression(Expression),
    FunctionDeclaration(FunDeclaration),
    CalssDeclaration(ClassDecl),
    If(Expression, Box<Statement>, Option<Box<Statement>>),
    Print(Expression),
    LetDeclaration(Symbol, Option<Expression>),
    Block(Vec<Statement>),
    Return(SourceLocation, Option<Expression>),
    While(Expression, Vec<Statement>),
}

#[derive(Debug)]
pub struct ClassDecl {
    pub name: Symbol,
    pub superclass: Option<Symbol>,
    pub methods: Vec<FunDeclaration>,
    pub properties: Vec<Statement>,
}

#[derive(Debug)]
pub struct FunDeclaration {
    pub name: Symbol,
    pub parameters: Vec<Symbol>,
    pub body: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub line: usize,
    pub column: usize,
    pub name: String,
}
