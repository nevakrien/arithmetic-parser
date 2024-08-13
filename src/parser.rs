use crate::lexer::Token;
use crate::lexer::Lexer;
use std::error::Error;
use std::fmt;
use std::io::Read;
use std::str::FromStr;
use std::vec::Vec;

#[derive(Debug)]
pub struct LineParseErrors(Vec<LineParseError>);

impl LineParseErrors {
    // Delegate the methods you need
    pub fn new() -> Self {
        LineParseErrors(Vec::new())
    }

    pub fn push(&mut self, error: LineParseError) {
        self.0.push(error);
    }

    // pub fn extend(&mut self, error: LineParseErrors) {
    //     self.0.extend(error.0);
    // }

    // pub fn len(&self) -> usize {
    //     self.0.len()
    // }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    // pub fn get(&self, index: usize) -> Option<&LineParseError> {
    //     self.0.get(index)
    // }
    
    // You can add more methods as needed to fully wrap the Vec functionality
}

impl fmt::Display for LineParseErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for error in &self.0 {
            writeln!(f, "{}", error)?;
        }
        Ok(())
    }
}

impl Error for LineParseErrors {}



#[derive(Debug)]
pub struct LineParseError {
    pub error: ParseError,
    pub line: u32,
}

impl LineParseError {
    // Constructor method
    pub fn new(error: ParseError, line: u32) -> Self {
        LineParseError { error, line }
    }
}

impl fmt::Display for LineParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ERROR at line [{}]: {}", self.line, self.error)
    }
}

impl Error for LineParseError {}

#[derive(Debug)]
pub enum ParseError {
    InvalidNumber(String),
    UnexpectedToken(Token),

    EmptyParenthesis,
    UnmatchedParenthesis,

    OpenOp(Optype),
    ExpectedOp,
    DoubleOp(Optype,Optype),

    NoEnd,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::InvalidNumber(s) => write!(f, "Invalid number: {}", s),
            ParseError::UnexpectedToken(token) => {
                write!(f, "Unexpected token {:?}", token)
            }
            ParseError::EmptyParenthesis => write!(f, "( ) is not a valid expression"),
            ParseError::UnmatchedParenthesis => {
                write!(f, "Unmatched parenthesis")
            }

            ParseError::OpenOp(x) => write!(f, "expected to have ? {} ?",x),
            ParseError::ExpectedOp  => write!(f,"expected +-/* found value type instead"),
            ParseError::DoubleOp(a,b) => write!(f, "found {}{} expected to have ? [op] ?",a,b),

            ParseError::NoEnd => write!(f, "expected ;"),
        }
    }
}

impl Error for ParseError {}

enum ParExpr {
	Leaf(Token),
	Exp(Vec<ParExpr>),
}

fn gather_statement<R:Read>(lex : &mut Lexer<R>) -> Result<Option<Vec<ParExpr>>,LineParseErrors> {
	let mut stack : Vec<Vec<ParExpr>> = Vec::new();
	let mut errors = LineParseErrors::new();

	let mut ans :Vec<ParExpr> = Vec::new();

	while let Some(token) = lex.next() {
		match token {
			Token::Ender => {
				if errors.is_empty(){
					if stack.is_empty() {
						return Ok(Some(ans));
					}
					
					errors.push(LineParseError::new(ParseError::UnmatchedParenthesis,lex.line()));
					return Err(errors);
				}
				else {
					return Err(errors);
				}
			}

			Token::Comment(_) | Token::Line(_) => {}

			Token::OpenPar => {
				stack.push(Vec::new());
			}

			Token::ClosePar => {
				if stack.is_empty() {
					errors.push(LineParseError::new(ParseError::UnmatchedParenthesis,lex.line()));
					
					continue;
				}

				let exp = ParExpr::Exp(stack.pop().unwrap());
				
				if let Some(last) = stack.last_mut() {
			        last.push(exp);
			    } 
			    else {
			        ans.push(exp);
			    }
			}



			_ => {
				let exp = ParExpr::Leaf(token);
				
				if let Some(last) = stack.last_mut() {
			        last.push(exp);
			    } 
			    else {
			        ans.push(exp);
			    }
			}
		}
	} 

	if stack.is_empty() && ans.is_empty() && errors.is_empty() {
		//seen only comments
		return Ok(None);
	}

	errors.push(LineParseError::new(ParseError::NoEnd,lex.line()));
	Err(errors)
	
}


#[test]
fn test_gather_statement() {
    let input = "123 + 456; (789 * 10); junk ;";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    // Test first statement: "123 + 456;"
    let statement = gather_statement(&mut lexer).unwrap().unwrap();
    assert_eq!(statement.len(), 3);
    match &statement[0] {
        ParExpr::Leaf(Token::Num(n)) => assert_eq!(n, "123"),
        _ => panic!("Expected a number token"),
    }
    match &statement[1] {
        ParExpr::Leaf(Token::Plus) => {}
        _ => panic!("Expected a plus token"),
    }
    match &statement[2] {
        ParExpr::Leaf(Token::Num(n)) => assert_eq!(n, "456"),
        _ => panic!("Expected a number token"),
    }

    // Test second statement: "(789 * 10);"
    let statement = gather_statement(&mut lexer).unwrap().unwrap();
    assert_eq!(statement.len(), 1);
    match &statement[0] {
        ParExpr::Exp(expr) => {
            assert_eq!(expr.len(), 3);
            match &expr[0] {
                ParExpr::Leaf(Token::Num(n)) => assert_eq!(n, "789"),
                _ => panic!("Expected a number token"),
            }
            match &expr[1] {
                ParExpr::Leaf(Token::Mul) => {}
                _ => panic!("Expected a multiplication token"),
            }
            match &expr[2] {
                ParExpr::Leaf(Token::Num(n)) => assert_eq!(n, "10"),
                _ => panic!("Expected a number token"),
            }
        }
        _ => panic!("Expected an expression"),
    }

    // Test third statement: "junk ;"
    let statement = gather_statement(&mut lexer).unwrap().unwrap();
    assert_eq!(statement.len(), 1);
    match &statement[0] {
        ParExpr::Leaf(Token::Unknowen(unk)) => assert_eq!(unk, "junk"),
        _ => panic!("Expected an unknown token"),
    }
}

#[test]
fn test_gather_statement_nested_expression() {
    let input = "(((123 + 456) * 789) - 10);";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    // Test nested statement: "(((123 + 456) * 789) - 10);"
    let statement = gather_statement(&mut lexer).unwrap().unwrap();
    assert_eq!(statement.len(), 1);
    match &statement[0] {
        ParExpr::Exp(expr) => {
            assert_eq!(expr.len(), 3);
            match &expr[0] {
                ParExpr::Exp(inner_expr) => {
                    assert_eq!(inner_expr.len(), 3);
                    match &inner_expr[0] {
                        ParExpr::Exp(inner_inner_expr) => {
                            assert_eq!(inner_inner_expr.len(), 3);
                            match &inner_inner_expr[0] {
                                ParExpr::Leaf(Token::Num(n)) => assert_eq!(n, "123"),
                                _ => panic!("Expected a number token"),
                            }
                            match &inner_inner_expr[1] {
                                ParExpr::Leaf(Token::Plus) => {}
                                _ => panic!("Expected a plus token"),
                            }
                            match &inner_inner_expr[2] {
                                ParExpr::Leaf(Token::Num(n)) => assert_eq!(n, "456"),
                                _ => panic!("Expected a number token"),
                            }
                        }
                        _ => panic!("Expected an expression"),
                    }
                    match &inner_expr[1] {
                        ParExpr::Leaf(Token::Mul) => {}
                        _ => panic!("Expected a multiplication token"),
                    }
                    match &inner_expr[2] {
                        ParExpr::Leaf(Token::Num(n)) => assert_eq!(n, "789"),
                        _ => panic!("Expected a number token"),
                    }
                }
                _ => panic!("Expected an expression"),
            }
            match &expr[1] {
                ParExpr::Leaf(Token::Minus) => {}
                _ => panic!("Expected a minus token"),
            }
            match &expr[2] {
                ParExpr::Leaf(Token::Num(n)) => assert_eq!(n, "10"),
                _ => panic!("Expected a number token"),
            }
        }
        _ => panic!("Expected an expression"),
    }
}

#[test]
fn test_unmatched_parenthesis() {
    let input = "((123 + 456);";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    let result = gather_statement(&mut lexer);
    assert!(result.is_err());

    if let Err(LineParseErrors(errors)) = result {
        assert_eq!(errors.len(), 1);
        if let Some(error) = errors.get(0) {
            assert!(matches!(error.error, ParseError::UnmatchedParenthesis));
        }
    } else {
        panic!("Expected LineParseErrors, got different error type");
    }
}

#[test]
fn test_no_end() {
    let input = "123 + 456";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    let result = gather_statement(&mut lexer);
    assert!(result.is_err());

    if let Err(LineParseErrors(errors)) = result {
        assert_eq!(errors.len(), 1);
        if let Some(error) = errors.get(0) {
            assert!(matches!(error.error, ParseError::NoEnd));
        }
    } else {
        panic!("Expected LineParseErrors, got different error type");
    }
}




#[allow(dead_code)]
#[derive(Debug)]
pub enum Number {
    Float(f64),
    Int(i64),
}

fn translate_num(s: String) -> Result<Number, ParseError> {
    if s.contains('.') {
        f64::from_str(&s)
            .map(Number::Float)
            .map_err(|_e| ParseError::InvalidNumber(s))
    } else {
        i64::from_str(&s)
            .map(Number::Int)
            .map_err(|_e| ParseError::InvalidNumber(s))
    }
}

#[derive(Debug,PartialEq)]
pub enum Optype {
	Add,
	Sub,
	Mul,
	Div,
}

impl fmt::Display for Optype {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
	        match self {
	        	Optype::Add => write!(f,"+"),
	        	Optype::Sub => write!(f,"-"),
	        	Optype::Mul => write!(f,"*"),
	        	Optype::Div => write!(f,"/"),
	        }
	}
}

#[allow(dead_code)]
pub enum ArNode {
	Op(BinaryOp),
	Num(Number),
}

#[allow(dead_code)]
pub struct BinaryOp {
	left :Box<ArNode>,
	right: Box<ArNode>,
	action :Optype
}

#[allow(dead_code)]
pub fn next_statment<R:Read>(lex : &mut Lexer<R>) -> Result<Option<ArNode>,LineParseErrors> {
	let l=lex.line();
	let mut errors = LineParseErrors::new();

	match gather_statement(lex) {
		Ok(Some(x)) => {
			match _next_statment(x,l,&mut errors) {
				Ok(v) => Ok(Some(v)),
				Err(()) => Err(errors),
			}
		},  
		Ok(None) => Ok(None),
		Err(e) => Err(e),
	}
}

fn _next_statment(vec:Vec<ParExpr>,line: u32,errors: &mut LineParseErrors) ->  Result<ArNode,()> {
	let mut m = vec.into_iter().map(|x| recurse_map(x,line,errors));
	
	let mut cur = match m.next() {
		None => {
			errors.push(LineParseError::new(ParseError::EmptyParenthesis,line));
			return Err(());
		}
		Some(res) => match res {
			MapResult::Value(v) => v,
			MapResult::Err => {return Err(());},
			MapResult::Op(o) => {
				errors.push(LineParseError::new(
					ParseError::OpenOp(o),
					line)
				);
				return Err(());
			},
		}
	};

	while let Some(r) = m.next() {
		match r {
			MapResult::Err => {return Err(());},
			MapResult::Value(_) => {
				errors.push(LineParseError::new(
					ParseError::ExpectedOp,
					line)
				);
				return Err(());
			}
			MapResult::Op(op) => {
				let next=m.next();
				if next.is_none() {
					errors.push(LineParseError::new(
						ParseError::OpenOp(op),
						line)
					);
					return Err(());
				}

				let right = next.unwrap();
				match right {
					MapResult::Err => {return Err(())},
					MapResult::Value(v) => {
						cur = ArNode::Op(BinaryOp{
							action:op,
							left:Box::new(cur),
							right:Box::new(v)
						});
					},
					MapResult::Op(op2) => {
						errors.push(LineParseError::new(
							ParseError::DoubleOp(op,op2),
							line)
						);
						return Err(());
					}
				}
			}
		}
	}

	return Ok(cur);
}

enum MapResult {
	Value(ArNode),
	Op(Optype),
	Err
}

fn recurse_map(input :ParExpr,line: u32,errors: &mut LineParseErrors) -> MapResult {
	match input{
		ParExpr::Leaf(tok) => {
			match tok {
				Token::Num(s) => match translate_num(s) {
					Ok(n) => MapResult::Value(ArNode::Num(n)),
					Err(e) => {
						errors.push(LineParseError::new(e,line));
						MapResult::Err
					}
				},

				Token::Plus => MapResult::Op(Optype::Add),
				Token::Minus => MapResult::Op(Optype::Sub),
				Token::Mul => MapResult::Op(Optype::Mul),
				Token::Div => MapResult::Op(Optype::Div),

				other => {
					errors.push(
						LineParseError::new(
								ParseError::UnexpectedToken(other),
								line
						)
					);
					MapResult::Err
				},
			}
		},

		ParExpr::Exp(vec) => match _next_statment(vec,line,errors) {
			Ok(ar) => MapResult::Value(ar),
			Err(()) => MapResult::Err
		}
	}
}

#[test]
fn test_next_statment_simple_addition() {
    let input = "123 + 456;";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    let result = next_statment(&mut lexer).unwrap().unwrap();
    if let ArNode::Op(op) = result {
        match *op.left {
            ArNode::Num(Number::Int(n)) => assert_eq!(n, 123),
            _ => panic!("Expected left operand to be 123"),
        }
        assert_eq!(op.action, Optype::Add);
        match *op.right {
            ArNode::Num(Number::Int(n)) => assert_eq!(n, 456),
            _ => panic!("Expected right operand to be 456"),
        }
    } else {
        panic!("Expected an addition operation");
    }
}

#[test]
fn test_next_statment_nested_operations() {
    let input = "(123 + 456) * 789;";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    let result = next_statment(&mut lexer).unwrap().unwrap();
    if let ArNode::Op(op) = result {
        match *op.left {
            ArNode::Op(inner_op) => {
                match *inner_op.left {
                    ArNode::Num(Number::Int(n)) => assert_eq!(n, 123),
                    _ => panic!("Expected left operand to be 123"),
                }
                assert_eq!(inner_op.action, Optype::Add);
                match *inner_op.right {
                    ArNode::Num(Number::Int(n)) => assert_eq!(n, 456),
                    _ => panic!("Expected right operand to be 456"),
                }
            }
            _ => panic!("Expected an addition operation inside the multiplication"),
        }
        assert_eq!(op.action, Optype::Mul);
        match *op.right {
            ArNode::Num(Number::Int(n)) => assert_eq!(n, 789),
            _ => panic!("Expected right operand to be 789"),
        }
    } else {
        panic!("Expected a multiplication operation");
    }
}

#[test]
fn test_next_statment_missing_semicolon() {
    let input = "123 + 456";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    let result = next_statment(&mut lexer);
    assert!(result.is_err());

    if let Err(LineParseErrors(errors)) = result {
        assert_eq!(errors.len(), 1);
        if let Some(error) = errors.get(0) {
            assert!(matches!(error.error, ParseError::NoEnd));
        }
    } else {
        panic!("Expected LineParseErrors, got different error type");
    }
}

#[test]
fn test_next_statment_unmatched_parenthesis() {
    let input = "((123 + 456);";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    let result = next_statment(&mut lexer);
    assert!(result.is_err());

    if let Err(LineParseErrors(errors)) = result {
        assert_eq!(errors.len(), 1);
        if let Some(error) = errors.get(0) {
            assert!(matches!(error.error, ParseError::UnmatchedParenthesis));
        }
    } else {
        panic!("Expected LineParseErrors, got different error type");
    }
}

#[test]
fn test_deeply_nested_left() {
    let input = "(((((123 + 456) - 789) * 10) / 2) + 5";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    let result = next_statment(&mut lexer);
    assert!(result.is_err());

    if let Err(LineParseErrors(errors)) = result {
        assert_eq!(errors.len(), 1);
        if let Some(error) = errors.get(0) {
            assert!(matches!(error.error, ParseError::NoEnd));
        }
    } else {
        panic!("Expected LineParseErrors, got different error type");
    }
}

#[test]
fn test_deeply_nested_valid() {
    let input = "(((((123 + 456) - 789) * 10) / 2) + 5);";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    let result = next_statment(&mut lexer).unwrap().unwrap();

    if let ArNode::Op(op) = result {
        assert_eq!(op.action, Optype::Add);
        match *op.left {
            ArNode::Op(left_op) => {
                assert_eq!(left_op.action, Optype::Div);
                match *left_op.left {
                    ArNode::Op(mul_op) => {
                        assert_eq!(mul_op.action, Optype::Mul);
                        match *mul_op.left {
                            ArNode::Op(sub_op) => {
                                assert_eq!(sub_op.action, Optype::Sub);
                                match *sub_op.left {
                                    ArNode::Op(add_op) => {
                                        assert_eq!(add_op.action, Optype::Add);
                                        match *add_op.left {
                                            ArNode::Num(Number::Int(n)) => assert_eq!(n, 123),
                                            _ => panic!("Expected left operand to be 123"),
                                        }
                                        match *add_op.right {
                                            ArNode::Num(Number::Int(n)) => assert_eq!(n, 456),
                                            _ => panic!("Expected right operand to be 456"),
                                        }
                                    }
                                    _ => panic!("Expected an addition operation"),
                                }
                                match *sub_op.right {
                                    ArNode::Num(Number::Int(n)) => assert_eq!(n, 789),
                                    _ => panic!("Expected right operand to be 789"),
                                }
                            }
                            _ => panic!("Expected a subtraction operation"),
                        }
                        match *mul_op.right {
                            ArNode::Num(Number::Int(n)) => assert_eq!(n, 10),
                            _ => panic!("Expected right operand to be 10"),
                        }
                    }
                    _ => panic!("Expected a multiplication operation"),
                }
                match *left_op.right {
                    ArNode::Num(Number::Int(n)) => assert_eq!(n, 2),
                    _ => panic!("Expected right operand to be 2"),
                }
            }
            _ => panic!("Expected a division operation"),
        }
        match *op.right {
            ArNode::Num(Number::Int(n)) => assert_eq!(n, 5),
            _ => panic!("Expected right operand to be 5"),
        }
    } else {
        panic!("Expected an addition operation");
    }
}

#[test]
fn test_deeply_nested() {
    let input = "(((123 + 456) * (789 - 10)) / ((20 / 5) + (3 * 2)));";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    let result = next_statment(&mut lexer).unwrap().unwrap();

    if let ArNode::Op(op) = result {
        assert_eq!(op.action, Optype::Div);

        // Check the left side of the division
        match *op.left {
            ArNode::Op(mul_op) => {
                assert_eq!(mul_op.action, Optype::Mul);
                
                // Check the left side of the multiplication
                match *mul_op.left {
                    ArNode::Op(add_op) => {
                        assert_eq!(add_op.action, Optype::Add);
                        match *add_op.left {
                            ArNode::Num(Number::Int(n)) => assert_eq!(n, 123),
                            _ => panic!("Expected left operand to be 123"),
                        }
                        match *add_op.right {
                            ArNode::Num(Number::Int(n)) => assert_eq!(n, 456),
                            _ => panic!("Expected right operand to be 456"),
                        }
                    }
                    _ => panic!("Expected an addition operation"),
                }

                // Check the right side of the multiplication
                match *mul_op.right {
                    ArNode::Op(sub_op) => {
                        assert_eq!(sub_op.action, Optype::Sub);
                        match *sub_op.left {
                            ArNode::Num(Number::Int(n)) => assert_eq!(n, 789),
                            _ => panic!("Expected left operand to be 789"),
                        }
                        match *sub_op.right {
                            ArNode::Num(Number::Int(n)) => assert_eq!(n, 10),
                            _ => panic!("Expected right operand to be 10"),
                        }
                    }
                    _ => panic!("Expected a subtraction operation"),
                }
            }
            _ => panic!("Expected a multiplication operation"),
        }

        // Check the right side of the division
        match *op.right {
            ArNode::Op(add_op) => {
                assert_eq!(add_op.action, Optype::Add);
                
                // Check the left side of the addition
                match *add_op.left {
                    ArNode::Op(div_op) => {
                        assert_eq!(div_op.action, Optype::Div);
                        match *div_op.left {
                            ArNode::Num(Number::Int(n)) => assert_eq!(n, 20),
                            _ => panic!("Expected left operand to be 20"),
                        }
                        match *div_op.right {
                            ArNode::Num(Number::Int(n)) => assert_eq!(n, 5),
                            _ => panic!("Expected right operand to be 5"),
                        }
                    }
                    _ => panic!("Expected a division operation"),
                }

                // Check the right side of the addition
                match *add_op.right {
                    ArNode::Op(mul_op) => {
                        assert_eq!(mul_op.action, Optype::Mul);
                        match *mul_op.left {
                            ArNode::Num(Number::Int(n)) => assert_eq!(n, 3),
                            _ => panic!("Expected left operand to be 3"),
                        }
                        match *mul_op.right {
                            ArNode::Num(Number::Int(n)) => assert_eq!(n, 2),
                            _ => panic!("Expected right operand to be 2"),
                        }
                    }
                    _ => panic!("Expected a multiplication operation"),
                }
            }
            _ => panic!("Expected an addition operation"),
        }
    } else {
        panic!("Expected a division operation");
    }
}
