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

    pub fn extend(&mut self, error: LineParseErrors) {
        self.0.extend(error.0);
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&LineParseError> {
        self.0.get(index)
    }
    
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

    NoEnd,

    Other(Box<dyn Error>),
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

            ParseError::NoEnd => write!(f, "expected ;"),

            ParseError::Other(err) => write!(f, "Other error: {}", err),
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

pub enum Optype {
	Add,
	Sub,
	Mul,
	Div,
}

pub enum ArNode {
	Op(BinaryOp),
	Num(Number),
}


pub struct BinaryOp {
	left :Box<ArNode>,
	right: Box<ArNode>,
	action :Optype
}

// fn is_value (x:ParExpr) -> bool {
// 	match x {
// 		ParExpr::Leaf(t) => match t {
// 			Token::Num(_) => true,
// 			_ => false,
// 		}
// 		ParExpr::Exp(_) => true,
// 	}
// }

#[allow(dead_code)]
pub fn next_statment<R:Read>(lex : &mut Lexer<R>) -> Result<Option<ArNode>,LineParseErrors> {
	let l=lex.line();

	match gather_statement(lex) {
		Ok(Some(mut x)) => {
			match _next_statment(x,l) {
				Ok(v) => Ok(Some(v)),
				Err(e) => Err(e),
			}
		},  
		Ok(None) => Ok(None),
		Err(e) => Err(e),
	}
}

fn swap_vec(mut x: Vec<ParExpr>, i: usize) -> ParExpr {
    let ans = std::mem::replace(&mut x[i], ParExpr::Leaf(Token::Ender));
    ans
}


fn _next_statment(x:Vec<ParExpr>,line: u32) -> Result<ArNode,LineParseErrors> {
	let mut errors = LineParseErrors::new();

	if x.is_empty() {
		errors.push(LineParseError::new(ParseError::EmptyParenthesis,line));
		return Err(errors);
	}


	let first = match swap_vec(x,0){
		ParExpr::Leaf(tok) => {
			match tok {
				Token::Num(s) => match translate_num(s) {
					Ok(n) => Ok(ArNode::Num(n)),
					Err(e) => Err(errors.push(LineParseError::new(e,line))),
				},
				other => Err(errors.push(
					LineParseError::new(
							ParseError::UnexpectedToken(other),
							line
					)
				)),
			}
		}
		ParExpr::Exp(vec) => match _next_statment(vec,line) {
			Ok(v) => Ok(v),
			Err(e) => Err(errors.extend(e))
		}
	};

	let mut cur :ArNode = match first {
		Err(()) => {return Err(errors);}
		Ok(v) => v
	};

	// for i in (1..x.len()).step_by(2) {
	// 	// match x[i] {
			
	// 	// }
	// }

	todo!()

}