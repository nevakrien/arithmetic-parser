use crate::lexer::Token;
use crate::lexer::Lexer;
use std::error::Error;
use std::fmt;
use std::io::Read;
use std::str::FromStr;
use std::vec::Vec;


#[derive(Debug)]
pub struct LineParseErrors(pub Vec<LineParseError>);

impl fmt::Display for LineParseErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for error in &self.0 {
            writeln!(f, "{}", error)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct LineParseError {
    pub error: ParseError,
    pub line: u32,
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
    UnexpectedEOF,
    UnmatchedParenthesis,
    PartialArith(BuildArith),

    EmptyTree,

    Other(Box<dyn Error>),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::InvalidNumber(s) => write!(f, "Invalid number: {}", s),
            ParseError::UnexpectedToken(token) => {
                write!(f, "Unexpected token {:?}", token)
            }
            ParseError::UnexpectedEOF => write!(f, "Unexpected end of file"),
            ParseError::UnmatchedParenthesis => {
                write!(f, "Unmatched parenthesis")
            }
            ParseError::PartialArith(build) => {
                write!(f, "Partial arithmetic expression: {}", build.show())
            }
            ParseError::EmptyTree => write!(f, "Found no AST..."),
            ParseError::Other(err) => write!(f, "Other error: {}", err),
        }
    }
}





impl Error for ParseError {}
impl Error for LineParseErrors {}

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

pub enum Arith {
    Num(Number),
    Add(Box<Arith>, Box<Arith>),
    Sub(Box<Arith>, Box<Arith>),
    Mul(Box<Arith>, Box<Arith>),
    Div(Box<Arith>, Box<Arith>),
}

#[derive(Debug)]
enum BuildArith {
    Num(Number),
    Add(Option<Box<BuildArith>>, Option<Box<BuildArith>>),
    Sub(Option<Box<BuildArith>>, Option<Box<BuildArith>>),
    Mul(Option<Box<BuildArith>>, Option<Box<BuildArith>>),
    Div(Option<Box<BuildArith>>, Option<Box<BuildArith>>),
}

impl fmt::Display for BuildArith {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BuildArith::Num(n) => write!(f, "Number: {:?}", n),
            BuildArith::Add(a, b) => write!(f, "Addition: {}, {}", a.as_ref().map(|x| x.show()).unwrap_or("[MISSING]".to_string()), b.as_ref().map(|x| x.show()).unwrap_or("[MISSING]".to_string())),
            BuildArith::Sub(a, b) => write!(f, "Subtraction: {}, {}", a.as_ref().map(|x| x.show()).unwrap_or("[MISSING]".to_string()), b.as_ref().map(|x| x.show()).unwrap_or("[MISSING]".to_string())),
            BuildArith::Mul(a, b) => write!(f, "Multiplication: {}, {}", a.as_ref().map(|x| x.show()).unwrap_or("[MISSING]".to_string()), b.as_ref().map(|x| x.show()).unwrap_or("[MISSING]".to_string())),
            BuildArith::Div(a, b) => write!(f, "Division: {}, {}", a.as_ref().map(|x| x.show()).unwrap_or("[MISSING]".to_string()), b.as_ref().map(|x| x.show()).unwrap_or("[MISSING]".to_string())),
        }
    }
}

impl BuildArith {
    fn show(&self) -> String {
        format!("{}", self)
    }
}

macro_rules! actualize_operation {
    ($variant:ident, $a:expr, $b:expr) => {
        match ($a, $b) {
            (Some(a), Some(b)) => {
                Ok(Arith::$variant(
                    Box::new(actualize_arith(*a)?),
                    Box::new(actualize_arith(*b)?),
                ))
            }
            _ => {
                let partial = BuildArith::$variant($a, $b);
                Err(ParseError::PartialArith(partial))
            }
        }
    };
}


fn actualize_arith(build: BuildArith) -> Result<Arith, ParseError> {
    match build {
        BuildArith::Num(n) => Ok(Arith::Num(n)),
        BuildArith::Add(mut a,mut b) => actualize_operation!(Add, a.take(), b.take()),
        BuildArith::Sub(mut a,mut b) => actualize_operation!(Sub, a.take(), b.take()),
        BuildArith::Mul(mut a,mut b) => actualize_operation!(Mul, a.take(), b.take()),
        BuildArith::Div(mut a,mut b) => actualize_operation!(Div, a.take(), b.take()),
    }
}



pub enum AST {
    Statement(Arith, Option<Box<AST>>),
}

struct ParserData<'a> {
    root: Option<Box<AST>>,
    cur_statement: Option<&'a mut Option<Box<AST>>>, //unsafe when root is non (automatic reset in pop)
    line: u32,
    par_count: u32,
    build_state: Option<Box<BuildArith>>,
}

impl<'a> ParserData<'a>  {
    fn new() -> Self {
        ParserData {
            root: None,
            cur_statement: None,
            line: 0,
            par_count: 0,
            build_state: None,
        }
    }

    fn append(&mut self,x:Arith ) {
    	let new_node = Box::new(AST::Statement(x, None));

    	match self.cur_statement.as_mut() {
    		Some(n) => {
    			assert!(n.is_none());
    			**n=Some(new_node);
    		}

    		None => {
    			assert!(self.root.is_none());
	    		self.root=Some(new_node);
	    		
	    		unsafe{
	    			//getting around the 'a  lifetime requirment
	    			let p = (&mut self.root) as *mut Option<Box<AST>>;
	    			self.cur_statement=Some(&mut *p);
    			}
	    	}
	    		
    	}
        let next = {
        	let first_mut_ref = self.cur_statement.take().unwrap().as_mut().unwrap();
        	let AST::Statement(_, ref mut next) = **first_mut_ref;
        	next

        };

        self.cur_statement = Some(next);
    	
	}

	fn pop(&mut self) -> Option<Arith> {
		match self.root.take() {
			None => None, 

			Some(mut x) =>{
				let AST::Statement(ans, ref mut next) = *x;
				match next.take() {
					None => {
						self.root=None;
						self.cur_statement=None;
					},
					Some(s) =>
						self.root=Some(s),
				};
				Some(ans)
			}
		}
	}
}

fn make_arith<R: Read>(lex: &mut Lexer<R>, data: &mut ParserData) -> Result<Option<Arith>, Vec<LineParseError>> {
    let mut result = None;
    let mut errors = Vec::new();

    while let Some(token) = lex.next() {
        match token {
            Token::Line(l) => data.line = l,
            Token::OpenPar => data.par_count += 1,
            Token::ClosePar => {
                if data.par_count == 0 {
                    errors.push(LineParseError {
                        error: ParseError::UnmatchedParenthesis,
                        line: data.line,
                    });
                    break;
                }
                data.par_count -= 1;
            }
            Token::Ender => break,
            Token::Comment(_) => continue,
            Token::Num(s) => {
                match translate_num(s) {
                    Ok(num) => {
                        data.build_state = Some(Box::new(BuildArith::Num(num)));
                        match actualize_arith(*data.build_state.take().unwrap()) {
                            Ok(arith) => result = Some(arith),
                            Err(err) => {
                                errors.push(LineParseError {
                                    error: err,
                                    line: data.line,
                                });
                            }
                        }
                    }
                    Err(e) => {
                        errors.push(LineParseError {
                            error: e,
                            line: data.line,
                        });
                    }
                }
            }
            Token::Plus => {
                data.build_state = Some(Box::new(BuildArith::Add(
                    data.build_state.take(),
                    None,
                )));
            }
            Token::Minus => {
                data.build_state = Some(Box::new(BuildArith::Sub(
                    data.build_state.take(),
                    None,
                )));
            }
            Token::Mul => {
                data.build_state = Some(Box::new(BuildArith::Mul(
                    data.build_state.take(),
                    None,
                )));
            }
            Token::Div => {
                data.build_state = Some(Box::new(BuildArith::Div(
                    data.build_state.take(),
                    None,
                )));
            }
            other => {
                errors.push(LineParseError {
                    error: ParseError::UnexpectedToken(other),
                    line: data.line,
                });
            }
        }
    }

    if data.par_count > 0 {
        errors.push(LineParseError {
            error: ParseError::UnmatchedParenthesis,
            line: data.line,
        });
    }

    if errors.is_empty() {
        Ok(result)
    } else {
        Err(errors)
    }
}


pub fn make_ast<R: Read>(mut lex: Lexer<R>) -> Result<AST, LineParseErrors> {
    let mut data = ParserData::new();
    let mut errors = Vec::new();

    	
	loop {
        match make_arith(&mut lex, &mut data) {
            Ok(Some(arith)) => {data.append(arith)},
            Ok(None) => break,
            Err(errs) => errors.extend(errs),
        }
    }
    
    

    if !errors.is_empty() {
        return Err(LineParseErrors(errors));
    }

    if let Some(root) = data.root {
        Ok(*root)
    } else {
        errors.push(LineParseError {
            error: ParseError::EmptyTree,
            line: data.line,
        });
        Err(LineParseErrors(errors))
    }
}