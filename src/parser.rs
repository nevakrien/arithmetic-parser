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
    EmptyParenthesis,
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
            ParseError::EmptyParenthesis => write!(f, "( ) is not a valid expression"),
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

#[derive(Debug)]
pub enum Arith {
    Num(Number),
    Add(Box<Arith>, Box<Arith>),
    Sub(Box<Arith>, Box<Arith>),
    Mul(Box<Arith>, Box<Arith>),
    Div(Box<Arith>, Box<Arith>),
}

#[derive(Debug)]
enum BuildArith {
    Made(Arith),
    Num(Number),
    Add(Option<Box<BuildArith>>, Option<Box<BuildArith>>),
    Sub(Option<Box<BuildArith>>, Option<Box<BuildArith>>),
    Mul(Option<Box<BuildArith>>, Option<Box<BuildArith>>),
    Div(Option<Box<BuildArith>>, Option<Box<BuildArith>>),
}

impl fmt::Display for BuildArith {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BuildArith::Made(a) => todo!("add print for arith and put it here"),
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
        BuildArith::Made(a) => Ok(a),
        BuildArith::Num(n) => Ok(Arith::Num(n)),
        BuildArith::Add(mut a,mut b) => actualize_operation!(Add, a.take(), b.take()),
        BuildArith::Sub(mut a,mut b) => actualize_operation!(Sub, a.take(), b.take()),
        BuildArith::Mul(mut a,mut b) => actualize_operation!(Mul, a.take(), b.take()),
        BuildArith::Div(mut a,mut b) => actualize_operation!(Div, a.take(), b.take()),
    }
}

struct AST {
    states : Vec<Arith>,
}

fn is_binary_op(tok :&Token) -> bool{
	match tok {
		Token::Plus  => true,
        Token::Minus => true,
        Token::Mul => true,
        Token::Div => true,
        other => false
	}
}

fn is_binary_arith(tok :&Arith) -> bool{
	match tok {
		Arith::Num(_) =>false,
        other => true
	}
}


fn is_binary_build_arith(tok :&BuildArith) -> bool{
	match tok {
		BuildArith::Made(x)=>is_binary_arith(&x),
		BuildArith::Num(_) =>false,
        other => true
	}
}


struct ParserData<R: Read>{


    line: u32,
    par_count: u32,
    build_state: Option<Box<BuildArith>>,

    lex: Lexer<R>,
    next_token : Option<Token>,
}

impl<R: Read> ParserData<R>  {
    fn new(mut lex: Lexer<R>,) -> Self {
        let next_token=lex.next();
        
        ParserData {
            // storage: Vec::new(),
            line: 0,
            par_count: 0,
            build_state: None,

            lex :lex,
            next_token:next_token ,
        }
    }

	fn open_pair(&self) ->bool {
		match &self.next_token {
			None => false,
			Some(tok) => is_binary_op(tok),
		}
	}

	fn handle_add(&mut self,x:BuildArith ) -> Option<BuildArith> {
		match self.build_state.take(){
			None=> {
				if !is_binary_build_arith(&x) {
					return Some(x);
				}
				else {
					self.build_state=Some(Box::<BuildArith>::new(x));
					return None;
				}
			}

			Some(mut z) => {
				if !is_binary_build_arith(&z) || matches!(*z, BuildArith::Made(_)) {
					self.build_state=Some(Box::<BuildArith>::new(x));
					return Some(*z);
				}

				let mut cur = &mut z;
				
				loop {
				    match cur.as_mut() {
				        // If we encounter a completed arithmetic operation or a number, we can't go further.
				        // We should place x as the new build state and return the current `z`.
				        BuildArith::Made(_) | BuildArith::Num(_) => {
				            self.build_state = Some(Box::<BuildArith>::new(x));
				            return Some(*z);
				        },

				        // If we encounter an Add, continue moving to the right.
				        BuildArith::Add(_, Some(ref mut right)) => {
				            cur = right;
				        },

				        // If the right side of the Add is open, place x there and return None.
				        BuildArith::Add(_, ref mut right) => {
				            *right = Some(Box::new(x));
				            return None;
				        },

				        // If we encounter a Sub, continue moving to the right.
				        BuildArith::Sub(_, Some(ref mut right)) => {
				            cur = right;
				        },

				        // If the right side of the Sub is open, place x there and return None.
				        BuildArith::Sub(_, ref mut right) => {
				            *right = Some(Box::new(x));
				            return None;
				        },

				        // If we encounter a Mul, continue moving to the right.
				        BuildArith::Mul(_, Some(ref mut right)) => {
				            cur = right;
				        },

				        // If the right side of the Mul is open, place x there and return None.
				        BuildArith::Mul(_, ref mut right) => {
				            *right = Some(Box::new(x));
				            return None;
				        },

				        // If we encounter a Div, continue moving to the right.
				        BuildArith::Div(_, Some(ref mut right)) => {
				            cur = right;
				        },

				        // If the right side of the Div is open, place x there and return None.
				        BuildArith::Div(_, ref mut right) => {
				            *right = Some(Box::new(x));
				            return None;
				        },
				    }
				}

			}
		}
	}
}

impl<R: Read> Iterator for ParserData<R> {
	type Item = Token;

	fn next(&mut self) -> Option<Self::Item> {
		match self.next_token.take() {
			Some(tok) => {
				self.next_token = self.lex.next();
				Some(tok)
			},
			None => None
		}
		
	}
}

macro_rules! pair_op_handle{
	($op:ident,$data:expr) =>{
		{
        	todo!("handle the case where we have ANOTHER open pair");
            $data.build_state = Some(Box::new(BuildArith::$op(
                $data.build_state.take(),
                None,
            )));
        }
	}
}

//need to check if the next arith happens to be a binary operation

fn make_arith<R: Read>(data: &mut ParserData<R>) -> Result<Option<Arith>, Vec<LineParseError>> {
    let mut result = None;
    let mut errors = Vec::new();

    while let Some(token) = data.next() {
        match token {
            Token::Line(l) => data.line = l,
            Token::OpenPar => {
            	data.par_count += 1;

                let par_arith = make_arith(data);
                match par_arith {
                    Err(ers) => errors.extend(ers),
                    Ok(opa) => match opa {
                        None => errors.push(LineParseError {
                                    error: ParseError::EmptyParenthesis,
                                    line: data.line,
                                }),
                        Some(ari) => {todo!("actually handle this");},
                    } 

                };
            }, 
            Token::ClosePar => {
                if data.par_count == 0 {
                    errors.push(LineParseError {
                        error: ParseError::UnmatchedParenthesis,
                        line: data.line,
                    });
                    break;
                }
                data.par_count -= 1;
                break;
            }
            Token::Ender =>  break,
            Token::Comment(_) => continue,
            Token::Num(s) => {
            	//WRONG!!!!
                match translate_num(s) {
                    Ok(num) => {
                        let ar = data.handle_add(BuildArith::Num(num));
                        if ar.is_none() {
                        	continue;
                        }
                        match actualize_arith(ar.unwrap()) {
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
            Token::Plus => pair_op_handle!(Add,data),
            Token::Minus => pair_op_handle!(Sub,data),
            Token::Mul => pair_op_handle!(Mul,data),
            Token::Div => pair_op_handle!(Div,data),
            
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
        match result {
        	Some(_) => Ok(result),
        	None => {
        		let last = data.build_state.take().unwrap_or({
        			return Ok(None);
        		});

        		match actualize_arith(*last) {
        			Ok(arith) => Ok(Some(arith)),
                    Err(err) => {
                        errors.push(LineParseError {
                            error: err,
                            line: data.line,
                        });

                        return Err(errors);
                    }
        		}
        	}
        }
    } else {
        Err(errors)
    }
}


pub fn make_ast<R: Read>(mut lex: Lexer<R>) -> Result<AST, LineParseErrors> {
    let mut data = ParserData::new(lex);
    let mut ans = Vec::new();
    let mut errors = Vec::new();
    	
	loop {
        match make_arith(&mut data) {
            Ok(Some(arith)) => {ans.push(arith)},
            Ok(None) => break,
            Err(errs) => errors.extend(errs),
        }
    }

    if !errors.is_empty() {
        return Err(LineParseErrors(errors));
    }

    if ans.is_empty() {
        errors.push(LineParseError {
            error: ParseError::EmptyTree,
            line: data.line,
        });
        return Err(LineParseErrors(errors));
    }

    return Ok(AST{states: ans});
}