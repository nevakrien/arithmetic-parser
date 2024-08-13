use ::char_reader::CharReader;
use std::io::Read;


#[derive(Debug,PartialEq)]
pub enum Token{
	Unknowen(String),
	Comment(String),

	OpenPar,
	ClosePar,

	Plus,
	Minus,
	Div,
	Mul,
	Num(String),
	Ender,
	Line(u32),
}

pub struct Lexer<R :Read>{
	iter: CharReader<R>,
	cur_c :Option<char>,
	line_num : u32,
}

impl<R :Read> Lexer<R> {
	#[allow(dead_code)]
	pub fn new(input: R) -> Self {
        Lexer {
            iter: CharReader::new(input),
            cur_c: None,
            line_num: 0,
        }
    }

	pub fn line(&self) -> u32 {
		return self.line_num;
	}

	fn iter_char(&mut self) -> Option<char> {
	    match self.iter.next_char() {
	        Ok(Some('\n')) => {
	            self.line_num += 1;
	            Some('\n')
	        }
	        Ok(c) => c,
	        Err(e) => panic!("Error reading file {}", e),
	    }
	}

	fn collect_until<F>(&mut self, s: &mut String, stop_cond: F) -> Option<char>
    where
        F: Fn(char) -> bool,
    {
        while let Some(nc) = self.iter_char() {
            if stop_cond(nc) {
                self.cur_c = Some(nc);
                return Some(nc);
            } else {
                s.push(nc);
            }
        }
        None
    }
}




impl<R :Read> Iterator for Lexer<R> {
	type Item = Token;

	fn next(&mut self) -> Option<Self::Item>{
		let c = match self.cur_c.take(){
			Some(c) => c,
			None => self.iter_char()?,
			
		};
		match c {
			'\n' =>  {
				while let Some(nc) = self.iter_char() {
		            if !nc.is_whitespace() {
		                self.cur_c = Some(nc);
		                break;
		            }
		        }
				Some(Token::Line(self.line()))
			},
			c if c.is_whitespace() => self.next(),

			'+' => Some(Token::Plus),
            '-' => Some(Token::Minus),
            '/' => Some(Token::Div),
            '*' => Some(Token::Mul),
            ';' => Some(Token::Ender),
            '(' => Some(Token::OpenPar),
            ')' => Some(Token::ClosePar),
            
            '#' => {
		        let mut s = String::new();
		        self.collect_until(&mut s, |ch| ch == '\n');
		        Some(Token::Comment(s))
		    },
		    '0'..='9' => {
		        let mut s = String::new();
		        s.push(c);
		        self.collect_until(&mut s, |ch| !ch.is_numeric() && ch != '.');
		        Some(Token::Num(s))
		    },

			_  => {
		        let mut s = String::new();
		        s.push(c);
		        self.collect_until(&mut s, |ch| ch.is_whitespace());
		        Some(Token::Unknowen(s))
		    },
		}
	}
}



#[test]
fn test_lexer() {
    let input = "+ - / * ; # this is a comment\n  \n 123 jjunkkk 456.78 ()";
    let mut lexer = Lexer::new(std::io::Cursor::new(input));

    let tokens: Vec<Token> = lexer.by_ref().collect();

    assert_eq!(tokens.len(), 12);
    assert_eq!(tokens[0], Token::Plus);
    assert_eq!(tokens[1], Token::Minus);
    assert_eq!(tokens[2], Token::Div);
    assert_eq!(tokens[3], Token::Mul);
    assert_eq!(tokens[4], Token::Ender);
    assert_eq!(tokens[5], Token::Comment(" this is a comment".to_string()));
    assert_eq!(tokens[6], Token::Line(2));
    
    assert_eq!(tokens[7], Token::Num("123".to_string()));
    

    assert_eq!(tokens[8], Token::Unknowen("jjunkkk".to_string()));
    assert_eq!(tokens[9], Token::Num("456.78".to_string()));

     assert_eq!(tokens[10], Token::OpenPar);
     assert_eq!(tokens[11], Token::ClosePar);
}
