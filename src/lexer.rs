use ::char_reader::CharReader;
use std::io::Read;

#[derive(Debug,PartialEq)]
pub enum Token{
	Unknowen(String),
	Comment(String),
	Plus,
	Minus,
	Div,
	Mul,
	Num(String),
	Ender,
}

pub struct Lexer<R :Read>{
	iter: CharReader<R>,
	cur_c :Option<char>,
}

// pub impl<'a> Lexer<'a>{

// }

fn iter_char<R :Read>(lex :&mut Lexer<R>) -> Option<char>{
		match lex.iter.next_char() {
			Ok(x) => x,
			Err(e) => panic!("Error reading file {}", e),
		}
}

impl<R :Read> Iterator for Lexer<R> {
	type Item = Token;

	

	fn next(&mut self) -> Option<Self::Item>{
		let c = match self.cur_c.take(){
			Some(c) => c,
			None => iter_char(self)?,
			
		};
		match c {
			c if c.is_whitespace() => self.next(),

			'+' => Some(Token::Plus),
            '-' => Some(Token::Minus),
            '/' => Some(Token::Div),
            '*' => Some(Token::Mul),
            ';' => Some(Token::Ender),
            

            '#' => {
			    let mut s = String::new();
			    while let Some(nc) = iter_char(self) {
			        match nc {
			            '\n' => break,
			            c => s.push(c),
			        }
			    }
			    Some(Token::Comment(s))
			},
			'0'..='9' => {
			    let mut s = String::new();
			    s.push(c);
			    while let Some(nc) = iter_char(self) {
			        match nc {
			            '0'..='9' | '.' |',' => s.push(nc),
			            _ => {
			            	self.cur_c=Some(nc);
			            	break;
			            }
			        }
			    }
			    Some(Token::Num(s))
			},
			_ => todo!(),
		}
	}
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    use ::char_reader::CharReader;

    fn create_lexer(input: &str) -> Lexer<Cursor<&str>> {
        Lexer {
            iter: CharReader::new(Cursor::new(input)),
            cur_c: None,
        }
    }

    #[test]
    fn test_lexer() {
        let input = "+ - / * ; # this is a comment\n 123 456.78";
        let mut lexer = create_lexer(input);

        let tokens: Vec<Token> = lexer.by_ref().collect();

        assert_eq!(tokens.len(), 8);
        assert_eq!(tokens[0], Token::Plus);
        assert_eq!(tokens[1], Token::Minus);
        assert_eq!(tokens[2], Token::Div);
        assert_eq!(tokens[3], Token::Mul);
        assert_eq!(tokens[4], Token::Ender);
        assert_eq!(tokens[5], Token::Comment(" this is a comment".to_string()));
        assert_eq!(tokens[6], Token::Num("123".to_string()));
        assert_eq!(tokens[7], Token::Num("456.78".to_string()));
    }
}