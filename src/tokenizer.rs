#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Not,
    And,
    Or,
    Implication,
    Equivalence,
    Identifier(String),
    LeftParen,
    RightParen,
}

pub struct Tokenizer {
    input: Vec<char>,
    pos: usize,
}

impl Tokenizer {
    pub fn new(input: &str) -> Self {
        Self {
            input: input.chars().collect(),
            pos: 0,
        }
    }

    fn next_token(&mut self) -> Option<Token> {
        while self.pos < self.input.len() {
            let ch = self.input[self.pos];

            match ch {
                ' ' => self.pos += 1,
                '(' => {
                    self.pos += 1;
                    return Some(Token::LeftParen);
                }
                ')' => {
                    self.pos += 1;
                    return Some(Token::RightParen);
                }
                '!' => {
                    self.pos += 1;
                    return Some(Token::Not);
                }
                '&' => {
                    self.pos += 1;
                    return Some(Token::And);
                }
                '|' => {
                    self.pos += 1;
                    return Some(Token::Or);
                }
                '-' => {
                    if self.pos + 1 < self.input.len() && self.input[self.pos + 1] == '>' {
                        self.pos += 2;
                        return Some(Token::Implication);
                    }
                }
                '<' => {
                    if self.pos + 2 < self.input.len()
                        && self.input[self.pos + 1] == '='
                        && self.input[self.pos + 2] == '>'
                    {
                        self.pos += 3;
                        return Some(Token::Equivalence);
                    }
                }
                _ if ch.is_alphabetic() => {
                    let start = self.pos;
                    while self.pos < self.input.len() && self.input[self.pos].is_alphanumeric() {
                        self.pos += 1;
                    }
                    return Some(Token::Identifier(
                        self.input[start..self.pos].iter().collect(),
                    ));
                }
                _ => panic!("Unexpected character: {}", ch),
            }
        }
        None
    }

    pub fn tokenize(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        while let Some(token) = self.next_token() {
            tokens.push(token);
        }
        tokens
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identifier() {
        let mut tokenizer = Tokenizer::new("A");
        let tokens = tokenizer.tokenize();
        assert_eq!(tokens, vec![Token::Identifier("A".to_string())]);
    }

    #[test]
    fn test_not_operator() {
        let mut tokenizer = Tokenizer::new("!A");
        let tokens = tokenizer.tokenize();
        assert_eq!(tokens, vec![Token::Not, Token::Identifier("A".to_string())]);
    }

    #[test]
    fn test_and_operator() {
        let mut tokenizer = Tokenizer::new("A & B");
        let tokens = tokenizer.tokenize();
        assert_eq!(
            tokens,
            vec![
                Token::Identifier("A".to_string()),
                Token::And,
                Token::Identifier("B".to_string()),
            ]
        );
    }

    #[test]
    fn test_or_operator() {
        let mut tokenizer = Tokenizer::new("A | B");
        let tokens = tokenizer.tokenize();
        assert_eq!(
            tokens,
            vec![
                Token::Identifier("A".to_string()),
                Token::Or,
                Token::Identifier("B".to_string()),
            ]
        );
    }

    #[test]
    fn test_implication_operator() {
        let mut tokenizer = Tokenizer::new("A -> B");
        let tokens = tokenizer.tokenize();
        assert_eq!(
            tokens,
            vec![
                Token::Identifier("A".to_string()),
                Token::Implication,
                Token::Identifier("B".to_string()),
            ]
        );
    }

    #[test]
    fn test_parentheses() {
        let mut tokenizer = Tokenizer::new("(A & B)");
        let tokens = tokenizer.tokenize();
        assert_eq!(
            tokens,
            vec![
                Token::LeftParen,
                Token::Identifier("A".to_string()),
                Token::And,
                Token::Identifier("B".to_string()),
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn test_complex_expression() {
        let mut tokenizer = Tokenizer::new("!(A & B) -> C | D");
        let tokens = tokenizer.tokenize();
        assert_eq!(
            tokens,
            vec![
                Token::Not,
                Token::LeftParen,
                Token::Identifier("A".to_string()),
                Token::And,
                Token::Identifier("B".to_string()),
                Token::RightParen,
                Token::Implication,
                Token::Identifier("C".to_string()),
                Token::Or,
                Token::Identifier("D".to_string()),
            ]
        );
    }

    #[test]
    fn test_whitespace_handling() {
        let mut tokenizer = Tokenizer::new(" A  ->  B ");
        let tokens = tokenizer.tokenize();
        assert_eq!(
            tokens,
            vec![
                Token::Identifier("A".to_string()),
                Token::Implication,
                Token::Identifier("B".to_string()),
            ]
        );
    }

    #[test]
    fn test_multiple_operators() {
        let mut tokenizer = Tokenizer::new("A & B | C -> D");
        let tokens = tokenizer.tokenize();
        assert_eq!(
            tokens,
            vec![
                Token::Identifier("A".to_string()),
                Token::And,
                Token::Identifier("B".to_string()),
                Token::Or,
                Token::Identifier("C".to_string()),
                Token::Implication,
                Token::Identifier("D".to_string()),
            ]
        );
    }
}
