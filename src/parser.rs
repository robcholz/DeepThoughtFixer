use std::cmp::PartialEq;
use std::fmt;
use std::fmt::Display;

use crate::tokenizer::Token;

#[derive(Clone, Debug, PartialEq, Copy)]
pub enum Operator {
    Not,
    And,
    Or,
    Implication,
    Equivalence,
}

#[derive(Clone, Debug)]
pub enum BooleanValue {
    True,
    False,
}

#[derive(Debug, Clone)]
pub enum ASTNode {
    UnaryOp {
        op: Operator,
        expr: Box<ASTNode>,
    },
    BinaryOp {
        op: Operator,
        left: Box<ASTNode>,
        right: Box<ASTNode>,
    },
    Identifier(String),
    Value(BooleanValue),
}

impl Display for BooleanValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let val = match self {
            BooleanValue::True => "True",
            BooleanValue::False => "False",
        };
        write!(f, "{}", val)
    }
}

impl Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op_str = match self {
            Operator::Not => "!",
            Operator::And => "&",
            Operator::Or => "|",
            Operator::Implication => "->",
            Operator::Equivalence => "<->",
        };
        write!(f, "{}", op_str)
    }
}

impl Display for ASTNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ASTNode::UnaryOp { op, expr } => {
                write!(f, "{}{}", op, expr)
            }
            ASTNode::BinaryOp { op, left, right } => {
                write!(f, "({} {} {})", left, op, right)
            }
            ASTNode::Identifier(id) => {
                write!(f, "{}", id)
            }
            ASTNode::Value(val) => {
                write!(f, "{}", val)
            }
        }
    }
}

impl PartialEq for ASTNode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                ASTNode::UnaryOp {
                    op: op1,
                    expr: expr1,
                },
                ASTNode::UnaryOp {
                    op: op2,
                    expr: expr2,
                },
            ) => op1 == op2 && expr1 == expr2,
            (
                ASTNode::BinaryOp {
                    op: op1,
                    left: left1,
                    right: right1,
                },
                ASTNode::BinaryOp {
                    op: op2,
                    left: left2,
                    right: right2,
                },
            ) => op1 == op2 && left1 == left2 && right1 == right2,
            (ASTNode::Identifier(id1), ASTNode::Identifier(id2)) => id1 == id2,
            _ => false,
        }
    }
}

impl ASTNode {
    pub fn construct_unary(new: Operator, node: ASTNode) -> ASTNode {
        match new {
            Operator::Not => {
                return ASTNode::UnaryOp {
                    op: new,
                    expr: Box::new(node),
                };
            }
            _ => {
                panic!("Only accept Unary here!");
            }
        }
    }

    pub fn construct_binary(new: Operator, left: ASTNode, right: ASTNode) -> ASTNode {
        match new {
            Operator::Not => {
                panic!("Only accept BinaryOp here!");
            }
            _ => {
                return ASTNode::BinaryOp {
                    op: new,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            }
        }
    }

    #[allow(dead_code)]
    pub fn is_unary(&self) -> bool {
        matches!(self, ASTNode::UnaryOp { .. })
    }

    #[allow(dead_code)]
    pub fn is_binary(&self) -> bool {
        matches!(self, ASTNode::BinaryOp { .. })
    }

    #[allow(dead_code)]
    pub fn is_identifier(&self) -> bool {
        matches!(self, ASTNode::Identifier(_))
    }

    pub fn is_not(&self) -> bool {
        matches!(
            self,
            ASTNode::UnaryOp {
                op: Operator::Not,
                ..
            }
        )
    }

    pub fn is_and(&self) -> bool {
        matches!(
            self,
            ASTNode::BinaryOp {
                op: Operator::And,
                ..
            }
        )
    }

    pub fn is_or(&self) -> bool {
        matches!(
            self,
            ASTNode::BinaryOp {
                op: Operator::Or,
                ..
            }
        )
    }

    pub fn is_implication(&self) -> bool {
        matches!(
            self,
            ASTNode::BinaryOp {
                op: Operator::Implication,
                ..
            }
        )
    }

    pub fn is_equivalence(&self) -> bool {
        matches!(
            self,
            ASTNode::BinaryOp {
                op: Operator::Equivalence,
                ..
            }
        )
    }

    pub fn unary_node(&self) -> Option<&ASTNode> {
        if let ASTNode::UnaryOp { expr, .. } = self {
            Some(expr)
        } else {
            None
        }
    }

    pub fn right(&self) -> Option<&ASTNode> {
        if let ASTNode::BinaryOp { right, .. } = self {
            Some(right)
        } else {
            None
        }
    }

    pub fn left(&self) -> Option<&ASTNode> {
        if let ASTNode::BinaryOp { left, .. } = self {
            Some(left)
        } else {
            None
        }
    }
}

pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    pub(crate) fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0 }
    }

    fn current_token(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn advance(&mut self) {
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
    }

    pub fn parse_expression(&mut self) -> Result<ASTNode, String> {
        self.parse_implication()
    }

    fn parse_implication(&mut self) -> Result<ASTNode, String> {
        let mut left = self.parse_equivalence()?;

        while let Some(Token::Implication) = self.current_token() {
            self.advance();
            let right = self.parse_equivalence()?;
            left = ASTNode::BinaryOp {
                op: Operator::Implication,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_equivalence(&mut self) -> Result<ASTNode, String> {
        let mut left = self.parse_or()?;

        while let Some(Token::Equivalence) = self.current_token() {
            self.advance();
            let right = self.parse_or()?;
            left = ASTNode::BinaryOp {
                op: Operator::Equivalence,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_or(&mut self) -> Result<ASTNode, String> {
        let mut left = self.parse_and()?;

        while let Some(Token::Or) = self.current_token() {
            self.advance();
            let right = self.parse_and()?;
            left = ASTNode::BinaryOp {
                op: Operator::Or,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<ASTNode, String> {
        let mut left = self.parse_unary()?;

        while let Some(Token::And) = self.current_token() {
            self.advance();
            let right = self.parse_unary()?;
            left = ASTNode::BinaryOp {
                op: Operator::And,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<ASTNode, String> {
        if let Some(Token::Not) = self.current_token() {
            self.advance();
            let expr = self.parse_unary()?;
            return Ok(ASTNode::UnaryOp {
                op: Operator::Not,
                expr: Box::new(expr),
            });
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Result<ASTNode, String> {
        match self.current_token() {
            Some(Token::Identifier(name)) => {
                let name = name.clone();
                self.advance();
                Ok(ASTNode::Identifier(name))
            }
            Some(Token::LeftParen) => {
                self.advance();
                let expr = self.parse_expression()?;
                if let Some(Token::RightParen) = self.current_token() {
                    self.advance();
                    Ok(expr)
                } else {
                    Err("Expected closing parenthesis".to_string())
                }
            }
            _ => Err("Unexpected token".to_string()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_equivalence_operator() {
        let tokens = vec![
            Token::Identifier("A".to_string()),
            Token::Equivalence,
            Token::Identifier("B".to_string()),
        ];
        let mut parser = Parser::new(tokens);
        let ast = parser.parse_expression().unwrap();

        let expected_ast = ASTNode::BinaryOp {
            op: Operator::Equivalence,
            left: Box::new(ASTNode::Identifier("A".to_string())),
            right: Box::new(ASTNode::Identifier("B".to_string())),
        };

        assert_eq!(ast, expected_ast);
    }

    #[test]
    fn test_and_or_precedence() {
        let tokens = vec![
            Token::Identifier("A".to_string()),
            Token::And,
            Token::Identifier("B".to_string()),
            Token::Or,
            Token::Identifier("C".to_string()),
        ];
        let mut parser = Parser::new(tokens);
        let ast = parser.parse_expression().unwrap();

        let expected_ast = ASTNode::BinaryOp {
            op: Operator::Or,
            left: Box::new(ASTNode::BinaryOp {
                op: Operator::And,
                left: Box::new(ASTNode::Identifier("A".to_string())),
                right: Box::new(ASTNode::Identifier("B".to_string())),
            }),
            right: Box::new(ASTNode::Identifier("C".to_string())),
        };

        assert_eq!(ast, expected_ast);
    }

    #[test]
    fn test_unary_not_operator() {
        let tokens = vec![Token::Not, Token::Identifier("A".to_string())];
        let mut parser = Parser::new(tokens);
        let ast = parser.parse_expression().unwrap();

        let expected_ast = ASTNode::UnaryOp {
            op: Operator::Not,
            expr: Box::new(ASTNode::Identifier("A".to_string())),
        };

        assert_eq!(ast, expected_ast);
    }

    #[test]
    fn test_implication_or_precedence() {
        let tokens = vec![
            Token::Identifier("A".to_string()),
            Token::Implication,
            Token::Identifier("B".to_string()),
            Token::Or,
            Token::Identifier("C".to_string()),
        ];
        let mut parser = Parser::new(tokens);
        let ast = parser.parse_expression().unwrap();

        let expected_ast = ASTNode::BinaryOp {
            op: Operator::Implication,
            left: Box::new(ASTNode::Identifier("A".to_string())),
            right: Box::new(ASTNode::BinaryOp {
                op: Operator::Or,
                left: Box::new(ASTNode::Identifier("B".to_string())),
                right: Box::new(ASTNode::Identifier("C".to_string())),
            }),
        };

        assert_eq!(ast, expected_ast);
    }

    #[test]
    fn test_parentheses_handling() {
        let tokens = vec![
            Token::LeftParen,
            Token::Identifier("A".to_string()),
            Token::And,
            Token::Identifier("B".to_string()),
            Token::RightParen,
            Token::Or,
            Token::Identifier("C".to_string()),
        ];
        let mut parser = Parser::new(tokens);
        let ast = parser.parse_expression().unwrap();

        let expected_ast = ASTNode::BinaryOp {
            op: Operator::Or,
            left: Box::new(ASTNode::BinaryOp {
                op: Operator::And,
                left: Box::new(ASTNode::Identifier("A".to_string())),
                right: Box::new(ASTNode::Identifier("B".to_string())),
            }),
            right: Box::new(ASTNode::Identifier("C".to_string())),
        };

        assert_eq!(ast, expected_ast);
    }

    #[test]
    fn test_complex_mixed_operators() {
        let tokens = vec![
            Token::Not,
            Token::Identifier("A".to_string()),
            Token::And,
            Token::Identifier("B".to_string()),
            Token::Or,
            Token::Identifier("C".to_string()),
            Token::Implication,
            Token::Identifier("D".to_string()),
        ];
        let mut parser = Parser::new(tokens);
        let ast = parser.parse_expression().unwrap();

        let expected_ast = ASTNode::BinaryOp {
            op: Operator::Implication,
            left: Box::new(ASTNode::BinaryOp {
                op: Operator::Or,
                left: Box::new(ASTNode::BinaryOp {
                    op: Operator::And,
                    left: Box::new(ASTNode::UnaryOp {
                        op: Operator::Not,
                        expr: Box::new(ASTNode::Identifier("A".to_string())),
                    }),
                    right: Box::new(ASTNode::Identifier("B".to_string())),
                }),
                right: Box::new(ASTNode::Identifier("C".to_string())),
            }),
            right: Box::new(ASTNode::Identifier("D".to_string())),
        };

        assert_eq!(ast, expected_ast);
    }

    #[test]
    fn test_empty_input() {
        let tokens = vec![];
        let mut parser = Parser::new(tokens);
        let result = parser.parse_expression();
        assert_eq!(result, Err("Unexpected token".to_string()));
    }
}
