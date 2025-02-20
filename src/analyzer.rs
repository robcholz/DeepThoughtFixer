use std::cmp::PartialEq;
use std::fmt;
use std::str::FromStr;

use crate::parser::{ASTNode, BooleanValue, Operator, Parser};
use crate::tokenizer::Tokenizer;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub enum Rule {
    ModusPonens,
    ModusTollens,
    DisjunctiveSyllogism,
    Addition,
    Simplification,
    Conjunction,
    HypotheticalSyllogism,
    ConstructiveDilemma,
    DoubleNegation,
    DeMorgan,
    ConditionalIdentity,
    Contrapositive,
    Equivalence,
    Commutative,
    Associative,
    Distributive,
    Contradiction,
    Tautology,
}

impl FromStr for Rule {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "ModusPonens" => Ok(Rule::ModusPonens),
            "ModusTollens" => Ok(Rule::ModusTollens),
            "DisjunctiveSyllogism" => Ok(Rule::DisjunctiveSyllogism),
            "Addition" => Ok(Rule::Addition),
            "Simplification" => Ok(Rule::Simplification),
            "Conjunction" => Ok(Rule::Conjunction),
            "HypotheticalSyllogism" => Ok(Rule::HypotheticalSyllogism),
            "ConstructiveDilemma" => Ok(Rule::ConstructiveDilemma),
            "DoubleNegation" => Ok(Rule::DoubleNegation),
            "DeMorgan" => Ok(Rule::DeMorgan),
            "ConditionalIdentity" => Ok(Rule::ConditionalIdentity),
            "Contrapositive" => Ok(Rule::Contrapositive),
            "Equivalence" => Ok(Rule::Equivalence),
            "Commutative" => Ok(Rule::Commutative),
            "Associative" => Ok(Rule::Associative),
            "Distributive" => Ok(Rule::Distributive),
            "Contradiction" => Ok(Rule::Contradiction),
            _ => Err(()),
        }
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Returns Ok with a vector representing the list of applicable rules in string.
/// Propositions should be either one or two, Err will be returned if two of the strings are missing.
/// If string(s) cannot neither be parsed nor have syntax errors, Err will be returned.
pub fn autocomplete_rules_available(
    a: Option<String>,
    b: Option<String>,
) -> Result<Vec<String>, String> {
    let mut result = autocomplete_rules_available_single(a.clone(), b.clone(), true)?;
    let mut r = autocomplete_rules_available_single(a, b, false)?;
    result.append(&mut r);
    result.sort();
    result.dedup();
    Ok(result.iter().map(|ast| ast.to_string()).collect())
}

/// Returns Ok with a vector representing the list of propositions with rules applied to the provided strings of propositions.
/// Propositions should be either one or two, Err will be returned if two of the strings are missing.
/// If string(s) cannot neither be parsed nor have syntax errors, Err will be returned.
/// If the given rule cannot be applied to the string(s), Err will be returned.
pub fn apply_the_rule(
    rule: Rule,
    a: Option<String>,
    b: Option<String>,
) -> Result<Vec<String>, String> {
    let mut result = vec![];
    let l = apply_the_rule_single(rule, a.clone(), b.clone(), true);
    let r = apply_the_rule_single(rule, a, b, false);
    if l.is_err() && r.is_err() {
        return Err(l.err().unwrap());
    }
    if l.is_ok() {
        result.append(&mut l.unwrap());
    }
    if r.is_ok() {
        result.append(&mut r.unwrap());
    }
    let mut result: Vec<_> = result.iter().map(|ast| ast.to_string()).collect();
    result.sort();
    result.dedup();
    Ok(result)
}

fn autocomplete_rules_available_single(
    a: Option<String>,
    b: Option<String>,
    order: bool,
) -> Result<Vec<Rule>, String> {
    let mut result = vec![];
    // single node
    if (a.is_some() && b.is_none()) || (a.is_none() && b.is_some()) {
        let ast = get_ast(a, b)?;
        let l_expr;
        let r_expr;
        if order {
            l_expr = ast.left();
            r_expr = ast.right();
        } else {
            r_expr = ast.left();
            l_expr = ast.right();
        }

        // DisjunctiveSyllogism
        if ast.is_and() && l_expr.unwrap().is_or() && r_expr.unwrap().is_not() {
            let not_expr = r_expr.unwrap();
            if l_expr.unwrap().left().unwrap() == not_expr.unary_node().unwrap() {
                result.push(Rule::DisjunctiveSyllogism);
            } else if l_expr.unwrap().right().unwrap() == not_expr.unary_node().unwrap() {
                result.push(Rule::DisjunctiveSyllogism);
            }
        }
        // Simplification
        if ast.is_and() {
            result.push(Rule::Simplification);
        }
        // ConstructiveDilemma
        if ast.is_and() && l_expr.unwrap().is_implication() && r_expr.unwrap().is_implication() {
            result.push(Rule::ConstructiveDilemma);
        }
        // DoubleNegation
        result.push(Rule::DoubleNegation);
        // DeMorgan
        if ast.is_not() && (ast.unary_node().unwrap().is_or() || ast.unary_node().unwrap().is_and())
        {
            result.push(Rule::DeMorgan);
        } else if ast.is_and() || ast.is_or() {
            result.push(Rule::DeMorgan);
        }
        // ConditionalIdentity
        if ast.is_implication() {
            result.push(Rule::ConditionalIdentity);
        } else if ast.is_or() && l_expr.unwrap().is_not() {
            result.push(Rule::ConditionalIdentity);
        }
        // Contrapositive
        if ast.is_implication() {
            result.push(Rule::Contrapositive);
        }
        // Equivalence
        if ast.is_equivalence() {
            result.push(Rule::Equivalence);
        }
        // Commutative
        if ast.is_and() || ast.is_or() {
            result.push(Rule::Commutative);
        }
        // Associative
        if ast.is_and() && l_expr.unwrap().is_and() {
            result.push(Rule::Associative);
        } else if ast.is_or() && l_expr.unwrap().is_or() {
            result.push(Rule::Associative);
        }
        // Distributive
        if ast.is_and() && l_expr.unwrap().is_or() {
            result.push(Rule::Distributive);
        } else if ast.is_or() && l_expr.unwrap().is_and() {
            result.push(Rule::Distributive);
        }
        // Contradiction
        if ast.is_and() {
            if l_expr.unwrap().is_not() && l_expr.unwrap().unary_node().unwrap() == r_expr.unwrap()
            {
                result.push(Rule::Contradiction);
            }
        }
        // Tautology
        result.push(Rule::Tautology);

        return Ok(result);
    }
    let (l_expr, r_expr);
    if order {
        (l_expr, r_expr) = get_ast_pair(a.clone(), b.clone())?;
    } else {
        (l_expr, r_expr) = get_ast_pair(b.clone(), a.clone())?;
    }
    // multi-node

    // ModusPonens
    if l_expr.is_implication() && l_expr.left().unwrap() == &r_expr {
        result.push(Rule::ModusPonens);
    }
    // ModusTollens
    if l_expr.is_implication()
        && r_expr.is_not()
        && r_expr.unary_node().unwrap() == l_expr.right().unwrap()
    {
        result.push(Rule::ModusTollens);
    }
    // Addition
    result.push(Rule::Addition);
    // Conjunction
    result.push(Rule::Conjunction);
    // HypotheticalSyllogism
    if l_expr.is_implication()
        && r_expr.is_implication()
        && l_expr.right().unwrap() == r_expr.left().unwrap()
    {
        result.push(Rule::HypotheticalSyllogism);
    }

    Ok(result)
}

fn apply_the_rule_single(
    rule: Rule,
    a: Option<String>,
    b: Option<String>,
    order: bool,
) -> Result<Vec<ASTNode>, String> {
    let available_rules = autocomplete_rules_available_single(a.clone(), b.clone(), order)?;
    if !available_rules.contains(&rule) {
        return Err(format!("Cannot apply rule: {}", rule));
    }
    let res: Vec<ASTNode> = match rule {
        Rule::ModusPonens => {
            let (a, _) = get_ast_pair(a, b)?;
            vec![a.right().unwrap().clone()]
        }
        Rule::ModusTollens => {
            let (a, _) = get_ast_pair(a, b)?;
            vec![ASTNode::construct_unary(
                Operator::Not,
                a.left().unwrap().clone(),
            )]
        }
        Rule::DisjunctiveSyllogism => {
            let ast = get_ast(a, b)?;
            let not_expr = ast.right().unwrap();
            if ast.left().unwrap().left().unwrap() == not_expr.unary_node().unwrap() {
                vec![ast.left().unwrap().right().unwrap().clone()]
            } else {
                vec![ast.left().unwrap().left().unwrap().clone()]
            }
        }
        Rule::Addition => {
            let (a, b) = get_ast_pair(a, b)?;
            vec![ASTNode::construct_binary(Operator::Or, a, b)]
        }
        Rule::Simplification => {
            let ast = get_ast(a, b)?;
            vec![ast.left().unwrap().clone(), ast.right().unwrap().clone()]
        }
        Rule::Conjunction => {
            let (a, b) = get_ast_pair(a, b)?;
            vec![ASTNode::construct_binary(Operator::And, a, b)]
        }
        Rule::HypotheticalSyllogism => {
            let (a, b) = get_ast_pair(a, b)?;
            vec![ASTNode::construct_binary(
                Operator::Implication,
                a.left().unwrap().clone(),
                b.right().unwrap().clone(),
            )]
        }
        Rule::ConstructiveDilemma => {
            let ast = get_ast(a, b)?;
            let left = ast.left().unwrap().left().unwrap();
            let right = ast.right().unwrap().left().unwrap();
            vec![ASTNode::construct_binary(
                Operator::Or,
                left.clone(),
                right.clone(),
            )]
        }
        Rule::DoubleNegation => {
            let ast = get_ast(a, b)?;
            // add !!
            if !ast.is_not() {
                vec![ASTNode::construct_unary(
                    Operator::Not,
                    ASTNode::construct_unary(Operator::Not, ast),
                )]
            }
            // remove !!
            else {
                let mut count = 0usize;
                let mut current = &ast;
                while current.is_not() {
                    current = current.unary_node().unwrap();
                    count += 1;
                }
                if count % 2 == 0 {
                    vec![current.clone()]
                } else {
                    vec![ASTNode::construct_unary(Operator::Not, current.clone())]
                }
            }
        }
        Rule::DeMorgan => {
            let ast = get_ast(a, b)?;
            let left;
            let right;
            let mut operator = Operator::Or;
            // condition 1: NOT
            if ast.is_not()
                && (ast.unary_node().unwrap().is_or() || ast.unary_node().unwrap().is_and())
            {
                left = ASTNode::construct_unary(
                    Operator::Not,
                    ast.unary_node().unwrap().left().unwrap().clone(),
                );
                right = ASTNode::construct_unary(
                    Operator::Not,
                    ast.unary_node().unwrap().right().unwrap().clone(),
                );
                if ast.unary_node().unwrap().is_or() {
                    operator = Operator::And;
                }
                vec![ASTNode::construct_binary(operator, left, right)]
            }
            // condition 2: Extract (AND)
            else {
                left = ASTNode::construct_unary(Operator::Not, ast.left().unwrap().clone());
                right = ASTNode::construct_unary(Operator::Not, ast.right().unwrap().clone());
                if ast.is_or() {
                    operator = Operator::And;
                }
                vec![ASTNode::construct_unary(
                    Operator::Not,
                    ASTNode::construct_binary(operator, left, right),
                )]
            }
        }
        Rule::ConditionalIdentity => {
            let ast = get_ast(a, b)?;
            let r = ast.right().unwrap();
            // p->q -p v q
            if ast.is_implication() {
                let l = &ASTNode::construct_unary(Operator::Not, ast.left().unwrap().clone());
                vec![ASTNode::construct_binary(
                    Operator::Or,
                    l.clone(),
                    r.clone(),
                )]
            }
            // -p v q p->q
            else {
                let l = &ASTNode::construct_unary(
                    Operator::Not,
                    ast.left().unwrap().unary_node().unwrap().clone(),
                );
                vec![ASTNode::construct_binary(
                    Operator::Implication,
                    l.clone(),
                    r.clone(),
                )]
            }
        }
        Rule::Contrapositive => {
            let ast = get_ast(a, b)?;
            let left = ASTNode::construct_unary(Operator::Not, ast.right().unwrap().clone());
            let right = ASTNode::construct_unary(Operator::Not, ast.left().unwrap().clone());
            vec![ASTNode::construct_binary(
                Operator::Implication,
                left,
                right,
            )]
        }
        Rule::Equivalence => {
            let ast = get_ast(a, b)?;
            let left = ast.left().unwrap();
            let right = ast.right().unwrap();
            vec![ASTNode::construct_binary(
                Operator::Implication,
                left.clone(),
                right.clone(),
            )]
        }
        Rule::Commutative => {
            let ast = get_ast(a, b)?;
            if ast.is_and() {
                vec![ASTNode::construct_binary(
                    Operator::And,
                    ast.right().unwrap().clone(),
                    ast.left().unwrap().clone(),
                )]
            }
            // or
            else {
                vec![ASTNode::construct_binary(
                    Operator::Or,
                    ast.right().unwrap().clone(),
                    ast.left().unwrap().clone(),
                )]
            }
        }
        Rule::Associative => {
            let ast = get_ast(a, b)?;
            let reorder_ast_left = |op: Operator, ast: &ASTNode| {
                ASTNode::construct_binary(
                    op,
                    ASTNode::construct_binary(
                        op,
                        ast.right().unwrap().clone(),
                        ast.left().unwrap().left().unwrap().clone(),
                    ),
                    ast.left().unwrap().right().unwrap().clone(),
                )
            };
            if ast.is_and() && ast.left().unwrap().is_and() {
                vec![reorder_ast_left(Operator::And, &ast)]
            }
            // or
            else {
                vec![reorder_ast_left(Operator::Or, &ast)]
            }
        }
        Rule::Distributive => {
            let ast = get_ast(a, b)?;
            // and
            if ast.is_and() && ast.left().unwrap().is_or() {
                let sub1 = ASTNode::construct_binary(
                    Operator::And,
                    ast.left().unwrap().left().unwrap().clone(),
                    ast.right().unwrap().clone(),
                );
                let sub2 = ASTNode::construct_binary(
                    Operator::And,
                    ast.left().unwrap().right().unwrap().clone(),
                    ast.right().unwrap().clone(),
                );
                vec![ASTNode::construct_binary(Operator::Or, sub1, sub2)]
            }
            // or
            else {
                let sub1 = ASTNode::construct_binary(
                    Operator::Or,
                    ast.left().unwrap().left().unwrap().clone(),
                    ast.right().unwrap().clone(),
                );
                let sub2 = ASTNode::construct_binary(
                    Operator::Or,
                    ast.left().unwrap().right().unwrap().clone(),
                    ast.right().unwrap().clone(),
                );
                vec![ASTNode::construct_binary(Operator::And, sub1, sub2)]
            }
        }
        Rule::Contradiction => {
            vec![ASTNode::Value(BooleanValue::False)]
        }
        Rule::Tautology => {
            let ast = get_ast(a, b)?;
            // optimize
            println!("{}", ast);
            if ast.is_or() {
                let l_expr;
                let r_expr;
                if order {
                    l_expr = ast.left().unwrap();
                    r_expr = ast.right().unwrap();
                } else {
                    l_expr = ast.right().unwrap();
                    r_expr = ast.left().unwrap();
                }
                if order && l_expr.is_not() && l_expr.unary_node().unwrap() == r_expr {
                    vec![ASTNode::Value(BooleanValue::True)]
                } else if !order && l_expr.is_not() && l_expr.unary_node().unwrap() == r_expr {
                    vec![ASTNode::Value(BooleanValue::True)]
                } else {
                    vec![
                        ASTNode::construct_binary(
                            Operator::And,
                            ast.clone(),
                            ASTNode::Value(BooleanValue::False),
                        ),
                        ASTNode::construct_binary(
                            Operator::Or,
                            ast,
                            ASTNode::Value(BooleanValue::True),
                        ),
                    ]
                }
            }
            // add booleans
            else {
                vec![
                    ASTNode::construct_binary(
                        Operator::And,
                        ast.clone(),
                        ASTNode::Value(BooleanValue::False),
                    ),
                    ASTNode::construct_binary(
                        Operator::Or,
                        ast,
                        ASTNode::Value(BooleanValue::True),
                    ),
                ]
            }
        }
    };
    Ok(res)
}

fn get_ast(a: Option<String>, b: Option<String>) -> Result<ASTNode, String> {
    if a.is_none() && b.is_none() {
        return Err("Expressions are missing!".to_string());
    }
    if a.is_some() && b.is_some() {
        return Err("Cannot have two expressions".to_string());
    }
    let str = if a.is_some() { a } else { b }.unwrap();
    Parser::new(Tokenizer::new(&str).tokenize()).parse_expression()
}

fn get_ast_pair(a: Option<String>, b: Option<String>) -> Result<(ASTNode, ASTNode), String> {
    if a.is_none() || b.is_none() {
        return Err("One of the expressions are missing!".to_string());
    }
    let a = a.unwrap();
    let b = b.unwrap();
    let mut parser_a = Parser::new(Tokenizer::new(&a).tokenize());
    let mut parser_b = Parser::new(Tokenizer::new(&b).tokenize());
    let a = parser_a.parse_expression();
    let b = parser_b.parse_expression();
    if a.is_err() {
        return Err(a.err().unwrap());
    }
    if b.is_err() {
        return Err(b.err().unwrap());
    }
    Ok((a.unwrap(), b.unwrap()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_autocomplete_rules_available_valid_single_input() {
        let input = Some("A".to_string());
        let result = autocomplete_rules_available(input, None);
        assert!(result.is_ok(), "Expected Ok result");
        assert!(
            !result.unwrap().is_empty(),
            "Expected non-empty vector of rules"
        );
    }

    #[test]
    fn test_autocomplete_rules_available_valid_two_inputs() {
        let result = autocomplete_rules_available(Some("A".to_string()), Some("B".to_string()));
        assert!(result.is_ok());
        assert!(
            !result.unwrap().is_empty(),
            "Expected non-empty vector of rules"
        );
    }

    #[test]
    fn test_autocomplete_rules_available_missing_inputs() {
        let result = autocomplete_rules_available(None, None);
        assert!(result.is_err(), "Expected Err result for missing inputs");
    }

    #[test]
    fn test_autocomplete_rules_available_invalid_syntax() {
        let result = autocomplete_rules_available(Some("invalid!".to_string()), None);
        assert!(result.is_ok(), "This is a valid syntax!");
    }

    #[test]
    fn test_apply_the_rule_modus_ponens_valid() {
        let rule = Rule::ModusPonens;
        let result = apply_the_rule(rule, Some("P -> Q".to_string()), Some("P".to_string()));
        assert!(result.is_ok(), "Expected Ok result for Modus Ponens");
        assert!(
            !result.unwrap().is_empty(),
            "Expected non-empty vector of results"
        );
    }

    #[test]
    fn test_apply_the_rule_modus_tollens_valid() {
        let rule = Rule::ModusTollens;
        let result = apply_the_rule(rule, Some("P -> Q".to_string()), Some("!Q".to_string()));
        assert!(result.is_ok(), "Expected Ok result for Modus Tollens");
        assert!(
            !result.unwrap().is_empty(),
            "Expected non-empty vector of results"
        );
    }

    #[test]
    fn test_apply_the_rule_invalid_syntax() {
        let rule = Rule::Addition;
        let result = apply_the_rule(rule, Some("invalid!".to_string()), None);
        assert!(result.is_err(), "Expected Err for invalid syntax");
    }

    #[test]
    fn test_apply_the_rule_missing_inputs() {
        let rule = Rule::Conjunction;
        let result = apply_the_rule(rule, None, None);
        assert!(result.is_err(), "Expected Err for missing inputs");
    }

    #[test]
    fn test_apply_the_rule_inapplicable_rule() {
        let rule = Rule::Distributive;
        let result = apply_the_rule(rule, Some("P -> Q".to_string()), Some("R".to_string()));
        assert!(result.is_err(), "Expected Err for an inapplicable rule");
    }

    #[test]
    fn test_apply_the_rule_double_negation() {
        let rule = Rule::DoubleNegation;
        let result = apply_the_rule(rule, Some("!!P".to_string()), None);
        assert!(result.is_ok(), "Expected Ok result for Double Negation");
        assert_eq!(
            result.unwrap(),
            vec!["P".to_string()],
            "Expected 'P' after applying Double Negation"
        );
    }

    #[test]
    fn test_apply_the_rule_demorgan() {
        let rule = Rule::DeMorgan;
        let result = apply_the_rule(rule, Some("!(P & Q)".to_string()), None);
        assert!(result.is_ok(), "Expected Ok result for DeMorgan's Law");
        assert_eq!(
            result.unwrap(),
            vec!["(!P | !Q)".to_string()],
            "Expected '(!P | !Q)' after applying DeMorgan's Law"
        );
    }

    #[test]
    fn test_apply_the_rule_contradiction() {
        let rule = Rule::Contradiction;
        let result = apply_the_rule(rule, Some("P & !P".to_string()), None);
        assert!(result.is_ok(), "Expected Ok result for Contradiction rule");
        assert_eq!(
            result.unwrap(),
            vec!["False".to_string()],
            "Expected 'False' after applying Contradiction rule"
        );
    }

    #[test]
    fn test_apply_the_rule_tautology() {
        let rule = Rule::Tautology;
        let result = apply_the_rule(rule, Some("P | !P".to_string()), None);
        assert!(result.is_ok(), "Expected Ok result for Tautology rule");
        assert!(
            result.unwrap().contains(&"True".to_string()),
            "Expected 'True' after applying Tautology rule"
        );
    }
}
