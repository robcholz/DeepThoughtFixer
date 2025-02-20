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

pub fn autocomplete_rules_available(
    a: Option<String>,
    b: Option<String>,
) -> Result<Vec<String>, String> {
    let mut result = autocomplete_rules_available_single(a.clone(), b.clone())?;
    let mut r = autocomplete_rules_available_single(b, a)?;
    result.append(&mut r);
    result.sort();
    result.dedup();
    Ok(result.iter().map(|ast| ast.to_string()).collect())
}

pub fn apply_the_rule(
    rule: Rule,
    a: Option<String>,
    b: Option<String>,
) -> Result<Vec<String>, String> {
    let mut result = apply_the_rule_single(rule, a.clone(), b.clone())?;
    let mut r = apply_the_rule_single(rule, b, a)?;
    result.append(&mut r);
    let mut result: Vec<_> = result.iter().map(|ast| ast.to_string()).collect();
    result.sort();
    result.dedup();
    Ok(result)
}

pub fn autocomplete_rules_available_single(
    a: Option<String>,
    b: Option<String>,
) -> Result<Vec<Rule>, String> {
    let mut result = vec![];
    // single node
    if (a.is_some() && b.is_none()) || (a.is_none() && b.is_some()) {
        let ast = get_ast(a, b)?;

        // DisjunctiveSyllogism
        if ast.is_and() && ast.left().unwrap().is_or() && ast.right().unwrap().is_not() {
            let not_expr = ast.right().unwrap();
            if ast.left().unwrap().left().unwrap() == not_expr.unary_node().unwrap() {
                result.push(Rule::DisjunctiveSyllogism);
            } else if ast.left().unwrap().right().unwrap() == not_expr.unary_node().unwrap() {
                result.push(Rule::DisjunctiveSyllogism);
            }
        }
        // Simplification
        if ast.is_and() {
            result.push(Rule::Simplification);
        }
        // ConstructiveDilemma
        if ast.is_and()
            && ast.left().unwrap().is_implication()
            && ast.right().unwrap().is_implication()
        {
            result.push(Rule::ConstructiveDilemma);
        }
        // DoubleNegation
        if ast.is_not() && ast.unary_node().unwrap().is_not() {
            result.push(Rule::DoubleNegation);
        }
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
        } else if ast.is_or() && ast.left().unwrap().is_not() {
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
        if ast.is_and() && ast.left().unwrap().is_and() {
            result.push(Rule::Associative);
        } else if ast.is_or() && ast.left().unwrap().is_or() {
            result.push(Rule::Associative);
        }
        // Distributive
        if ast.is_and() && ast.left().unwrap().is_or() {
            result.push(Rule::Distributive);
        } else if ast.is_or() && ast.left().unwrap().is_and() {
            result.push(Rule::Distributive);
        }
        // Contradiction
        if ast.is_and() {
            let left = ast.left().unwrap();
            let right = ast.right().unwrap();
            if left.is_not() && left.unary_node().unwrap() == right {
                result.push(Rule::Contradiction);
            }
        }
        // Tautology
        if ast.is_or() {
            let left = ast.left().unwrap();
            let right = ast.right().unwrap();
            if left.is_not() && left.unary_node().unwrap() == right {
                result.push(Rule::Tautology);
            }
        }

        return Ok(result);
    }
    let (l_expr, r_expr) = get_ast_pair(a.clone(), b.clone())?;
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

pub fn apply_the_rule_single(
    rule: Rule,
    a: Option<String>,
    b: Option<String>,
) -> Result<Vec<ASTNode>, String> {
    let available_rules = autocomplete_rules_available_single(a.clone(), b.clone())?;
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
            vec![ast.unary_node().unwrap().unary_node().unwrap().clone()]
        }
        Rule::DeMorgan => {
            let ast = get_ast(a, b)?;
            let left = ASTNode::construct_unary(Operator::Not, ast.left().unwrap().clone());
            let right = ASTNode::construct_unary(Operator::Not, ast.right().unwrap().clone());
            let mut operator = Operator::Or;
            // condition 1: NOT
            if ast.is_not()
                && (ast.unary_node().unwrap().is_or() || ast.unary_node().unwrap().is_and())
            {
                if ast.unary_node().unwrap().is_or() {
                    operator = Operator::And;
                }
                vec![ASTNode::construct_binary(operator, left, right)]
            }
            // condition 2: Extract
            else {
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
            vec![ASTNode::Value(BooleanValue::True)]
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
