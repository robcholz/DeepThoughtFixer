#[macro_use]
extern crate rocket;

use rocket::serde::json::Json;
use serde::Serialize;

use crate::analyzer::*;

mod analyzer;
mod parser;
mod tokenizer;

impl Serialize for Rule {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&format!("{:?}", self))
    }
}

#[derive(Serialize)]
struct CommonResult {
    data: Vec<String>,
    error: String,
}

impl CommonResult {
    fn new(param: Result<Vec<String>, String>) -> Self {
        match param {
            Ok(ok) => Self {
                data: ok,
                error: "".to_owned(),
            },
            Err(err) => Self {
                data: vec![],
                error: err,
            },
        }
    }
}

#[get("/autocomplete_rules_available?<a>&<b>")]
fn controller_autocomplete_rules_available(
    a: Option<String>,
    b: Option<String>,
) -> Json<CommonResult> {
    Json(CommonResult::new(analyzer::autocomplete_rules_available(
        a, b,
    )))
}

#[get("/apply_the_rule?<rule>&<a>&<b>")]
fn controller_apply_the_rule(
    rule: String,
    a: Option<String>,
    b: Option<String>,
) -> Option<Json<CommonResult>> {
    if let Ok(parsed_rule) = rule.parse::<Rule>() {
        Some(Json(CommonResult::new(analyzer::apply_the_rule(
            parsed_rule,
            a,
            b,
        ))))
    } else {
        None
    }
}

#[launch]
fn rocket() -> _ {
    rocket::build().mount(
        "/",
        routes![
            controller_autocomplete_rules_available,
            controller_apply_the_rule
        ],
    )
}
