#[macro_use]
extern crate rocket;

use rocket::serde::json::Json;
use rocket::serde::Deserialize;
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

#[derive(Deserialize)]
struct QueryParams {
    left: Option<String>,
    right: Option<String>,
}

#[derive(Deserialize)]
struct RuleQueryParams {
    rule: String,
    left: Option<String>,
    right: Option<String>,
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

#[get("/")]
fn controller_landing() -> &'static str {
    "DeepThoughtFixer"
}

#[get("/autocomplete_rules_available", format = "json", data = "<params>")]
fn controller_autocomplete_rules_available(params: Json<QueryParams>) -> Json<CommonResult> {
    Json(CommonResult::new(analyzer::autocomplete_rules_available(
        params.left.clone(),
        params.right.clone(),
    )))
}

#[get("/apply_the_rule", format = "json", data = "<params>")]
fn controller_apply_the_rule(params: Json<RuleQueryParams>) -> Option<Json<CommonResult>> {
    if let Ok(parsed_rule) = params.rule.parse::<Rule>() {
        Some(Json(CommonResult::new(analyzer::apply_the_rule(
            parsed_rule,
            params.left.clone(),
            params.right.clone(),
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
            controller_apply_the_rule,
            controller_landing,
        ],
    )
}

#[cfg(test)]
mod test {
    use rocket::http::ContentType;
    use rocket::http::Status;
    use rocket::local::blocking::Client;

    use super::rocket;

    //noinspection RsUnresolvedPath
    #[test]
    fn landing() {
        let client = Client::tracked(rocket()).expect("valid rocket instance");
        let response = client.get(uri!(super::controller_landing)).dispatch();
        assert_eq!(response.status(), Status::Ok);
        assert_eq!(response.into_string().unwrap(), "DeepThoughtFixer");
    }

    //noinspection RsUnresolvedPath
    #[test]
    fn autocomplete_rules_available() {
        let client = Client::tracked(rocket()).expect("valid rocket instance");
        let json_data = r#"{"left": "P -> Q"}"#;

        let response = client
            .get(uri!(super::controller_autocomplete_rules_available))
            .header(ContentType::JSON)
            .body(json_data)
            .dispatch();

        assert_eq!(response.status(), Status::Ok);
        assert_eq!(
            response.into_string().unwrap(),
            r#"{"data":["DoubleNegation","ConditionalIdentity","Contrapositive","Tautology"],"error":""}"#
        );
    }

    //noinspection RsUnresolvedPath
    #[test]
    fn apply_the_rule() {
        let client = Client::tracked(rocket()).expect("valid rocket instance");
        let json_data = r#"{"rule": "DeMorgan", "left": "!(P & Q)"}"#;

        let response = client
            .get(uri!(super::controller_apply_the_rule))
            .header(ContentType::JSON)
            .body(json_data)
            .dispatch();

        assert_eq!(response.status(), Status::Ok);
        assert_eq!(
            response.into_string().unwrap(),
            r#"{"data":["(!P | !Q)"],"error":""}"#
        );
    }
}
