# DeepThoughtFixer

Fixed the trash NC State DeepThought grading system for [CSC226](https://www.csc.ncsu.edu/courses/outcomes.php?uniq_id=8000025).

Hopefully they will update their annoying system.

## Endpoints

This API provides endpoints for retrieving applicable logical rules and applying specific rules to given propositions.

### 1. Autocomplete Available Rules

**Endpoint:**  
`GET /autocomplete_rules_available`

Returns a list of applicable logical rules based on the given propositions.

**Request**

• left (optional): First proposition (string).

• right (optional): Second proposition (string).

```json
{
  "left": "P -> Q"
}
```

**Response**

• If valid propositions are provided, returns a list of applicable rules.

• If both propositions are missing, returns an error.

• If syntax errors exist in the propositions, returns an error.

```json
{
  "data": [
    "DoubleNegation",
    "ConditionalIdentity",
    "Contrapositive",
    "Tautology"
  ],
  "error": ""
}
```

### 2. Apply a rule

**Endpoint:**  
`GET /apply_the_rule`

Applies a given logical rule to one or two provided propositions and returns the resulting propositions.

**Request**

• rule (required): A valid logical rule from the predefined Rule set.

• left (optional): First proposition (string).

• right (optional): Second proposition (string).

```json
{
  "rule": "DeMorgan",
  "left": "!(P & Q)"
}
```

**Response**

• Returns the transformed propositions after applying the rule.

• If the rule cannot be applied to the given propositions, an error is returned.

• If invalid syntax or missing propositions are detected, an error is returned.

```json
{
  "data": [
    "(!P | !Q)"
  ],
  "error": ""
}
```