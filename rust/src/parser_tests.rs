
#[test]
fn test_parser() {
    assert!(lambdaterms::TermParser::new().parse(" \\Lambda x . x x").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda x . x x) (\Lambda x . x x)").is_ok());
    assert!(lambdaterms::TermParser::new().parse("y z").is_ok());
    assert!(lambdaterms::TermParser::new().parse("(y z) u").is_ok());
    assert!(lambdaterms::TermParser::new().parse("y z u").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda x . x x) w").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda x . x x) (w z)").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(y z) u (\Lambda x . x x)").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(y z) u (\Lambda x . x x) (\Lambda x . x x)").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"\Lambda x y . x y ").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda x y . x y) (\Lambda x . x x)").is_ok());


    assert!(lambdaterms::TermParser::new().parse("(λx y . x y) (λ x . x x)").is_ok());
    assert!(lambdaterms::TermParser::new().parse("(λ x y . x y) (λ x . x x)").is_ok());

    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda x y . x y) \Lambda x . x x").is_err());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda  . x y)").is_err());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda  . x y)").is_err());
}
