
lalrpop_mod!(pub lambdaterms); // synthesized by LALRPOP
lalrpop_mod!(pub alt_lambdaterms); // synthesized by LALRPOP

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

    assert!(lambdaterms::TermParser::new().parse(r"u (x u)").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"λ u . u (x u)").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(λ u . u (x u)) (λ v . v y)").is_ok());

    assert!(lambdaterms::TermParser::new().parse("(λx y . x y) (λ x . x x)").is_ok());
    assert!(lambdaterms::TermParser::new().parse("(λ x y . x y) (λ x . x x)").is_ok());

    assert!(lambdaterms::TermParser::new().parse(r"(λ t . t (λ n a x .  n (λ s z . a  (s (x s z)))) ( λ a . a) (λ z0 . z0) ) (λ s2 z2 . s2 (s2 z2))").is_ok());


    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda x y . x y) \Lambda x . x x").is_err());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda  . x y)").is_err());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda  . x y)").is_err());

}

#[test]
fn test_alternating_ast_parser() {
    assert!(alt_lambdaterms::TermParser::new().parse(r"\Lambda x . x").is_ok());
    assert!(alt_lambdaterms::TermParser::new().parse(r"\Lambda x . y").is_ok());
    assert!(alt_lambdaterms::TermParser::new().parse(r"(\Lambda x y . x y) \Lambda x . x x").is_err());
    assert!(alt_lambdaterms::TermParser::new().parse(r"(λ x y . x y) (λ x . x x)").is_ok());

    assert!(alt_lambdaterms::TermParser::new().parse(r"(t (λ n a x .  n (λ s z . a  (s (x s z))))) (λ a . a)").is_ok());
    assert!(alt_lambdaterms::TermParser::new().parse(r"(λ t . t (λ n a x .  n (λ s z . a  (s (x s z)))) (λ a . a)  )").is_ok());
    assert!(alt_lambdaterms::TermParser::new().parse(r"(λ t . t (λ n a x .  n (λ s z . a  (s (x s z)))) ( λ a . a) (λ z0 . z0) ) (λ s2 z2 . s2 (s2 z2))").is_ok());

}
