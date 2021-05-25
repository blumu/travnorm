import { neil, varityTwo, test_parsing } from "./parsing";
import { test_debruijn_ast_printing } from "./deBruijnAst";
import {
  setVerbosity, setVeryVerbosity, evaluate, Identifier_findBinder,
  test_enumerate_traversals, test_enumerate_no_resolution,
  test_ast_pretty_printing, test_name_preserving_evaluation} from "./travnorm";

test_parsing();
test_debruijn_ast_printing();
test_enumerate_traversals();
test_enumerate_no_resolution();
test_ast_pretty_printing(neil);
test_ast_pretty_printing(varityTwo);
test_name_preserving_evaluation();

console.log("===== Enumerating all traversals")
evaluate(Identifier_findBinder, neil)

setVerbosity(false);
setVeryVerbosity(false);
evaluate(Identifier_findBinder, varityTwo)