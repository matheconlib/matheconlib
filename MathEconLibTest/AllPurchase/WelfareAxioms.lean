import MathEconLibExamples.AllPurchase.Welfare

/-!
# Axiom checks for all-purchase welfare results

These checks are kept in a non-`module` test file because Lean does not allow `#print axioms`
inside a `module`. The default test target builds this file and records the results in CI.
-/

#print axioms MathEconLib.LinearScarcityAuction.welfare_decomposition
#print axioms MathEconLib.LinearScarcityAuction.editionWelfare_mean_sub_bundled_eq_variance
#print axioms MathEconLib.LinearScarcityAuction.cournotPurchaseLinear_best_response
#print axioms MathEconLib.LinearScarcityAuction.bundledEditionWelfare_le_firstBest
#print axioms MathEconLib.Examples.AllPurchase.Welfare.welfare_gap
