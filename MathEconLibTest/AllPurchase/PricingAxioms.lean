import MathEconLibExamples.AllPurchase.UniformTwoBidder

/-!
# Axiom checks for all-purchase pricing and prize-aware welfare results

These checks are kept in a non-`module` test file because Lean does not allow `#print axioms`
inside a `module`. The default test target builds this file and records the results in CI.
-/

#print axioms MathEconLib.LinearScarcityAuction.bundledProfit_eq_sellerProfitInterior
#print axioms MathEconLib.LinearScarcityAuction.bundledProfit_le_interior_optimum
#print axioms MathEconLib.Examples.AllPurchase.UniformTwoBidder.bundledProfit_eq
#print axioms MathEconLib.Examples.AllPurchase.UniformTwoBidder.universalIC
#print axioms MathEconLib.Examples.AllPurchase.UniformTwoBidder.prize_aware_best_response
#print axioms MathEconLib.Examples.AllPurchase.UniformTwoBidder.welfare_gap
#print axioms MathEconLib.Examples.AllPurchase.UniformTwoBidder.variance_penalty
