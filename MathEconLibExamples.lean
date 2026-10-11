/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLibExamples.AllPurchase.Basic
public import MathEconLibExamples.AllPurchase.Welfare
public import MathEconLibExamples.GameTheory.MatchingPennies

/-!
# Mathematical economics examples

Concrete economic models illustrate the library's definitions, equilibrium results, and welfare
comparisons.

## Main statements

* Matching pennies has a unique mixed Nash equilibrium: Both players randomize uniformly.
* Matching pennies has no pure Nash equilibrium.
* The all-purchase Cournot example applies the welfare decomposition and obtains a gap of `25/36`.

## Tags

mathematical economics, examples, game theory, nash equilibrium, auctions, welfare
-/

#print axioms MathEconLib.LinearScarcityAuction.welfare_decomposition
#print axioms MathEconLib.LinearScarcityAuction.editionWelfare_mean_sub_bundled_eq_variance
#print axioms MathEconLib.LinearScarcityAuction.cournotPurchaseLinear_best_response
#print axioms MathEconLib.LinearScarcityAuction.bundledEditionWelfare_le_firstBest
#print axioms MathEconLib.Examples.AllPurchase.Welfare.welfare_gap
