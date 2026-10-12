/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLibExamples.AllPurchase.Basic
public import MathEconLibExamples.AllPurchase.UniformProbability
public import MathEconLibExamples.AllPurchase.UniformTwoBidder
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

* The uniform all-purchase equilibrium attains profit `8/3` at price `2` and has an edition-welfare
  gap of `7/36` when buyers account for the prize.

## Tags

mathematical economics, examples, game theory, nash equilibrium, auctions, welfare
-/
