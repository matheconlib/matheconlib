/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLibExamples.GameTheory.Braess
public import MathEconLibExamples.GameTheory.MatchingPennies
public import MathEconLibExamples.GameTheory.Pigou
public import MathEconLibExamples.SingleParameter.BeckerCrime

/-!
# Mathematical economics examples

Concrete economic models illustrate the library's definitions and results.

## Main statements

* Matching pennies has a unique mixed Nash equilibrium: Both players randomize uniformly.
* Matching pennies has no pure Nash equilibrium.
* Braess's paradox: adding a free link raises equilibrium latency from `3 / 2` to `2`.
* Pigou's example attains the Roughgarden–Tardos price-of-anarchy bound `4 / 3`.
* A Becker-inspired crime-choice model gives a threshold rule and deterrence results
  for individuals and aggregate crime under a fixed type distribution.

## Tags

mathematical economics, examples, game theory, nash equilibrium, price theory, price of anarchy,
braess paradox
-/
