/-
Copyright (c) 2026 Daniel Lyng, Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng, Victor H. Aguiar
-/
module

public import MathEconLibExamples.AllPurchase.UniformTwoBidder

public import MathEconLibExamples.AllPurchase.Welfare
public import MathEconLibExamples.Choice.SubstituteEnvelope
public import MathEconLibExamples.GameTheory.ExplicitComparisons
public import MathEconLibExamples.GameTheory.MatchingPennies
public import MathEconLibExamples.Matching.DistributiveMarriage
public import MathEconLibExamples.Matching.JointPreservation
public import MathEconLibExamples.Matching.UnbalancedMarriage
public import MathEconLibExamples.Mechanism.PostedPriceUtility
public import MathEconLibExamples.Preferences.Finite
public import MathEconLibExamples.RevealedPreference
public import MathEconLibExamples.SingleParameter.BeckerCrime

/-!
# Mathematical economics examples

Concrete economic models illustrate the library's definitions and results.

## Main statements

* Matching pennies has a unique mixed Nash equilibrium: Both players randomize uniformly.
* Matching pennies has no pure Nash equilibrium.
* A Becker-inspired crime-choice model gives a threshold rule and deterrence results
  for individuals and aggregate crime under a fixed type distribution.
* A two-couple marriage market has distinct stable outcomes whose lattice join,
  meet, and intrinsic ideal representations are checked explicitly.

## Tags

mathematical economics, examples, game theory, nash equilibrium, price theory
-/
