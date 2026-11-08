/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import MathEconLibExamples.AllPurchase.Welfare

/-!
# Axiom checks for all-purchase welfare results

These checks are kept in a non-`module` test file because Lean does not allow `#print axioms`
inside a `module`. The default test target builds this file and records the results in CI.
-/

#print axioms MathEconLib.LinearScarcityAuction.welfare_decomposition
#print axioms MathEconLib.LinearScarcityAuction.editionWelfare_mean_sub_bundled_eq_variance
#print axioms MathEconLib.LinearScarcityAuction.bundledEditionWelfare_le_firstBest
#print axioms MathEconLib.Examples.AllPurchase.Welfare.welfare_gap

#print axioms MathEconLib.LinearScarcityAuction.cournotProfile_payoff_gap
#print axioms MathEconLib.LinearScarcityAuction.cournotProfile_isNash

#print axioms MathEconLib.LinearScarcityAuction.sum_cournotProfile

-- No nonempty-player assumption is needed for the equilibrium API.
example {Ω : Type} [MeasureTheory.MeasureSpace Ω]
    [MeasureTheory.IsProbabilityMeasure (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure Ω)]
    (A : MathEconLib.LinearScarcityAuction Ω 0) (hp : A.spec.price ≤ A.φ_bar) :
    A.editionsOnlyGame.IsNash (A.cournotProfile hp) := A.cournotProfile_isNash hp
