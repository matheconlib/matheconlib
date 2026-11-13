/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
import MathEconLibExamples.Matching.CountingFoundations

/-!
# Checked applications of the counting foundations

Regression checks for `MathEconLibExamples.Matching.CountingFoundations`: an
infeasible threshold and an unmatched man in the unbalanced marriage market, the
counterexample to transfer through an originally unacceptable cutoff, and the
empty population.
-/

open MathEconLib.Matching MarriageMarket
open MathEconLibExamples.Matching
open MathEconLibExamples.Matching.CountingFoundations

/-! Unmatched man and infeasible threshold. -/

example (μ : UnbalancedMarriage.market.StableMatching) : μ.matching 2 = none :=
  matching_third_man μ

example : StableMatching.thresholdGenerator UnbalancedMarriage.market 2 (some 0) = ⊤ :=
  thresholdGenerator_third_man.1

example : ¬ StableMatching.MeetsThreshold UnbalancedMarriage.market 2 (some 0)
    (StableMatching.thresholdGenerator UnbalancedMarriage.market 2 (some 0)) :=
  thresholdGenerator_third_man.2

example : UnbalancedMarriage.market.IsStableMatching UnbalancedMarriage.crossed :=
  crossed_stable_of_truncateMan

example : 2 ≤ Nat.card UnbalancedMarriage.market.StableMatching ∧
    Nat.card UnbalancedMarriage.market.StableMatching ≤ 27 :=
  card_stableMatching_bounds

/-! Moving a cutoff below an unacceptable partner. -/

example : cutoffInput.market.ltM cutoffMan (some cutoffWoman) none ∧
    movedMarket.IsStableMatching fullMatching ∧
    ¬ cutoffInput.market.IsStableMatching fullMatching :=
  cutoff_counterexample

/-! Empty populations. -/

example : Nat.card emptyInput.market.StableMatching = 1 := card_stableMatching_empty

example : Nat.card {μ : emptyInput.market.StableMatching // SupIrred μ} = 0 :=
  card_supIrred_empty
