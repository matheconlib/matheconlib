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
counterexamples showing the need for each stability-transfer guard, and the empty
population.
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

-- The feasibility guard cannot be omitted from the generator equivalence.
example : StableMatching.thresholdGenerator UnbalancedMarriage.market 2 (some 0) ≤ ⊤ ∧
    ¬ StableMatching.MeetsThreshold UnbalancedMarriage.market 2 (some 0) ⊤ := by
  refine ⟨le_top, ?_⟩
  rw [← thresholdGenerator_third_man.1]
  exact thresholdGenerator_third_man.2

example (μ : UnbalancedMarriage.market.StableMatching) :
    StableMatching.thresholdGenerator UnbalancedMarriage.market 0 (some 0) ≤ μ ↔
      StableMatching.MeetsThreshold UnbalancedMarriage.market 0 (some 0) μ :=
  thresholdGenerator_first_man_le_iff μ

example : (Finset.univ : Finset (Fin 3)).sup
    (fun m => StableMatching.thresholdGenerator UnbalancedMarriage.market m
      (UnbalancedMarriage.menBest.matching m)) = UnbalancedMarriage.menBest :=
  sup_thresholdGenerators_menBest

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

/-! An acceptable cutoff that leaves the changed man unmatched. -/

example : UnmatchedCutoff.market.leM 0 none (some 0) ∧
    UnmatchedCutoff.allSingle 0 = none ∧
    (UnmatchedCutoff.market.truncateMan 0 0).IsStableMatching UnmatchedCutoff.allSingle ∧
    ¬ UnmatchedCutoff.market.IsStableMatching UnmatchedCutoff.allSingle :=
  UnmatchedCutoff.matchedness_counterexample

example : UnmatchedCutoff.market.IsBlockingPair UnmatchedCutoff.allSingle 0 1 :=
  UnmatchedCutoff.original_blockingPair

/-! Empty populations. -/

example : Nat.card emptyInput.market.StableMatching = 1 := card_stableMatching_empty

example : Nat.card {μ : emptyInput.market.StableMatching // SupIrred μ} = 0 :=
  card_supIrred_empty
