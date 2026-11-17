/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLib.RevealedPreference
import MathEconLibExamples.RevealedPreference

/-!
# Checked finite Afriat applications

Import the canonical worked examples rather than duplicating their data or proofs.
The positive application supplies a regular rationalizer; the negative application
excludes both regular rationalization and a positive-multiplier Afriat certificate.
-/

-- This module only contains anonymous compile-time clients.
set_option linter.privateModule false

open MathEconLib.RevealedPreference MathEconLibExamples.RevealedPreference

example : GARP twoDataset := two_garp

example (x : Bundle 2) :
    twoUtility x = min (x 0 + 2 * x 1) (2 * x 0 + x 1) :=
  twoUtility_eq_min x

example (t : Fin 2) : twoUtility (twoDataset.choice t) = twoLevels t :=
  twoUtility_eq_observed t

example : UtilityRationalizes twoDataset twoUtility := twoUtility_rationalizes

example : Continuous twoUtility ∧ ConcaveOn ℝ Set.univ twoUtility ∧
    StrictlyIncreasing twoUtility := twoUtility_regular

example : ∃ u : Utility 2, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
    StrictlyIncreasing u ∧ UtilityRationalizes twoDataset u :=
  two_has_regular_utility

example : ¬ GARP cycleDataset := cycle_not_garp

example (s t : Fin 3) :
    DirectlyRevealedPreferred threeDataset.price threeDataset.choice s t →
      ¬ StrictlyCheaperAt threeDataset.price threeDataset.choice t s :=
  three_no_pairwise_reversal s t

example : ¬ GARP threeDataset := three_not_garp

example : ¬ HasRegularUtilityRationalization threeDataset := three_no_regular_utility

example : ¬ HasRegularUtilityRationalization cycleDataset := cycle_no_regular_utility

example : ∃ u : Utility 2, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
    StrictlyIncreasing u ∧
    ∀ t, twoDataset.choice t ∈ utilityChoice u (budgetSet twoDataset t) :=
  two_has_regular_utilityChoice

example : ¬ ∃ U lam, PositiveMultipliers lam ∧
    AfriatInequalities U lam cycleDataset.price cycleDataset.choice :=
  cycle_no_afriat_certificate

-- One good and a zero purchase satisfy the minimal dataset assumptions.
private def zeroPurchaseDataset : Dataset 1 (Fin 1) where
  price := fun _ _ => 1
  choice := fun _ _ => 0
  price_pos := by intros; norm_num
  choice_nonneg := by intros; norm_num

-- The named theorem also applies at this boundary: only the zero bundle is affordable.
example : HasRegularUtilityRationalization zeroPurchaseDataset := by
  apply (garp_iff_hasRegularUtilityRationalization zeroPurchaseDataset).mp
  intro s t _ hcheap
  simp [StrictlyCheaperAt, zeroPurchaseDataset, dot, dotProduct] at hcheap
