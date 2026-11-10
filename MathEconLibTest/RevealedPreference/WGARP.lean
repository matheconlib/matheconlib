/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLib.RevealedPreference
import MathEconLibExamples.RevealedPreference.WGARP

/-!
# WGARP applications and boundary cases

Reuse the canonical numerical applications. The additional clients retain empty
observations in the terminal equivalences, repeated endpoints, zero purchases, and
zero-dimensional commodity spaces. Public theorem contracts are pinned separately
in `WGARPCompatibility`, which imports no examples or leaf modules.
-/

set_option linter.privateModule false

open MathEconLib.RevealedPreference MathEconLibExamples.RevealedPreference

example : WGARP threeDataset ∧ ¬ GARP threeDataset := ⟨three_wgarp, three_not_garp⟩

example : HasFiniteCoherentCMURationalization threeDataset ∧
    ¬ HasRegularUtilityRationalization threeDataset :=
  three_cmu_but_not_regular_utility

example : HasRegularPreferenceRationalization threeDataset := three_has_regular_preference

example : ∃ r : PreferenceFunction 3,
    ContinuousPreference r ∧ StrictlyIncreasingFirst r ∧ Asymmetric r ∧
      ∀ t, threeDataset.choice t ∈ preferenceChoice r (budgetSet threeDataset t) :=
  three_has_regular_preferenceChoice

example : WGARP tieDataset ∧ HasRegularPreferenceRationalization tieDataset :=
  ⟨tie_wgarp, tie_has_regular_preference⟩

example :
    ¬ (∀ s t, tieDataset.choice s ≠ tieDataset.choice t →
      DirectlyRevealedPreferred tieDataset.price tieDataset.choice s t →
        expenditure tieDataset t (tieDataset.choice t) <
          expenditure tieDataset t (tieDataset.choice s)) :=
  tie_not_unique_choice_warp

example : ¬ WGARP cycleDataset ∧ ¬ HasRegularPreferenceRationalization cycleDataset :=
  ⟨cycle_not_wgarp, cycle_no_regular_preference⟩

private def zeroPurchaseDataset (L : ℕ) : Dataset L (Fin 1) where
  price := fun _ _ => 1
  choice := fun _ _ => 0
  price_pos := by intros; norm_num
  choice_nonneg := by intros; norm_num

-- Nonzero observed purchases and a lower bound of two goods are not required.
example : HasRegularPreferenceRationalization (zeroPurchaseDataset 1) :=
  (wgarp_iff_hasRegularPreferenceRationalization _).mp (wgarp_of_subsingleton _)

-- On the singleton zero-dimensional bundle space, strict increase is vacuous.
example : HasFiniteCoherentCMURationalization (zeroPurchaseDataset 0) ∧
    HasRegularPreferenceRationalization (zeroPurchaseDataset 0) :=
  ⟨(wgarp_iff_hasFiniteCoherentCMURationalization _).mp (wgarp_of_subsingleton _),
    (wgarp_iff_hasRegularPreferenceRationalization _).mp (wgarp_of_subsingleton _)⟩

private def emptyDataset : Dataset 1 (Fin 0) where
  price := Fin.elim0
  choice := Fin.elim0
  price_pos := fun t => Fin.elim0 t
  choice_nonneg := fun t => Fin.elim0 t

-- The pairwise result is meaningful without a Nonempty instance on observations.
example : WGARP emptyDataset ∧ ∀ s t, GARP (pairDataset emptyDataset s t) :=
  ⟨wgarp_of_subsingleton _, (wgarp_iff_pairwise_garp _).mp (wgarp_of_subsingleton _)⟩

-- A repeated endpoint must work even when the full dataset fails WGARP.
example {L : ℕ} {T : Type*} (D : Dataset L T) (s : T) :
    HasRegularUtilityRationalization (pairDataset D s s) := by
  apply hasRegularUtilityRationalization_of_garp
  apply (garp_bool_iff_wgarp _).mpr
  intro a b
  cases a <;> cases b <;> simp [expenditureGap, pairDataset]

-- The terminal characterizations also cover the empty sample: the generic CMU
-- witness need not have observations as its coalition carrier.
example : HasFiniteCoherentCMURationalization emptyDataset ∧
    HasRegularPreferenceRationalization emptyDataset :=
  ⟨(wgarp_iff_hasFiniteCoherentCMURationalization _).mp (wgarp_of_subsingleton _),
    (wgarp_iff_hasRegularPreferenceRationalization _).mp (wgarp_of_subsingleton _)⟩
