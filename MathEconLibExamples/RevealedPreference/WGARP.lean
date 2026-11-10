/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference
public import MathEconLibExamples.RevealedPreference

/-!
# WGARP rationalization beyond ordinary utility

The canonical three-observation example satisfies WGARP but violates GARP. Applying
both characterization theorems to those same data supplies a finite coherent CMU
rationalization and excludes a regular ordinary utility rationalization. The underlying
prices, choices, and exact arithmetic are defined once in
`MathEconLibExamples.RevealedPreference`.

A separate tie example distinguishes WGARP from the single-valued WARP condition:
two distinct choices on the same budget are permitted by weak rationalization.
These are exact mathematical examples, not empirical estimates. No demand existence
on unobserved budgets, numerical skew symmetry, or matrix/simplex representation is claimed.

## References

The three-observation data are attributed in the canonical example to Hans Keiding
and Mich Tvede (2013), *Revealed smooth nontransitive preferences*, Economic Theory
**54**(3), 463–484, Example 1, p. 467.
[DOI: 10.1007/s00199-013-0765-z](https://doi.org/10.1007/s00199-013-0765-z).
-/

@[expose] public section

namespace MathEconLibExamples.RevealedPreference

open MathEconLib.RevealedPreference

/-- The existing pairwise checks are exactly WGARP. -/
theorem three_wgarp : WGARP threeDataset := by
  intro s t hts
  apply le_of_not_gt
  intro hst
  exact three_no_pairwise_reversal t s
    ((directlyRevealedPreferred_iff_expenditureGap_nonneg threeDataset t s).mpr hts)
    ((strictlyCheaperAt_iff_expenditureGap_pos threeDataset s t).mpr hst)

/-- The named WGARP characterization supplies a coherent CMU, while finite Afriat
rules out every regular ordinary utility for the same observations. -/
theorem three_cmu_but_not_regular_utility :
    HasFiniteCoherentCMURationalization threeDataset ∧
      ¬ HasRegularUtilityRationalization threeDataset := by
  refine ⟨(wgarp_iff_hasFiniteCoherentCMURationalization threeDataset).mp three_wgarp, ?_⟩
  intro h
  exact three_not_garp ((garp_iff_hasRegularUtilityRationalization threeDataset).mpr h)

/-- The preference-function characterization also applies to the three-cycle. -/
theorem three_has_regular_preference : HasRegularPreferenceRationalization threeDataset :=
  (wgarp_iff_hasRegularPreferenceRationalization threeDataset).mp three_wgarp

/-- The same rationalizer supplies a choice correspondence containing each observed
choice on its budget, without asserting nonempty demand on other menus. -/
theorem three_has_regular_preferenceChoice :
    ∃ r : PreferenceFunction 3,
      ContinuousPreference r ∧ StrictlyIncreasingFirst r ∧ Asymmetric r ∧
        ∀ t, threeDataset.choice t ∈ preferenceChoice r (budgetSet threeDataset t) :=
  (wgarp_iff_exists_regular_preferenceChoice threeDataset).mp three_wgarp

/-- Two distinct bundles chosen at identical prices and identical expenditure. -/
def tieDataset : Dataset 2 (Fin 2) where
  price := fun _ => ![1, 1]
  choice := fun t => if t = 0 then ![1, 0] else ![0, 1]
  price_pos := by intro t i; fin_cases i <;> norm_num
  choice_nonneg := by intro t i; fin_cases t <;> fin_cases i <;> norm_num

/-- Every cross-budget comparison in the tie example is an equality. -/
theorem tie_expenditureGap (s t : Fin 2) : expenditureGap tieDataset s t = 0 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [expenditureGap, tieDataset, dot, dotProduct, Fin.sum_univ_succ]

/-- WGARP permits distinct choices tied on the same budget. -/
theorem tie_wgarp : WGARP tieDataset := by
  intro s t _
  exact le_of_eq (tie_expenditureGap s t)

/-- The strict reverse-affordability condition for single-valued WARP fails.
The condition is written explicitly to avoid confusing it with WGARP. -/
theorem tie_not_unique_choice_warp :
    ¬ (∀ s t, tieDataset.choice s ≠ tieDataset.choice t →
      DirectlyRevealedPreferred tieDataset.price tieDataset.choice s t →
        expenditure tieDataset t (tieDataset.choice t) <
          expenditure tieDataset t (tieDataset.choice s)) := by
  intro h
  have hne : tieDataset.choice 0 ≠ tieDataset.choice 1 := by
    intro heq
    have hcoord := congrFun heq 0
    norm_num [tieDataset] at hcoord
  have hdirect : DirectlyRevealedPreferred tieDataset.price tieDataset.choice 0 1 :=
    (directlyRevealedPreferred_iff_expenditureGap_nonneg tieDataset 0 1).mpr
      (le_of_eq (tie_expenditureGap 0 1).symm)
  have hbad := h 0 1 hne hdirect
  norm_num [expenditure, tieDataset, dot, dotProduct, Fin.sum_univ_succ] at hbad

/-- Regular preference rationalization retains these budget ties. -/
theorem tie_has_regular_preference : HasRegularPreferenceRationalization tieDataset :=
  (wgarp_iff_hasRegularPreferenceRationalization tieDataset).mp tie_wgarp

/-- A weak comparison followed by a strict reverse comparison violates WGARP. -/
theorem cycle_not_wgarp : ¬ WGARP cycleDataset := by
  intro h
  have hbad := h (0 : Fin 2) (1 : Fin 2)
  norm_num [expenditureGap, cycleDataset, cyclePrices, cycleChoices,
    dot, dotProduct, Fin.sum_univ_succ] at hbad

/-- The converse characterization excludes regular preference rationalization
for the mixed weak/strict binary cycle. -/
theorem cycle_no_regular_preference : ¬ HasRegularPreferenceRationalization cycleDataset := by
  intro h
  exact cycle_not_wgarp ((wgarp_iff_hasRegularPreferenceRationalization cycleDataset).mpr h)

end MathEconLibExamples.RevealedPreference
