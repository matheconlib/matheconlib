/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Concrete applications of finite Afriat rationalization

Two observations at prices `(1, 2)` and `(2, 1)` choose `(2, 0)` and `(0, 2)`.
The utility levels `2` and multipliers `1` satisfy every Afriat inequality.
Applying the finite Afriat theorem gives a continuous, concave, strictly increasing
utility under which the observations maximize utility on their nonnegative budgets.

A second dataset chooses `(6, 0)` at prices `(1, 2)` and `(0, 2)` at prices `(1, 3)`.
Both observed expenditures equal `6`; the cross-expenditures `4` and `6` violate GARP.
Consequently this dataset has no regular utility rationalization.

These are exact illustrative data, not empirical estimates. Rationalization permits ties.
The numerical examples are adapted from Victor H. Aguiar's Apache-2.0
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean) modules `Applications` and `Examples`.
-/

@[expose] public section

namespace MathEconLibExamples.RevealedPreference

open MathEconLib.RevealedPreference

/-- The first dataset's two price vectors. -/
def twoPrices (t : Fin 2) : Bundle 2 :=
  if t = 0 then ![1, 2] else ![2, 1]

/-- Each observation purchases two units of its cheaper good. -/
def twoChoices (t : Fin 2) : Bundle 2 :=
  if t = 0 then ![2, 0] else ![0, 2]

/-- A concrete consumer dataset with all primitive assumptions proved. -/
def twoDataset : Dataset 2 (Fin 2) where
  price := twoPrices
  choice := twoChoices
  price_pos := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [twoPrices]
  choice_nonneg := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [twoChoices]

/-- Equal utility levels provide an Afriat certificate for this dataset. -/
def twoLevels (_t : Fin 2) : ℝ := 2

/-- Unit multipliers provide an Afriat certificate for this dataset. -/
def twoMultipliers (_t : Fin 2) : ℝ := 1

theorem two_positive_multipliers : PositiveMultipliers twoMultipliers := by
  intro t
  norm_num [twoMultipliers]

theorem two_afriat_inequalities :
    AfriatInequalities twoLevels twoMultipliers twoDataset.price twoDataset.choice := by
  intro s t
  fin_cases s <;> fin_cases t <;>
    norm_num [globalAfriatSupport, twoLevels, twoMultipliers,
      twoDataset, twoPrices, twoChoices, dot, dotProduct, Fin.sum_univ_succ]

/-- The named finite certificate equivalence verifies GARP for the numerical data. -/
theorem two_garp : GARP twoDataset :=
  (garp_iff_exists_afriatInequalities twoDataset).mpr
    ⟨twoLevels, twoMultipliers, two_positive_multipliers, two_afriat_inequalities⟩

/-- Applying the named finite Afriat theorem yields a continuous, concave, strictly
increasing rationalizer for the two observed budget choices. -/
theorem two_has_regular_utility : HasRegularUtilityRationalization twoDataset :=
  (garp_iff_hasRegularUtilityRationalization twoDataset).mp two_garp

/-- The same rationalizer defines a choice correspondence in the existing choice API
that contains both observations on their respective budgets. -/
theorem two_has_regular_utilityChoice :
    ∃ u : Utility 2, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧ StrictlyIncreasing u ∧
      ∀ t, twoDataset.choice t ∈ utilityChoice u (budgetSet twoDataset t) :=
  (garp_iff_exists_regular_utilityChoice twoDataset).mp two_garp

/-- Prices for an affordability cycle with one strict comparison. -/
def cyclePrices : Fin 2 → Bundle 2 := ![![1, 2], ![1, 3]]

/-- Choices for an affordability cycle with one strict comparison. -/
def cycleChoices : Fin 2 → Bundle 2 := ![![6, 0], ![0, 2]]

/-- A second admissible dataset whose observed choices violate GARP. -/
def cycleDataset : Dataset 2 (Fin 2) where
  price := cyclePrices
  choice := cycleChoices
  price_pos := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [cyclePrices]
  choice_nonneg := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [cycleChoices]

/-- At the second observation the first choice is affordable; at the first observation
the second choice is strictly cheaper. These two comparisons violate GARP. -/
theorem cycle_not_garp : ¬ GARP cycleDataset := by
  intro hG
  have h10 : DirectRP cycleDataset.price cycleDataset.choice 1 0 := by
    norm_num [DirectRP, cycleDataset, cyclePrices, cycleChoices, dot, dotProduct, Fin.sum_univ_succ]
  have h01 : StrictlyCheaperAt cycleDataset.price cycleDataset.choice 0 1 := by
    norm_num [StrictlyCheaperAt, cycleDataset, cyclePrices, cycleChoices,
      dot, dotProduct, Fin.sum_univ_succ]
  exact hG 1 0 (directRP_revealedPref _ _ h10) h01

/-- The GARP violation rules out every continuous, concave, strictly increasing
utility rationalization, by the reverse implication of finite Afriat. -/
theorem cycle_no_regular_utility : ¬ HasRegularUtilityRationalization cycleDataset := by
  intro h
  exact cycle_not_garp ((garp_iff_hasRegularUtilityRationalization cycleDataset).mpr h)

/-- The same cycle also rules out a positive-multiplier Afriat certificate. -/
theorem cycle_no_afriat_certificate :
    ¬ ∃ U lam, PositiveMultipliers lam ∧
      AfriatInequalities U lam cycleDataset.price cycleDataset.choice := by
  intro h
  exact cycle_not_garp ((garp_iff_exists_afriatInequalities cycleDataset).mpr h)

end MathEconLibExamples.RevealedPreference

end
