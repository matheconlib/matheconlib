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
The supplied utility levels `2` and multipliers `1` satisfy every Afriat inequality.
Their explicit envelope is `min (x₀ + 2x₁) (2x₀ + x₁)`: it interpolates the supplied
levels and rationalizes both observations on their nonnegative budgets.

A second dataset chooses `(6, 0)` at prices `(1, 2)` and `(0, 2)` at prices `(1, 3)`.
Both observed expenditures equal `6`; the cross-expenditures `4` and `6` violate GARP.
Consequently this dataset has no regular utility rationalization.

A third dataset has no prohibited pairwise reversal but violates GARP along a
three-observation cycle. The pairwise condition is stated explicitly here;
`MathEconLibExamples.RevealedPreference.WGARP` applies the WGARP characterization
to these same data.

These are exact illustrative data, not empirical estimates. Rationalization permits ties.
The numerical examples are adapted from Victor H. Aguiar's Apache-2.0
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean) modules `Applications` and `Examples`.
The three-observation data are attributed there and in the accompanying manuscript to
Hans Keiding and Mich Tvede (2013), *Revealed smooth nontransitive preferences*,
Economic Theory **54**(3), 463–484, Example 1, p. 467.
[DOI: 10.1007/s00199-013-0765-z](https://doi.org/10.1007/s00199-013-0765-z).
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

/-- The explicit lower envelope selected by the supplied certificate. -/
noncomputable def twoUtility : Utility 2 :=
  globalAfriatUtility twoLevels twoMultipliers twoDataset.price twoDataset.choice

/-- Both affine support planes have an elementary closed form. -/
theorem two_supports (x : Bundle 2) :
    globalAfriatSupport twoLevels twoMultipliers twoDataset.price twoDataset.choice 0 x =
        x 0 + 2 * x 1 ∧
      globalAfriatSupport twoLevels twoMultipliers twoDataset.price twoDataset.choice 1 x =
        2 * x 0 + x 1 := by
  constructor <;>
    simp [globalAfriatSupport, twoLevels, twoMultipliers, twoDataset, twoPrices,
      twoChoices, dot, dotProduct, Fin.sum_univ_succ]

/-- An independently readable formula for the constructed utility on every bundle. -/
theorem twoUtility_eq_min (x : Bundle 2) :
    twoUtility x = min (x 0 + 2 * x 1) (2 * x 0 + x 1) := by
  apply le_antisymm
  · apply le_min
    · exact (globalAfriatUtility_le_support _ _ _ _ 0 x).trans_eq (two_supports x).1
    · exact (globalAfriatUtility_le_support _ _ _ _ 1 x).trans_eq (two_supports x).2
  · apply le_globalAfriatUtility_of_le_supports
    intro t
    fin_cases t
    · exact (min_le_left _ _).trans_eq (two_supports x).1.symm
    · exact (min_le_right _ _).trans_eq (two_supports x).2.symm

/-- The envelope interpolates the utility levels of the supplied certificate. -/
theorem twoUtility_eq_observed (t : Fin 2) :
    twoUtility (twoDataset.choice t) = twoLevels t :=
  globalAfriatUtility_eq_observed _ _ _ _ two_afriat_inequalities t

/-- The supplied certificate directly proves rationalization by this explicit envelope. -/
theorem twoUtility_rationalizes : UtilityRationalizes twoDataset twoUtility :=
  globalAfriatUtility_rationalizes twoDataset twoLevels twoMultipliers
    two_afriat_inequalities two_positive_multipliers

/-- The selected envelope, not merely an existential utility, has all regularity properties. -/
theorem twoUtility_regular :
    Continuous twoUtility ∧ ConcaveOn ℝ Set.univ twoUtility ∧
      StrictlyIncreasing twoUtility :=
  ⟨globalAfriatUtility_continuous _ _ _ _, globalAfriatUtility_concaveOn _ _ _ _,
    globalAfriatUtility_strictlyIncreasing _ _ _ _ twoDataset.price_pos
      two_positive_multipliers⟩

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
  have h10 : DirectlyRevealedPreferred cycleDataset.price cycleDataset.choice 1 0 := by
    norm_num [DirectlyRevealedPreferred, cycleDataset, cyclePrices, cycleChoices,
      dot, dotProduct, Fin.sum_univ_succ]
  have h01 : StrictlyCheaperAt cycleDataset.price cycleDataset.choice 0 1 := by
    norm_num [StrictlyCheaperAt, cycleDataset, cyclePrices, cycleChoices,
      dot, dotProduct, Fin.sum_univ_succ]
  exact hG 1 0 (directlyRevealedPreferred_revealedPreferred _ _ h10) h01

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

/-- Prices in the three-observation example ported from `WGARP.Examples`. -/
def threePrices (t : Fin 3) : Bundle 3 :=
  if t = 0 then ![4, 1, 5] else if t = 1 then ![5, 4, 1] else ![1, 5, 4]

/-- Choices in the three-observation example ported from `WGARP.Examples`. -/
def threeChoices (t : Fin 3) : Bundle 3 :=
  if t = 0 then ![4, 1, 1] else if t = 1 then ![1, 4, 1] else ![1, 1, 4]

/-- The three-observation dataset has positive prices and nonnegative choices. -/
def threeDataset : Dataset 3 (Fin 3) where
  price := threePrices
  choice := threeChoices
  price_pos := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [threePrices]
  choice_nonneg := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [threeChoices]

/-- Rows index prices and columns index choices. -/
theorem three_expenditure_table (s t : Fin 3) :
    expenditure threeDataset s (threeDataset.choice t) =
      (![![22, 13, 25], ![25, 22, 13], ![13, 25, 22]] : Fin 3 → Fin 3 → ℝ) s t := by
  fin_cases s <;> fin_cases t <;>
    norm_num [expenditure, threeDataset, threePrices, threeChoices, dot, dotProduct,
      Fin.sum_univ_succ]

/-- No pair has weak revealed preference in one direction and a strictly cheaper
reverse choice. This is the exact pairwise restriction checked here. -/
theorem three_no_pairwise_reversal (s t : Fin 3) :
    DirectlyRevealedPreferred threeDataset.price threeDataset.choice s t →
      ¬ StrictlyCheaperAt threeDataset.price threeDataset.choice t s := by
  fin_cases s <;> fin_cases t <;>
    norm_num [DirectlyRevealedPreferred, StrictlyCheaperAt, threeDataset, threePrices, threeChoices,
      dot, dotProduct, Fin.sum_univ_succ]

/-- The strictly cheaper comparisons form the cycle `0 → 1 → 2 → 0`. -/
theorem three_strict_cycle :
    StrictlyCheaperAt threeDataset.price threeDataset.choice 0 1 ∧
      StrictlyCheaperAt threeDataset.price threeDataset.choice 1 2 ∧
      StrictlyCheaperAt threeDataset.price threeDataset.choice 2 0 := by
  norm_num [StrictlyCheaperAt, threeDataset, threePrices, threeChoices,
    dot, dotProduct, Fin.sum_univ_succ]

/-- Pairwise consistency does not suffice for GARP: the length-three cycle violates it. -/
theorem three_not_garp : ¬ GARP threeDataset := by
  intro hG
  have h01 : DirectlyRevealedPreferred threeDataset.price threeDataset.choice 0 1 :=
    le_of_lt three_strict_cycle.1
  have h12 : DirectlyRevealedPreferred threeDataset.price threeDataset.choice 1 2 :=
    le_of_lt three_strict_cycle.2.1
  exact hG 0 2 ((directlyRevealedPreferred_revealedPreferred _ _ h01).trans
    (directlyRevealedPreferred_revealedPreferred _ _ h12)) three_strict_cycle.2.2

/-- The three-cycle excludes regular utility rationalization despite pairwise consistency. -/
theorem three_no_regular_utility : ¬ HasRegularUtilityRationalization threeDataset := by
  intro h
  exact three_not_garp ((garp_iff_hasRegularUtilityRationalization threeDataset).mpr h)

end MathEconLibExamples.RevealedPreference

end
