/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.GeneralEquilibrium.PureExchange

import Mathlib.Tactic.FinCases

/-!
# Pure exchange with linear preferences and demand ties

Two households each own one unit of each of two goods and rank bundles by the sum of their
coordinates. The primitive-preference existence theorem supplies a Walrasian equilibrium
with positive normalized prices, exhausted unit incomes, and two units cleared per good.
All continuity, ordinary convexity, and strong monotonicity assumptions are proved here.

At equal prices, `(2, 0)` and `(0, 2)` are distinct, indifferent full-budget maximizers.
Thus the same model exercises nonunique demand; no strict convexity or demand selection is used.
-/

@[expose] public section

open scoped BigOperators Topology
open MathEconLib.Preferences MathEconLib.RevealedPreference

namespace MathEconLib.GeneralEquilibrium.PureExchange.Examples.Linear

/-- Both goods contribute equally to the household's ranking. -/
noncomputable def sumPreference : CompletePreference (Orthant 2) :=
  CompletePreference.ofUtility (fun x => dot 1 x.val)

@[simp]
theorem sumPreference_le (x y : Orthant 2) :
    sumPreference.le x y ↔ dot 1 x.val ≤ dot 1 y.val := Iff.rfl

/-- Separate contour continuity, ordinary convexity, and strong monotonicity hold. -/
theorem sumPreference_regularity : PreferenceRegularity sumPreference where
  closed_upper := by
    intro x
    change IsClosed {y : Orthant 2 | dot 1 x.val ≤ dot 1 y.val}
    exact isClosed_le continuous_const
      ((continuous_dot (1 : Bundle 2)).comp continuous_subtype_val)
  closed_lower := by
    intro x
    change IsClosed {y : Orthant 2 | dot 1 y.val ≤ dot 1 x.val}
    exact isClosed_le ((continuous_dot (1 : Bundle 2)).comp continuous_subtype_val)
      continuous_const
  convex_upper := by
    intro x y hy z hz a b ha hb hab
    obtain ⟨hyn, hxy⟩ := hy
    obtain ⟨hzn, hxz⟩ := hz
    refine ⟨fun k => add_nonneg (mul_nonneg ha (hyn k)) (mul_nonneg hb (hzn k)), ?_⟩
    change dot (1 : Bundle 2) x.val ≤ dot 1 (a • y + b • z)
    rw [dot_add_smul]
    calc
      dot (1 : Bundle 2) x.val = a * dot 1 x.val + b * dot 1 x.val := by
        rw [← add_mul, hab, one_mul]
      _ ≤ a * dot 1 y + b * dot 1 z :=
        add_le_add (mul_le_mul_of_nonneg_left hxy ha) (mul_le_mul_of_nonneg_left hxz hb)
  strong_mono := by
    intro x y hxy
    change dot (1 : Bundle 2) x.val ≤ dot 1 y.val ∧ ¬ dot 1 y.val ≤ dot 1 x.val
    have h := dot_strictlyIncreasing_of_pos (p := (1 : Bundle 2)) (fun k => by norm_num)
      (strictDominates_iff_lt.mpr hxy)
    exact ⟨h.le, not_le_of_gt h⟩

/-- Each household owns one unit of each good. -/
def endowment : Fin 2 → Bundle 2 := fun _ => 1

theorem endowment_pos : ∀ i k, 0 < endowment i k := by
  intro i k
  norm_num [endowment]

/-- A checked application of the primitive-preference theorem, including the
concrete budget and resource consequences for this economy. -/
theorem exists_equilibrium :
    ∃ (p : Bundle 2) (x : Fin 2 → Orthant 2),
      IsWalrasianEquilibrium endowment (fun _ => sumPreference) p x ∧
      (∑ k, p k) = 1 ∧
      (∀ k, 0 < p k) ∧
      (∀ i, dot p (x i).val = 1) ∧
      (∀ k, ∑ i, (x i).val k = 2) := by
  obtain ⟨p, x, hEq, hnorm, hpos, hbudget⟩ :=
    exists_walrasianEquilibrium (by norm_num : 0 < 2) endowment (fun _ => sumPreference)
      endowment_pos (fun _ => sumPreference_regularity)
  have hwealth : ∀ i, dot p (endowment i) = 1 := by
    intro i
    simpa [endowment, dot, dotProduct] using hnorm
  refine ⟨p, x, hEq, hnorm, hpos, fun i => (hbudget i).trans (hwealth i), ?_⟩
  intro k
  have hk := congrFun hEq.clearing k
  simpa [endowment, Finset.sum_apply, Fin.sum_univ_succ] using hk

/-- Equal positive normalized prices. -/
noncomputable def halfPrice : Bundle 2 := ![1 / 2, 1 / 2]

/-- A household spends all income on the first good. -/
def leftChoice : Orthant 2 := ⟨![2, 0], by intro k; fin_cases k <;> norm_num⟩

/-- A household spends all income on the second good. -/
def rightChoice : Orthant 2 := ⟨![0, 2], by intro k; fin_cases k <;> norm_num⟩

theorem halfPrice_normalized_positive :
    Nonnegative halfPrice ∧ (∑ k, halfPrice k) = 1 ∧ ∀ k, 0 < halfPrice k := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    fin_cases k <;> norm_num [halfPrice]
  · norm_num [halfPrice, Fin.sum_univ_succ]
  · intro k
    fin_cases k <;> norm_num [halfPrice]

/-- Two distinct, indifferent choices belong to the canonical full-budget demand. -/
theorem distinct_tied_demand :
    leftChoice ≠ rightChoice ∧
      leftChoice ∈ demand sumPreference (1 : Bundle 2) halfPrice ∧
      rightChoice ∈ demand sumPreference (1 : Bundle 2) halfPrice ∧
      sumPreference.le leftChoice rightChoice ∧ sumPreference.le rightChoice leftChoice := by
  have hleft : dot (1 : Bundle 2) leftChoice.val = 2 := by
    norm_num [leftChoice, dot, dotProduct, Fin.sum_univ_succ]
  have hright : dot (1 : Bundle 2) rightChoice.val = 2 := by
    norm_num [rightChoice, dot, dotProduct, Fin.sum_univ_succ]
  have hwealth : dot halfPrice (1 : Bundle 2) = 1 := by
    norm_num [halfPrice, dot, dotProduct, Fin.sum_univ_succ]
  have hmax (y : Orthant 2) (hy : y ∈ budgetSet (1 : Bundle 2) halfPrice) :
      sumPreference.le y leftChoice ∧ sumPreference.le y rightChoice := by
    have hscale : dot (1 : Bundle 2) y.val = 2 * dot halfPrice y.val := by
      simp [halfPrice, dot, dotProduct, Fin.sum_univ_succ]
      ring
    have hscore : dot (1 : Bundle 2) y.val ≤ 2 := by
      have hbudget : dot halfPrice y.val ≤ 1 := by
        change dot halfPrice y.val ≤ dot halfPrice (1 : Bundle 2) at hy
        simpa only [hwealth] using hy
      linarith
    exact ⟨(sumPreference_le _ _).mpr (by simpa only [hleft] using hscore),
      (sumPreference_le _ _).mpr (by simpa only [hright] using hscore)⟩
  have hl : leftChoice ∈ demand sumPreference (1 : Bundle 2) halfPrice := by
    apply (mem_demand _ _ _ _).mpr
    refine ⟨?_, fun y hy => (hmax y hy).1⟩
    change dot halfPrice leftChoice.val ≤ dot halfPrice (1 : Bundle 2)
    norm_num [leftChoice, halfPrice, dot, dotProduct, Fin.sum_univ_succ]
  have hr : rightChoice ∈ demand sumPreference (1 : Bundle 2) halfPrice := by
    apply (mem_demand _ _ _ _).mpr
    refine ⟨?_, fun y hy => (hmax y hy).2⟩
    change dot halfPrice rightChoice.val ≤ dot halfPrice (1 : Bundle 2)
    norm_num [rightChoice, halfPrice, dot, dotProduct, Fin.sum_univ_succ]
  refine ⟨?_, hl, hr, Choice.indifferent_of_mem_maximizers sumPreference.toPreference hl hr⟩
  intro h
  have hc := congrArg (fun x : Orthant 2 => x.val 0) h
  norm_num [leftChoice, rightChoice] at hc

/-- Demand is genuinely multivalued in this ordinary-convex-preference example. -/
theorem demand_not_subsingleton : ¬ (demand sumPreference (1 : Bundle 2) halfPrice).Subsingleton :=
  fun h => distinct_tied_demand.1 (h distinct_tied_demand.2.1 distinct_tied_demand.2.2.1)

end MathEconLib.GeneralEquilibrium.PureExchange.Examples.Linear
