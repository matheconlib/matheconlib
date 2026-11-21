/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLibExamples.GeneralEquilibrium.PureExchange.Linear

import Mathlib.Tactic.FinCases

/-!
# Capped demand can lose its closed graph at zero income

This regression records the boundary example suggested by Bo Cowgill during review.

Reuse the linear preference `u(x) = x₁ + x₂`, with endowment `(1, 0)` and cap `(2, 2)`.
The endowment is demanded at normalized prices `(ε, 1 - ε)` for `0 < ε ≤ 1/2`.
At the limiting price `(0, 1)`, income is zero and the affordable bundle `(2, 0)`
is strictly preferred. An explicit price sequence therefore witnesses failure of
the capped-demand graph to be closed, even when restricted to normalized nonnegative prices.

This explains why positive limiting wealth `hm` is needed in
`Internal.cappedDemand_mem_of_tendsto`. It does not contradict the equilibrium existence
theorem: this endowment fails that theorem's strictly positive endowment hypothesis.
-/

@[expose] public section

open scoped BigOperators Topology
open MathEconLib.RevealedPreference Set Filter

namespace MathEconLib.GeneralEquilibrium.PureExchange.Examples.ZeroIncome

open Internal

/-- The household owns only the first good. -/
def endowment : Bundle 2 := ![1, 0]

/-- The temporary cap allows two units of either good. -/
def cap : Bundle 2 := ![2, 2]

/-- Prices approach the face where the endowed good is free. -/
def price (ε : ℝ) : Bundle 2 := ![ε, 1 - ε]

theorem endowment_nonnegative : Nonnegative endowment := by
  intro k
  fin_cases k <;> norm_num [endowment]

theorem endowment_not_strictly_positive : ¬ ∀ k, 0 < endowment k := by
  intro h
  simpa [endowment] using h 1

theorem price_mem_simplex {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) :
    price ε ∈ priceSimplex := by
  refine ⟨?_, ?_⟩
  · intro k
    fin_cases k <;> simp [price] <;> linarith
  · simp [price, Fin.sum_univ_succ]

@[simp]
theorem wealth (ε : ℝ) : dot (price ε) endowment = ε := by
  simp [price, endowment, dot, dotProduct, Fin.sum_univ_succ]

/-- Every sufficiently small positive first-good price makes the endowment optimal. -/
theorem endowment_mem_cappedDemand {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    endowment ∈ cappedDemand Linear.sumPreference endowment cap (price ε) := by
  refine ⟨endowment_nonnegative, ⟨?_, le_rfl⟩, ?_⟩
  · constructor <;> intro k <;> fin_cases k <;> norm_num [endowment, cap]
  · intro y hy
    have hbudget : ε * y.val 0 + (1 - ε) * y.val 1 ≤ ε := by
      simpa [price, endowment, dot, dotProduct, Fin.sum_univ_succ] using hy.2
    have hnonneg : 0 ≤ y.val 1 := y.property 1
    have hgap : 0 ≤ (1 - 2 * ε) * y.val 1 :=
      mul_nonneg (by linarith) hnonneg
    have hsum : y.val 0 + y.val 1 ≤ 1 := by
      nlinarith
    change dot (1 : Bundle 2) y.val ≤ dot 1 endowment
    simpa [endowment, dot, dotProduct, Fin.sum_univ_succ] using hsum

/-- At zero limiting wealth, the free first good admits a strictly better capped bundle. -/
theorem endowment_not_mem_cappedDemand_zero :
    endowment ∉ cappedDemand Linear.sumPreference endowment cap (price 0) := by
  rintro ⟨hn, _, hmax⟩
  have hbudget : Linear.leftChoice.val ∈ cappedBudget endowment cap (price 0) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Linear.leftChoice.property
    · intro k
      fin_cases k <;> norm_num [Linear.leftChoice, cap]
    · norm_num [price, endowment, Linear.leftChoice, dot, dotProduct, Fin.sum_univ_succ]
  have h := hmax hbudget
  change dot (1 : Bundle 2) Linear.leftChoice.val ≤ dot 1 endowment at h
  norm_num [Linear.leftChoice, endowment, dot, dotProduct, Fin.sum_univ_succ] at h

/-- An explicit positive price parameter tending to zero. -/
noncomputable def epsilonSeq (n : ℕ) : ℝ := (1 / 2) * (1 / ((n : ℝ) + 1))

theorem epsilonSeq_bounds (n : ℕ) : 0 < epsilonSeq n ∧ epsilonSeq n ≤ 1 / 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  constructor
  · unfold epsilonSeq
    positivity
  · unfold epsilonSeq
    linarith

theorem tendsto_price_epsilonSeq :
    Tendsto (fun n => price (epsilonSeq n)) atTop (𝓝 (price 0)) := by
  have hε : Tendsto epsilonSeq atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (1 / 2) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0)
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_pi_nhds.mpr
  intro k
  fin_cases k
  · simpa [price] using hε
  · simpa [price] using (tendsto_const_nhds (x := (1 : ℝ))).sub hε

/-- The graph fails to be closed even after restricting prices to the simplex. -/
theorem cappedDemand_graph_not_isClosed :
    ¬ IsClosed {z : Bundle 2 × Bundle 2 |
      z.1 ∈ priceSimplex ∧ z.2 ∈ cappedDemand Linear.sumPreference endowment cap z.1} := by
  intro hclosed
  have hseq : ∀ n : ℕ, price (epsilonSeq n) ∈ priceSimplex ∧
      endowment ∈ cappedDemand Linear.sumPreference endowment cap (price (epsilonSeq n)) := by
    intro n
    obtain ⟨hpos, hhalf⟩ := epsilonSeq_bounds n
    exact ⟨price_mem_simplex hpos.le (by linarith), endowment_mem_cappedDemand hpos hhalf⟩
  have hlim := hclosed.mem_of_tendsto
    (tendsto_price_epsilonSeq.prodMk_nhds (tendsto_const_nhds (x := endowment)))
    (Eventually.of_forall hseq)
  exact endowment_not_mem_cappedDemand_zero hlim.2

end MathEconLib.GeneralEquilibrium.PureExchange.Examples.ZeroIncome
