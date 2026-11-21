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
# Two finite exchange-market examples

Both examples have two goods, two consumers, and two observations. The first
supplies a joint Afriat certificate and applies the finite equilibrium theorem.
The second has positive prices and incomes and admits budget-exhausting,
market-clearing allocations at each observation. Every joint allocation nevertheless
forces a strict two-observation cycle for consumer zero. Thus accounting consistency
alone does not imply equilibrium rationalizability by increasing utilities. The
first certificate yields weighted welfare maximization and Pareto efficiency of
the same allocation; the second allocation is Pareto efficient for sum-of-goods
utilities despite failing GARE.

These are exact illustrative data, not empirical measurements or examples quoted
from Brown and Matzkin. The certificate characterization applied here is the finite
equilibrium-inequality part of Donald J. Brown and Rosa L. Matzkin (1996),
*Testable Restrictions on the Equilibrium Manifold*, Econometrica **64**(6),
1249–1262, [DOI: 10.2307/2171830](https://doi.org/10.2307/2171830), Theorem 2
in the [1995 discussion paper](https://cowles.yale.edu/sites/default/files/2022-08/d1109.pdf).
-/

@[expose] public section

open scoped BigOperators
open MathEconLib.RevealedPreference MathEconLib.RevealedPreference.Equilibrium

namespace MathEconLibExamples.RevealedEquilibrium

/-- Each consumer buys two units of the relatively cheaper good. -/
def rationalAllocation (_i : Fin 2) (t : Fin 2) : Bundle 2 :=
  if t = 0 then ![2, 0] else ![0, 2]

/-- Observed markets associated with this allocation. -/
def rationalMarket : MarketData 2 (Fin 2) (Fin 2) where
  price t := if t = 0 then ![1, 2] else ![2, 1]
  income _ _ := 2
  resources t := if t = 0 then ![4, 0] else ![0, 4]

theorem rational_price_pos (t k : Fin 2) : 0 < rationalMarket.price t k := by
  fin_cases t <;> fin_cases k <;> norm_num [rationalMarket]

theorem rational_allocation_feasible : AllocationFeasible rationalMarket rationalAllocation := by
  constructor
  · intro i t k
    fin_cases t <;> fin_cases k <;> norm_num [rationalAllocation]
  · intro i t
    fin_cases t <;>
      norm_num [rationalMarket, rationalAllocation, dot, dotProduct, Fin.sum_univ_succ]
  · intro t
    ext k
    fin_cases t <;> fin_cases k <;>
      norm_num [rationalMarket, rationalAllocation, Fin.sum_univ_succ]

/-- Constant levels and unit multipliers certify both consumers simultaneously. -/
theorem rational_afriat_certificate (i : Fin 2) :
    PositiveMultipliers (fun _ : Fin 2 => (1 : ℝ)) ∧
      AfriatInequalities (fun _ => 2) (fun _ => 1) rationalMarket.price
        (rationalAllocation i) := by
  constructor
  · intro t
    norm_num
  · intro s t
    fin_cases s <;> fin_cases t <;>
      norm_num [globalAfriatSupport, rationalMarket, rationalAllocation,
        dot, dotProduct, Fin.sum_univ_succ]

/-- The explicit certificate retains the observed joint allocation. -/
theorem rational_has_afriat_allocation : HasAfriatAllocation rationalMarket :=
  ⟨rationalAllocation, (fun _ _ => 2), (fun _ _ => 1),
    rational_allocation_feasible, rational_afriat_certificate⟩

/-- One Afriat utility per household, fixed across both observations. -/
noncomputable def rationalUtility (i : Fin 2) : Utility 2 :=
  globalAfriatUtility (fun _ => 2) (fun _ => 1) rationalMarket.price (rationalAllocation i)

/-- Applying the classical reciprocal-multiplier welfare theorem gives unit
weights and Pareto efficiency for the same supplied allocation. -/
theorem rational_weightedWelfare_and_pareto (t : Fin 2) :
    IsMaxOn (weightedWelfare rationalUtility (fun _ => 1))
      (resourceFeasibleSet (rationalMarket.resources t)) (fun i => rationalAllocation i t) ∧
      ParetoEfficient (rationalMarket.resources t) rationalUtility
        (fun i => rationalAllocation i t) := by
  have h := afriatAllocation_weightedWelfare_paretoEfficient rationalMarket
    (fun t k => (rational_price_pos t k).le) rationalAllocation
    (fun _ _ => 2) (fun _ _ => 1) rational_allocation_feasible rational_afriat_certificate t
  unfold rationalUtility
  simpa only [inv_one] using h.2

/-- Applying Brown–Matzkin's finite certificate theorem gives one regular utility
per consumer that supports both observed markets. -/
theorem rational_has_regular_equilibrium :
    HasRegularEquilibriumRationalization rationalMarket :=
  (hasRegularEquilibriumRationalization_iff_hasAfriatAllocation
    rationalMarket rational_price_pos).mpr rational_has_afriat_allocation

/-- The same market also satisfies the formulation with local nonsatiation and
initially weak budget inequalities. -/
theorem rational_has_locally_nonsatiated_equilibrium :
    HasLocallyNonsatiatedEquilibriumRationalization rationalMarket :=
  (hasLocallyNonsatiatedEquilibriumRationalization_iff_hasAfriatAllocation
    rationalMarket rational_price_pos (by decide)).mpr rational_has_afriat_allocation

/-- The rationalizable market passes the fully eliminated observable condition. -/
theorem rational_satisfies_generalized_axiom :
    GARE rationalMarket :=
  (hasRegularEquilibriumRationalization_iff_gare
    rationalMarket rational_price_pos).mp rational_has_regular_equilibrium

/-- Positive aggregate observations that will fail joint rationalizability. -/
def refutableMarket : MarketData 2 (Fin 2) (Fin 2) where
  price t := if t = 0 then ![2, 1] else ![1, 2]
  income _ _ := 9
  resources t := if t = 0 then ![8, 2] else ![2, 8]

/-- Equal sharing establishes feasibility separately at every observation. -/
def refutableAllocation (_i : Fin 2) (t : Fin 2) : Bundle 2 :=
  if t = 0 then ![4, 1] else ![1, 4]

theorem refutable_price_pos (t k : Fin 2) : 0 < refutableMarket.price t k := by
  fin_cases t <;> fin_cases k <;> norm_num [refutableMarket]

theorem refutable_income_pos (i t : Fin 2) : 0 < refutableMarket.income i t := by
  norm_num [refutableMarket]

theorem refutable_resources_pos (t k : Fin 2) : 0 < refutableMarket.resources t k := by
  fin_cases t <;> fin_cases k <;> norm_num [refutableMarket]

theorem refutable_allocation_feasible :
    AllocationFeasible refutableMarket refutableAllocation := by
  constructor
  · intro i t k
    fin_cases t <;> fin_cases k <;> norm_num [refutableAllocation]
  · intro i t
    fin_cases t <;>
      norm_num [refutableMarket, refutableAllocation, dot, dotProduct, Fin.sum_univ_succ]
  · intro t
    ext k
    fin_cases t <;> fin_cases k <;>
      norm_num [refutableMarket, refutableAllocation, Fin.sum_univ_succ]

/-- The aggregate budget identity holds at both observations. -/
theorem refutable_budget_adding_up (t : Fin 2) :
    ∑ i, refutableMarket.income i t =
      dot (refutableMarket.price t) (refutableMarket.resources t) := by
  fin_cases t <;> norm_num [refutableMarket, dot, dotProduct, Fin.sum_univ_succ]

/-- Constant utilities weakly increase and rationalize even these refutable markets.
Thus weak monotonicity alone cannot replace nonsatiation in the characterization. -/
theorem refutable_constant_utility_maximizes :
    Monotone (fun _ : Bundle 2 => (0 : ℝ)) ∧
      UtilityMaximizes refutableMarket refutableAllocation (fun _ _ => 0) := by
  constructor
  · intro x y hxy
    exact le_rfl
  · intro i t y hy hbudget
    exact le_rfl

/-- Every feasible allocation, not only equal sharing, violates consumer zero's GARP.
The low aggregate quantity of each expensive cross-period good bounds cross-costs. -/
theorem refutable_allocation_not_garp (x : Fin 2 → Fin 2 → Bundle 2)
    (hx : AllocationFeasible refutableMarket x) :
    ¬ GraphGARP refutableMarket.price (x 0) := by
  have hbudget0 := hx.budget 0 0
  have hbudget1 := hx.budget 0 1
  have hclear0 := congrFun (hx.clearing 0) 1
  have hclear1 := congrFun (hx.clearing 1) 0
  have hn0 : (0 : ℝ) ≤ x 1 0 1 := hx.nonneg 1 0 1
  have hn1 : (0 : ℝ) ≤ x 1 1 0 := hx.nonneg 1 1 0
  norm_num [refutableMarket, dot, dotProduct, Fin.sum_univ_succ] at hbudget0 hbudget1
  norm_num [refutableMarket, Fin.sum_univ_succ] at hclear0 hclear1
  have h01 : DirectlyRevealedPreferred refutableMarket.price (x 0) 0 1 := by
    simp only [DirectlyRevealedPreferred]
    norm_num [refutableMarket, dot, dotProduct, Fin.sum_univ_succ]
    linarith
  have h10 : StrictlyCheaperAt refutableMarket.price (x 0) 1 0 := by
    simp only [StrictlyCheaperAt]
    norm_num [refutableMarket, dot, dotProduct, Fin.sum_univ_succ]
    linarith
  intro hG
  exact hG 0 1 (directlyRevealedPreferred_revealedPreferred _ _ h01) h10

/-- Aggregate feasibility does not provide any common GARP allocation. -/
theorem refutable_no_garp_allocation : ¬ HasGARPAllocation refutableMarket := by
  rintro ⟨x, hx, hG⟩
  exact refutable_allocation_not_garp x hx (hG 0)

/-- The finite equilibrium inequalities have no solution for these observed markets. -/
theorem refutable_no_afriat_allocation : ¬ HasAfriatAllocation refutableMarket := by
  intro h
  exact refutable_no_garp_allocation
    ((hasGARPAllocation_iff_hasAfriatAllocation refutableMarket).mpr h)

/-- No increasing utility profile can rationalize these aggregate observations. -/
theorem refutable_no_increasing_equilibrium :
    ¬ HasIncreasingEquilibriumRationalization refutableMarket := by
  intro h
  exact refutable_no_garp_allocation
    (hasGARPAllocation_of_hasIncreasingEquilibriumRationalization
      refutableMarket refutable_price_pos h)

theorem refutable_no_regular_equilibrium :
    ¬ HasRegularEquilibriumRationalization refutableMarket := by
  intro h
  exact refutable_no_increasing_equilibrium h.to_increasing

/-- Allowing arbitrary locally nonsatiated utilities still cannot rationalize the data. -/
theorem refutable_no_locally_nonsatiated_equilibrium :
    ¬ HasLocallyNonsatiatedEquilibriumRationalization refutableMarket := by
  intro h
  exact refutable_no_garp_allocation
    (hasGARPAllocation_of_hasLocallyNonsatiatedEquilibriumRationalization
      refutableMarket refutable_price_pos h)

/-- Accounting-consistent observations can fail the fully observable axiom. -/
theorem refutable_fails_generalized_axiom :
    ¬ GARE refutableMarket := by
  intro h
  exact refutable_no_locally_nonsatiated_equilibrium
    ((hasLocallyNonsatiatedEquilibriumRationalization_iff_gare
      refutableMarket refutable_price_pos (by decide)).mpr h)

/-- Common strictly increasing sum-of-goods utility for the welfare counterexample. -/
def totalGoodsUtility (_i : Fin 2) (x : Bundle 2) : ℝ := x 0 + x 1

theorem totalGoodsUtility_strictlyIncreasing (i : Fin 2) :
    StrictlyIncreasing (totalGoodsUtility i) := by
  intro x z h
  have h0 := h.1 0
  have h1 := h.1 1
  have hneq : z 0 ≠ x 0 ∨ z 1 ≠ x 1 := by
    by_contra hn
    push Not at hn
    apply h.2
    ext k
    fin_cases k <;> simp_all
  rcases hneq with hneq | hneq
  · have := lt_of_le_of_ne h0 hneq
    dsimp [totalGoodsUtility]
    linarith
  · have := lt_of_le_of_ne h1 hneq
    dsimp [totalGoodsUtility]
    linarith

/-- Equal sharing maximizes total utility over resources at each observation,
even though these utilities do not rationalize the observed individual budgets. -/
theorem refutable_weightedWelfare_max (t : Fin 2) :
    IsMaxOn (weightedWelfare totalGoodsUtility (fun _ => 1))
      (resourceFeasibleSet (refutableMarket.resources t)) (fun i => refutableAllocation i t) := by
  apply isMaxOn_weightedWelfare_of_support (refutableMarket.resources t) ![1, 1]
    totalGoodsUtility (fun _ => 1) (fun i => refutableAllocation i t)
  · intro k
    fin_cases k <;> norm_num
  · exact refutable_allocation_feasible.clearing t
  · intro i y _hy
    simp only [one_mul]
    dsimp [totalGoodsUtility]
    norm_num [dot, dotProduct, Fin.sum_univ_succ]

/-- Pareto efficiency at every observed resource vector is insufficient for
joint rationalization at the observed prices and individual incomes. -/
theorem refutable_pareto_at_every_observation_but_not_gare :
    (∀ t, ParetoEfficient (refutableMarket.resources t) totalGoodsUtility
      (fun i => refutableAllocation i t)) ∧ ¬ GARE refutableMarket := by
  refine ⟨?_, refutable_fails_generalized_axiom⟩
  intro t
  exact paretoEfficient_of_isMaxOn_weightedWelfare _ totalGoodsUtility (fun _ => 1) _
    (fun _ => zero_lt_one) (refutable_allocation_feasible.mem_resourceFeasibleSet t)
    (refutable_weightedWelfare_max t)

end MathEconLibExamples.RevealedEquilibrium

end
