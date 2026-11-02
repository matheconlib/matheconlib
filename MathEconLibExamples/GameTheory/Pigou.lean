/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import MathEconLib.GameTheory.Routing.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Pigou's example

One unit of traffic travels over two parallel edges. The constant edge has latency `1`, and the
congestible edge has latency equal to its load. At the Wardrop equilibrium all traffic takes the
congestible edge, for total latency `1`. Splitting traffic equally gives total latency `3 / 4`, the
minimum over feasible flows. The ratio is `4 / 3`, so the Roughgarden–Tardos bound
`RoutingGame.IsWardrop.cost_le_four_thirds_mul` is attained.

## Main definitions

* `pigou`: The two-edge network with latencies `1` and `x`.
* `wardropFlow`: All traffic on the congestible edge.
* `splitFlow`: Half the traffic on each edge.

## Main statements

* `isWardrop_wardropFlow`: All traffic on the congestible edge is a Wardrop equilibrium.
* `cost_le_cost`: The equal split has minimum total latency.
* `cost_wardropFlow_eq`: The Wardrop flow costs exactly `4 / 3` times the equal split.

## Tags

pigou, routing games, wardrop equilibrium, price of anarchy
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory

namespace MathEconLibExamples.GameTheory.Pigou

/-- One commodity with unit demand on two single-edge paths. The path and edge `false` has constant
latency `1`; the path and edge `true` has latency equal to its load. -/
def pigou : RoutingGame Unit Bool Bool where
  commodity _ := ()
  edges p := {p}
  demand _ := 1
  latency e x := if e then x else 1

/-- All traffic takes the congestible edge. -/
def wardropFlow : Bool → ℝ := fun p ↦ if p then 1 else 0

/-- Traffic splits equally between the two edges. -/
def splitFlow : Bool → ℝ := fun _ ↦ 1 / 2

/-- Each edge carries the flow of its own path. -/
@[simp] lemma load_eq (f : Bool → ℝ) (e : Bool) : pigou.load f e = f e := by
  simp only [RoutingGame.load, show ∀ p, pigou.edges p = {p} from fun _ ↦ rfl,
    Finset.mem_singleton, Finset.filter_eq, Finset.mem_univ, ite_true, Finset.sum_singleton]

/-- Each path's latency is its edge's latency at the path's flow. -/
@[simp] lemma pathLatency_eq (f : Bool → ℝ) (p : Bool) :
    pigou.pathLatency f p = if p then f p else 1 := by
  simp only [RoutingGame.pathLatency, show pigou.edges p = {p} from rfl, Finset.sum_singleton,
    load_eq]
  rfl

/-- Total latency is the constant edge's flow plus the square of the congestible edge's flow. -/
lemma cost_eq (f : Bool → ℝ) : pigou.cost f = f false + f true * f true := by
  simp only [RoutingGame.cost, Fintype.sum_bool, pathLatency_eq]
  norm_num
  ring

/-- Feasible flows are nonnegative and sum to one. -/
lemma isFeasible_iff (f : Bool → ℝ) :
    pigou.IsFeasible f ↔ 0 ≤ f false ∧ 0 ≤ f true ∧ f false + f true = 1 := by
  simp [RoutingGame.IsFeasible, pigou, and_assoc, add_comm]

/-- Pigou's latencies are affine with nonnegative coefficients. -/
lemma hasAffineLatencies : pigou.HasAffineLatencies := by
  intro e
  cases e
  · exact ⟨0, 1, le_rfl, zero_le_one, fun x ↦ by simp [pigou]⟩
  · exact ⟨1, 0, zero_le_one, le_rfl, fun x ↦ by simp [pigou]⟩

/-- All traffic on the congestible edge is a Wardrop equilibrium: both paths have latency `1`. -/
theorem isWardrop_wardropFlow : pigou.IsWardrop wardropFlow := by
  rw [RoutingGame.isWardrop_iff, isFeasible_iff]
  refine ⟨by norm_num [wardropFlow], fun p q _ _ ↦ ?_⟩
  cases p <;> cases q <;> simp [wardropFlow]

/-- The equal split is feasible. -/
lemma isFeasible_splitFlow : pigou.IsFeasible splitFlow := by
  rw [isFeasible_iff]
  norm_num [splitFlow]

/-- The equal split minimizes total latency over feasible flows. -/
theorem cost_le_cost {g : Bool → ℝ} (hg : pigou.IsFeasible g) :
    pigou.cost splitFlow ≤ pigou.cost g := by
  obtain ⟨-, -, hsum⟩ := (isFeasible_iff g).1 hg
  rw [cost_eq, cost_eq]
  norm_num [splitFlow]
  nlinarith [sq_nonneg (g true - 1 / 2)]

/-- The Wardrop flow costs `4 / 3` times the optimum, so the Roughgarden–Tardos bound is tight. -/
theorem cost_wardropFlow_eq : pigou.cost wardropFlow = 4 / 3 * pigou.cost splitFlow := by
  norm_num [cost_eq, wardropFlow, splitFlow]

/-- The Roughgarden–Tardos bound applied to Pigou's example. -/
example {g : Bool → ℝ} (hg : pigou.IsFeasible g) :
    pigou.cost wardropFlow ≤ 4 / 3 * pigou.cost g :=
  isWardrop_wardropFlow.cost_le_four_thirds_mul hasAffineLatencies hg

end MathEconLibExamples.GameTheory.Pigou
