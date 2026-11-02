/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import MathEconLib.GameTheory.Equilibrium.Problem
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Nonatomic routing games and Wardrop equilibrium

A nonatomic routing game has finitely many paths, each serving one commodity and using a finite set
of edges. Each commodity has a demand, a continuum of infinitesimal drivers who split it among the
commodity's paths. Each edge has a latency depending on its load, the total flow on paths through
the edge. Paths are abstract sets of edges: the price-of-anarchy argument never uses the graph, so
these games are the nonatomic congestion games.

A Wardrop equilibrium is a feasible flow that routes demand only along paths of minimum latency
for their commodity. A single driver does not change any load, so a flow is a Wardrop equilibrium
exactly when, with the flow held fixed, a driver on any used path has no profitable switch.
`RoutingGame.driverProblem` expresses this as an `EquilibriumProblem` whose deviations leave the
flow unchanged, and `RoutingGame.isWardrop_iff` gives the usual minimum-latency condition.

The social cost of a flow is total latency. If every latency `ℓ` satisfies the Pigou-type bound
`y ℓ(x) ≤ y ℓ(y) + β x ℓ(x)` on nonnegative loads, every Wardrop flow `f` and feasible flow `g`
satisfy `(1 - β) C(f) ≤ C(g)`. Affine latencies with nonnegative coefficients satisfy the bound with
`β = 1 / 4`, which gives the Roughgarden–Tardos price-of-anarchy bound `4 / 3`. The comparison is
with every feasible flow, so neither existence of an optimal flow nor existence of a Wardrop
equilibrium is needed.

## Main definitions

* `RoutingGame`: Paths with commodities and edge sets, demands, and edge latencies.
* `RoutingGame.IsFeasible`: Nonnegative path flows meeting each commodity's demand.
* `RoutingGame.load`, `RoutingGame.pathLatency`, and `RoutingGame.cost`.
* `RoutingGame.driverProblem`: One driver's path choice with the flow held fixed.
* `RoutingGame.IsWardrop`: Feasible flows that are equilibria for drivers on every used path.
* `RoutingGame.HasAffineLatencies`: Latencies `a x + b` with `a, b ≥ 0`.

## Main statements

* `RoutingGame.isWardrop_iff`: Wardrop equilibrium is the minimum-latency condition on used paths.
* `RoutingGame.cost_eq_sum_edges`: Total latency is the sum over edges of load times latency.
* `RoutingGame.IsWardrop.cost_le`: The variational inequality for Wardrop flows.
* `RoutingGame.IsWardrop.one_sub_mul_cost_le`: The Pigou-bound price of anarchy.
* `RoutingGame.IsWardrop.cost_le_four_thirds_mul`: The Roughgarden–Tardos bound for affine
  latencies.

## References

* T. Roughgarden and É. Tardos, *How bad is selfish routing?*, J. ACM **49** (2002), 236–259.
* T. Roughgarden, *The price of anarchy is independent of the network topology*, J. Comput. System
  Sci. **67** (2003), 341–364.

## Tags

routing games, wardrop equilibrium, price of anarchy, congestion games
-/

@[expose] public section

open Finset

namespace MathEconLib.GameTheory

/-- A nonatomic routing game with commodities `C`, paths `P`, and edges `E`. -/
structure RoutingGame (C P E : Type*) where
  /-- The commodity served by each path. -/
  commodity : P → C
  /-- The edges used by each path. -/
  edges : P → Finset E
  /-- The total flow of each commodity. -/
  demand : C → ℝ
  /-- The latency of each edge as a function of its load. -/
  latency : E → ℝ → ℝ

namespace RoutingGame

variable {C P E : Type*} [Fintype P] [DecidableEq E]
  (R : RoutingGame C P E) {f g : P → ℝ}

/-- A flow is feasible when it is nonnegative and routes exactly each commodity's demand. -/
def IsFeasible [DecidableEq C] (f : P → ℝ) : Prop :=
  (∀ p, 0 ≤ f p) ∧ ∀ c, ∑ p with R.commodity p = c, f p = R.demand c

/-- The load of an edge is the total flow on paths through it. -/
def load (f : P → ℝ) (e : E) : ℝ :=
  ∑ p with e ∈ R.edges p, f p

/-- The latency of a path is the sum of its edges' latencies at their loads. -/
def pathLatency (f : P → ℝ) (p : P) : ℝ :=
  ∑ e ∈ R.edges p, R.latency e (R.load f e)

/-- The social cost of a flow is total latency experienced by all drivers. -/
def cost (f : P → ℝ) : ℝ :=
  ∑ p, f p * R.pathLatency f p

/-- Feasible flows put nonnegative load on every edge. -/
lemma IsFeasible.load_nonneg [DecidableEq C] {R : RoutingGame C P E} (hf : R.IsFeasible f) (e : E) :
    0 ≤ R.load f e :=
  sum_nonneg fun p _ ↦ hf.1 p

/-- Weighting path sums of edge quantities by a flow weights each edge by its load. -/
lemma sum_mul_sum_edges [Fintype E] (g : P → ℝ) (h : E → ℝ) :
    ∑ p, g p * ∑ e ∈ R.edges p, h e = ∑ e, R.load g e * h e := by
  simp_rw [mul_sum, load, sum_mul]
  exact sum_comm' (by simp)

/-- Path latencies weighted by a flow `g` are edge latencies weighted by the loads of `g`. -/
lemma sum_mul_pathLatency [Fintype E] (f g : P → ℝ) :
    ∑ p, g p * R.pathLatency f p = ∑ e, R.load g e * R.latency e (R.load f e) :=
  R.sum_mul_sum_edges g _

/-- Total latency is the sum over edges of load times latency. -/
lemma cost_eq_sum_edges [Fintype E] (f : P → ℝ) :
    R.cost f = ∑ e, R.load f e * R.latency e (R.load f e) :=
  R.sum_mul_pathLatency f f

/-- The equilibrium problem of one infinitesimal driver. A state is a flow together with the
driver's path. The driver may switch to a path of the same commodity but cannot change the flow,
and receives minus the latency of their path. -/
def driverProblem : EquilibriumProblem ((P → ℝ) × P) Unit ℝ where
  deviation _ s s' := s'.1 = s.1 ∧ R.commodity s'.2 = R.commodity s.2
  value _ s := -R.pathLatency s.1 s.2

/-- A Wardrop equilibrium is a feasible flow at which no infinitesimal driver on a used path gains
by switching paths. -/
def IsWardrop [DecidableEq C] (f : P → ℝ) : Prop :=
  R.IsFeasible f ∧ ∀ p, 0 < f p → R.driverProblem.IsEquilibrium (f, p)

/-- A Wardrop equilibrium is a feasible flow whose used paths have minimum latency among the paths
of their commodity. -/
lemma isWardrop_iff [DecidableEq C] (f : P → ℝ) :
    R.IsWardrop f ↔ R.IsFeasible f ∧
      ∀ p q, 0 < f p → R.commodity q = R.commodity p → R.pathLatency f p ≤ R.pathLatency f q := by
  refine and_congr_right fun _ ↦ ⟨fun h p q hp hq ↦ ?_, fun h p hp _ s hs ↦ ?_⟩
  · exact neg_le_neg_iff.1 (h p hp () (f, q) ⟨rfl, hq⟩)
  · obtain ⟨f', q⟩ := s
    obtain ⟨rfl, hq⟩ := hs
    exact neg_le_neg_iff.2 (h p q hp hq)

/-- Wardrop equilibria are feasible. -/
lemma IsWardrop.isFeasible [DecidableEq C] {R : RoutingGame C P E}
    (hf : R.IsWardrop f) : R.IsFeasible f :=
  hf.1

/-- **Variational inequality.** A Wardrop flow costs at most any feasible flow evaluated at the
Wardrop latencies. -/
theorem IsWardrop.cost_le [DecidableEq C] [Finite C] {R : RoutingGame C P E}
    (hf : R.IsWardrop f) (hg : R.IsFeasible g) :
    R.cost f ≤ ∑ p, g p * R.pathLatency f p := by
  have := Fintype.ofFinite C
  obtain ⟨⟨hf0, hfd⟩, hmin⟩ := (R.isWardrop_iff f).1 hf
  rw [cost, ← sum_fiberwise univ R.commodity, ← sum_fiberwise univ R.commodity]
  refine sum_le_sum fun c _ ↦ ?_
  rcases (univ.filter (R.commodity · = c)).eq_empty_or_nonempty with hs | hs
  · simp [hs]
  set m := (univ.filter (R.commodity · = c)).inf' hs (R.pathLatency f)
  have hfm : ∀ p ∈ univ.filter (R.commodity · = c), f p * R.pathLatency f p = f p * m := by
    intro p hp
    rcases (hf0 p).eq_or_lt with h | h
    · simp [← h]
    refine congrArg _ (le_antisymm (le_inf' _ _ fun q hq ↦ hmin p q h ?_) (inf'_le _ hp))
    rw [(mem_filter.1 hp).2, (mem_filter.1 hq).2]
  calc ∑ p with R.commodity p = c, f p * R.pathLatency f p
      = ∑ p with R.commodity p = c, f p * m := sum_congr rfl hfm
    _ = ∑ p with R.commodity p = c, g p * m := by rw [← sum_mul, ← sum_mul, hfd, hg.2]
    _ ≤ ∑ p with R.commodity p = c, g p * R.pathLatency f p :=
      sum_le_sum fun p hp ↦ mul_le_mul_of_nonneg_left (inf'_le _ hp) (hg.1 p)

/-- **Price of anarchy from a Pigou bound.** If every latency satisfies
`y ℓ(x) ≤ y ℓ(y) + β x ℓ(x)` for nonnegative loads, a Wardrop flow costs at most `(1 - β)⁻¹`
times any feasible flow. -/
theorem IsWardrop.one_sub_mul_cost_le [DecidableEq C] [Finite C] [Finite E]
    {R : RoutingGame C P E} (β : ℝ)
    (hβ : ∀ e x y, 0 ≤ x → 0 ≤ y →
      y * R.latency e x ≤ y * R.latency e y + β * (x * R.latency e x))
    (hf : R.IsWardrop f) (hg : R.IsFeasible g) :
    (1 - β) * R.cost f ≤ R.cost g := by
  have := Fintype.ofFinite E
  have hvi := hf.cost_le hg
  have hpt : ∑ e, R.load g e * R.latency e (R.load f e) ≤
      ∑ e, (R.load g e * R.latency e (R.load g e) +
        β * (R.load f e * R.latency e (R.load f e))) :=
    sum_le_sum fun e _ ↦ hβ e _ _ (hf.isFeasible.load_nonneg e) (hg.load_nonneg e)
  rw [sum_add_distrib, ← mul_sum, ← R.cost_eq_sum_edges, ← R.cost_eq_sum_edges] at hpt
  rw [R.sum_mul_pathLatency] at hvi
  linarith

/-- Every edge latency is affine with nonnegative slope and intercept. -/
def HasAffineLatencies : Prop :=
  ∀ e, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ x, R.latency e x = a * x + b

/-- **Roughgarden–Tardos.** With affine latencies, a Wardrop flow costs at most `4 / 3` times any
feasible flow. -/
theorem IsWardrop.cost_le_four_thirds_mul [DecidableEq C] [Finite C] [Finite E]
    {R : RoutingGame C P E} (hR : R.HasAffineLatencies) (hf : R.IsWardrop f)
    (hg : R.IsFeasible g) :
    R.cost f ≤ 4 / 3 * R.cost g := by
  have h := hf.one_sub_mul_cost_le (1 / 4) (fun e x y hx _ ↦ by
    obtain ⟨a, b, ha, hb, hl⟩ := hR e
    rw [hl, hl]
    nlinarith [mul_nonneg ha (sq_nonneg (y - x / 2)), mul_nonneg hb hx]) hg
  linarith

end RoutingGame

end MathEconLib.GameTheory
