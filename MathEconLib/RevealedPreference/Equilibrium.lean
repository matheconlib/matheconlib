/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.LocalNonsatiation

/-!
# Finite exchange-equilibrium rationalization

Observed prices, individual incomes, and aggregate resources admit one common
profile of regular utility functions exactly when there is one joint allocation
array satisfying nonnegativity, budget exhaustion, market clearing, and each
consumer's Afriat inequalities. Individual consumptions are latent. The allocation
array is shared across all comparisons and all observations.

This formalizes the finite equilibrium-inequality characterization in Brown and
Matzkin, Theorem 2 of the August 1995 Cowles discussion-paper version. Utilities
are continuous, concave, and strictly increasing; their maximization is on the
nonnegative consumption orthant. The constructed utilities extend to the whole
bundle space. The ordinary utility variant states local nonsatiation on the consumption orthant
explicitly and derives budget exhaustion from weak budget feasibility. This resolves
the source's ambiguous use of “monotone”: weak monotonicity alone would admit
constant utilities and cannot imply positive-multiplier Afriat inequalities.
We do not assert smoothness, strict
concavity, unique demand, quantifier elimination, or an observable-only axiom.
Prices need not be normalized. This is a characterization of finite observed
price equilibria, not an existence theorem at unobserved endowments.

## References

Donald J. Brown and Rosa L. Matzkin (1996), *Testable Restrictions on the
Equilibrium Manifold*, Econometrica **64**(6), 1249–1262.
[DOI: 10.2307/2171830](https://doi.org/10.2307/2171830).
[August 1995 Cowles discussion paper 1109](https://cowles.yale.edu/sites/default/files/files/pub/d11/d1109.pdf).
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace MathEconLib.RevealedPreference.Equilibrium

/-- Observed exchange-market data; individual consumption is not observed.
Sign restrictions and accounting consistency are separate properties. -/
structure MarketData (L : ℕ) (I T : Type*) where
  price : T → Bundle L
  income : I → T → ℝ
  resources : T → Bundle L

variable {L : ℕ} {I T : Type*}

/-- A joint consumption array satisfying nonnegativity, exhausted individual
budgets, and exact market clearing in every observation. -/
structure AllocationFeasible [Fintype I] (D : MarketData L I T)
    (x : I → T → Bundle L) : Prop where
  nonneg : ∀ i t, Nonnegative (x i t)
  budget : ∀ i t, dot (D.price t) (x i t) = D.income i t
  clearing : ∀ t, ∑ i, x i t = D.resources t

/-- Individual exhausted budgets and market clearing imply aggregate accounting. -/
theorem AllocationFeasible.budget_adding_up [Fintype I] {D : MarketData L I T}
    {x : I → T → Bundle L} (hx : AllocationFeasible D x) (t : T) :
    ∑ i, D.income i t = dot (D.price t) (D.resources t) := by
  calc
    ∑ i, D.income i t = ∑ i, dot (D.price t) (x i t) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hx.budget i t).symm
    _ = dot (D.price t) (∑ i, x i t) := by
      simp only [dot, dotProduct, Finset.sum_apply, Finset.mul_sum]
      exact Finset.sum_comm
    _ = dot (D.price t) (D.resources t) := congrArg (dot (D.price t)) (hx.clearing t)

/-- Every consumer maximizes the same utility function across all observations,
among all nonnegative bundles affordable at observed income. -/
def UtilityMaximizes (D : MarketData L I T) (x : I → T → Bundle L)
    (u : I → Utility L) : Prop :=
  ∀ i t y, Nonnegative y → dot (D.price t) y ≤ D.income i t →
    u i y ≤ u i (x i t)

/-- Ordinary utility maximization with local nonsatiation on the consumption
orthant. Feasibility initially imposes weak budgets; exhaustion is a theorem. -/
def HasLocallyNonsatiatedEquilibriumRationalization [Fintype I]
    (D : MarketData L I T) : Prop :=
  ∃ (x : I → T → Bundle L) (u : I → Utility L),
    (∀ i t, Nonnegative (x i t)) ∧
    (∀ i t, dot (D.price t) (x i t) ≤ D.income i t) ∧
    (∀ t, ∑ i, x i t = D.resources t) ∧
    (∀ i, LocallyNonsatiatedOnNonnegative (u i)) ∧ UtilityMaximizes D x u

/-- Local nonsatiation turns affordable maximizing allocations into allocations
with exhausted budgets, without any price-sign or dimension assumption. -/
theorem allocationFeasible_of_locallyNonsatiated [Fintype I]
    (D : MarketData L I T) (x : I → T → Bundle L) (u : I → Utility L)
    (hnonneg : ∀ i t, Nonnegative (x i t))
    (hbudget : ∀ i t, dot (D.price t) (x i t) ≤ D.income i t)
    (hclearing : ∀ t, ∑ i, x i t = D.resources t)
    (hlns : ∀ i, LocallyNonsatiatedOnNonnegative (u i))
    (hmax : UtilityMaximizes D x u) : AllocationFeasible D x where
  nonneg := hnonneg
  budget := fun i t => budget_exhaustion_of_locallyNonsatiated (hlns i)
    (D.price t) (x i t) (D.income i t) (hnonneg i t) (hbudget i t) (hmax i t)
  clearing := hclearing

/-- Equilibrium rationalization by strictly increasing ordinary utilities.
Budget exhaustion and market clearing are supplied by the joint allocation. -/
def HasIncreasingEquilibriumRationalization [Fintype I] (D : MarketData L I T) : Prop :=
  ∃ x u, AllocationFeasible D x ∧ (∀ i, StrictlyIncreasing (u i)) ∧
    UtilityMaximizes D x u

/-- Equilibrium rationalization by continuous, concave, strictly increasing utilities. -/
def HasRegularEquilibriumRationalization [Fintype I] (D : MarketData L I T) : Prop :=
  ∃ x u, AllocationFeasible D x ∧
    (∀ i, Continuous (u i) ∧ ConcaveOn ℝ Set.univ (u i) ∧ StrictlyIncreasing (u i)) ∧
    UtilityMaximizes D x u

/-- One jointly feasible allocation array whose consumer datasets all satisfy GARP.
This retains latent consumptions; it is not an observable-only axiom. -/
def HasGARPAllocation [Fintype I] (D : MarketData L I T) : Prop :=
  ∃ x, AllocationFeasible D x ∧ ∀ i, GraphGARP D.price (x i)

/-- Brown–Matzkin's finite equilibrium inequalities, retaining their latent
consumptions, utility levels, and positive marginal-utility multipliers. -/
def HasAfriatAllocation [Fintype I] (D : MarketData L I T) : Prop :=
  ∃ (x : I → T → Bundle L) (U lam : I → T → ℝ), AllocationFeasible D x ∧
    ∀ i, PositiveMultipliers (lam i) ∧ AfriatInequalities (U i) (lam i) D.price (x i)

/-- The consumer dataset induced by one feasible allocation array. -/
def consumerDataset [Fintype I] (D : MarketData L I T)
    (hp : ∀ t k, 0 < D.price t k) (x : I → T → Bundle L)
    (hx : AllocationFeasible D x) (i : I) : Dataset L T where
  price := D.price
  choice := x i
  price_pos := hp
  choice_nonneg := hx.nonneg i

/-- Exhaustion identifies the income budget with the consumer dataset's budget. -/
theorem utilityMaximizes_iff [Fintype I] (D : MarketData L I T)
    (hp : ∀ t k, 0 < D.price t k) (x : I → T → Bundle L)
    (hx : AllocationFeasible D x) (u : I → Utility L) :
    UtilityMaximizes D x u ↔ ∀ i, UtilityRationalizes (consumerDataset D hp x hx i) (u i) := by
  constructor
  · intro h i t y hy
    exact h i t y hy.1 (by simpa [expenditure, consumerDataset, hx.budget i t] using hy.2)
  · intro h i t y hy hbudget
    apply h i t y
    exact ⟨hy, by simpa [expenditure, consumerDataset, hx.budget i t] using hbudget⟩

/-- Joint GARP and joint Afriat feasibility are equivalent, even for empty data
and without positivity assumptions on observed prices. -/
theorem hasGARPAllocation_iff_hasAfriatAllocation [Fintype I] [Finite T]
    (D : MarketData L I T) : HasGARPAllocation D ↔ HasAfriatAllocation D := by
  classical
  constructor
  · rintro ⟨x, hx, hG⟩
    have hcert := fun i => (graphGARP_iff_exists_afriatInequalities D.price (x i)).mp (hG i)
    choose U lam hpos hA using hcert
    exact ⟨x, U, lam, hx, fun i => ⟨hpos i, hA i⟩⟩
  · rintro ⟨x, U, lam, hx, hcert⟩
    exact ⟨x, hx, fun i => (graphGARP_iff_exists_afriatInequalities D.price (x i)).mpr
      ⟨U i, lam i, (hcert i).1, (hcert i).2⟩⟩

/-- Increasing utility maximization forces GARP for the same joint allocation. -/
theorem hasGARPAllocation_of_hasIncreasingEquilibriumRationalization [Fintype I]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k)
    (h : HasIncreasingEquilibriumRationalization D) : HasGARPAllocation D := by
  obtain ⟨x, u, hx, hinc, hmax⟩ := h
  exact ⟨x, hx, fun i => garp_of_strictlyIncreasing_utilityRationalization
    (consumerDataset D hp x hx i) (u i) (hinc i)
    ((utilityMaximizes_iff D hp x hx u).mp hmax i)⟩

/-- The finite consumer theorem applied independently to each consumer, preserving
one common array of allocations and hence the market-clearing constraints. -/
theorem hasRegularEquilibriumRationalization_of_hasGARPAllocation
    [Fintype I] [Finite T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k)
    (h : HasGARPAllocation D) : HasRegularEquilibriumRationalization D := by
  classical
  obtain ⟨x, hx, hG⟩ := h
  have hreg := fun i => hasRegularUtilityRationalization_of_garp
    (consumerDataset D hp x hx i) (hG i)
  choose u hcont hconc hinc hrat using hreg
  exact ⟨x, u, hx, fun i => ⟨hcont i, hconc i, hinc i⟩,
    (utilityMaximizes_iff D hp x hx u).mpr hrat⟩

/-- Forgetting continuity and concavity preserves utility-maximizing equilibrium. -/
theorem HasRegularEquilibriumRationalization.to_increasing [Fintype I]
    {D : MarketData L I T} (h : HasRegularEquilibriumRationalization D) :
    HasIncreasingEquilibriumRationalization D := by
  obtain ⟨x, u, hx, hreg, hmax⟩ := h
  exact ⟨x, u, hx, fun i => (hreg i).2.2, hmax⟩

/-- Finite exchange observations admit regular utilities exactly when the
Brown–Matzkin equilibrium inequalities have a joint solution. -/
theorem hasRegularEquilibriumRationalization_iff_hasAfriatAllocation
    [Fintype I] [Finite T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) :
    HasRegularEquilibriumRationalization D ↔ HasAfriatAllocation D := by
  rw [← hasGARPAllocation_iff_hasAfriatAllocation D]
  exact ⟨fun h => hasGARPAllocation_of_hasIncreasingEquilibriumRationalization
    D hp h.to_increasing, hasRegularEquilibriumRationalization_of_hasGARPAllocation D hp⟩

/-- Strictly increasing rationalizations can be replaced by regular utilities
without changing the observed market data. -/
theorem hasIncreasingEquilibriumRationalization_iff_hasRegularEquilibriumRationalization
    [Fintype I] [Finite T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) :
    HasIncreasingEquilibriumRationalization D ↔ HasRegularEquilibriumRationalization D :=
  ⟨fun h => hasRegularEquilibriumRationalization_of_hasGARPAllocation D hp
      (hasGARPAllocation_of_hasIncreasingEquilibriumRationalization D hp h),
    HasRegularEquilibriumRationalization.to_increasing⟩

/-- Local nonsatiation and ordinary budget maximization yield a single jointly
feasible GARP allocation. No continuity or concavity of the initial utilities is assumed. -/
theorem hasGARPAllocation_of_hasLocallyNonsatiatedEquilibriumRationalization [Fintype I]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k)
    (h : HasLocallyNonsatiatedEquilibriumRationalization D) : HasGARPAllocation D := by
  obtain ⟨x, u, hnonneg, hbudget, hclearing, hlns, hmax⟩ := h
  have hx := allocationFeasible_of_locallyNonsatiated
    D x u hnonneg hbudget hclearing hlns hmax
  exact ⟨x, hx, fun i => garp_of_locallyNonsatiated_utilityRationalization
    (consumerDataset D hp x hx i) (u i) (hlns i)
    ((utilityMaximizes_iff D hp x hx u).mp hmax i)⟩

/-- Regular rationalizing utilities are locally nonsatiated when a commodity exists. -/
theorem HasRegularEquilibriumRationalization.to_locallyNonsatiated [Fintype I]
    {D : MarketData L I T} (h : HasRegularEquilibriumRationalization D) (hL : 0 < L) :
    HasLocallyNonsatiatedEquilibriumRationalization D := by
  obtain ⟨x, u, hx, hreg, hmax⟩ := h
  exact ⟨x, u, hx.nonneg, fun i t => (hx.budget i t).le, hx.clearing,
    fun i => locallyNonsatiatedOnNonnegative_of_strictlyIncreasing hL (hreg i).2.2, hmax⟩

/-- Finite ordinary locally nonsatiated equilibrium rationalization is equivalent
to the Brown–Matzkin equilibrium inequalities. This states the nonsatiation
premise explicitly and imposes it only on the nonnegative consumption domain. -/
theorem hasLocallyNonsatiatedEquilibriumRationalization_iff_hasAfriatAllocation
    [Fintype I] [Finite T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) (hL : 0 < L) :
    HasLocallyNonsatiatedEquilibriumRationalization D ↔ HasAfriatAllocation D := by
  constructor
  · intro h
    exact (hasGARPAllocation_iff_hasAfriatAllocation D).mp
      (hasGARPAllocation_of_hasLocallyNonsatiatedEquilibriumRationalization D hp h)
  · intro h
    exact HasRegularEquilibriumRationalization.to_locallyNonsatiated
      ((hasRegularEquilibriumRationalization_iff_hasAfriatAllocation D hp).mpr h) hL

end MathEconLib.RevealedPreference.Equilibrium
