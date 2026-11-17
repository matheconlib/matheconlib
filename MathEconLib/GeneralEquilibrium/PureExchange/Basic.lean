/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.Basic
public import MathEconLib.Preferences.Complete
public import MathEconLib.Choice.Maximizers
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Finite pure-exchange budgets and Walrasian equilibrium

Households rank the nonnegative consumption orthant using the existing complete-preference
primitive. Full endowment budgets and demand are meaningful without continuity, convexity,
or monotonicity. Demand reuses `MathEconLib.Choice.maximizers`, so membership includes both
feasibility and greatest-preference optimality, including ties.

`IsWalrasianEquilibrium` states nonnegative endowments, nonnegative nonzero prices, household
budget feasibility and full-budget optimality, and exact market clearing. Normalization,
strictly positive prices, exhausted budgets, and assumptions sufficient for existence are
separate. `PreferenceRegularity` is an ordinary proposition on supplied preferences, not a
new preference carrier or an inference class.

This module concerns finite pure exchange on the nonnegative orthant. It does not introduce
a general production or abstract-economy framework.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Topology
open MathEconLib.Preferences MathEconLib.RevealedPreference

namespace MathEconLib.GeneralEquilibrium.PureExchange

/-- The household's consumption alternatives, with nonnegativity retained in the carrier. -/
abbrev Orthant (L : ℕ) := {x : Bundle L // Nonnegative x}

variable {L : ℕ}

/-- The full, untruncated endowment budget on the consumption orthant. -/
def budgetSet (e p : Bundle L) : Set (Orthant L) := {x | dot p x.val ≤ dot p e}

/-- Every greatest feasible bundle under the supplied complete preference. -/
def demand (P : CompletePreference (Orthant L)) (e p : Bundle L) : Set (Orthant L) :=
  Choice.maximizers P.toPreference (budgetSet e p)

/-- Demand retains feasibility and compares against every affordable alternative. -/
@[simp] theorem mem_demand (P : CompletePreference (Orthant L)) (e p : Bundle L)
    (x : Orthant L) :
    x ∈ demand P e p ↔ x ∈ budgetSet e p ∧ ∀ y ∈ budgetSet e p, P.le y x := Iff.rfl

/-- Sufficient preference regularity for the existence theorem. Continuity uses the two
separate relatively closed contours; convexity is ordinary upper-contour convexity. -/
structure PreferenceRegularity (P : CompletePreference (Orthant L)) : Prop where
  /-- Weakly better alternatives form a closed subset of the orthant. -/
  closed_upper : ∀ x, IsClosed {y | P.le x y}
  /-- Weakly worse alternatives form a closed subset of the orthant. -/
  closed_lower : ∀ x, IsClosed {y | P.le y x}
  /-- Weak upper contours are convex in commodity space. -/
  convex_upper : ∀ x, Convex ℝ {y : Bundle L | ∃ hy : Nonnegative y, P.le x ⟨y, hy⟩}
  /-- A coordinatewise increase with at least one strict increase is strictly preferred. -/
  strong_mono : ∀ {x y : Orthant L}, x.val < y.val → P.le x y ∧ ¬P.le y x

/-- A Walrasian equilibrium of a finite pure-exchange economy. Normalization and
strict positivity are not constitutive: zero-priced goods are allowed here. -/
structure IsWalrasianEquilibrium {I : Type*} [Fintype I]
    (e : I → Bundle L) (P : I → CompletePreference (Orthant L))
    (p : Bundle L) (x : I → Orthant L) : Prop where
  /-- Physical endowments are nonnegative. -/
  endowment_nonneg : ∀ i, Nonnegative (e i)
  /-- Prices are nonnegative. -/
  price_nonneg : Nonnegative p
  /-- The entire price vector is not zero. -/
  price_ne_zero : p ≠ 0
  /-- Every selected nonnegative bundle is affordable at endowment income. -/
  budget_feasible : ∀ i, x i ∈ budgetSet (e i) p
  /-- Every affordable alternative is weakly worse than the selected bundle. -/
  optimal : ∀ i y, y ∈ budgetSet (e i) p → (P i).le y (x i)
  /-- Every commodity clears exactly. -/
  clearing : (∑ i, (x i).val) = ∑ i, e i

/-- The solution predicate expressed through the canonical feasible-maximizer correspondence. -/
theorem isWalrasianEquilibrium_iff {I : Type*} [Fintype I]
    (e : I → Bundle L) (P : I → CompletePreference (Orthant L))
    (p : Bundle L) (x : I → Orthant L) :
    IsWalrasianEquilibrium e P p x ↔
      (∀ i, Nonnegative (e i)) ∧ Nonnegative p ∧ p ≠ 0 ∧
      (∀ i, x i ∈ demand (P i) (e i) p) ∧ (∑ i, (x i).val) = ∑ i, e i := by
  constructor
  · intro h
    exact ⟨h.endowment_nonneg, h.price_nonneg, h.price_ne_zero,
      fun i => ⟨h.budget_feasible i, h.optimal i⟩, h.clearing⟩
  · rintro ⟨he, hp, hp0, hx, hc⟩
    exact ⟨he, hp, hp0, fun i => (hx i).1, fun i => (hx i).2, hc⟩

namespace Internal

/-- The temporary compact consumption domain used by the existence proof. -/
def consumptionBox (M : Bundle L) : Set (Bundle L) := Set.Icc 0 M

/-- The ambient form of the full nonnegative endowment budget. -/
def fullBudget (e p : Bundle L) : Set (Bundle L) :=
  {x | Nonnegative x ∧ dot p x ≤ dot p e}

/-- Budget feasibility inside the temporary consumption box. -/
def cappedBudget (e M p : Bundle L) : Set (Bundle L) :=
  {x | x ∈ consumptionBox M ∧ dot p x ≤ dot p e}

/-- Normalized nonnegative prices, including boundary faces. -/
def priceSimplex : Set (Bundle L) := {p | Nonnegative p ∧ ∑ k, p k = 1}

/-- A ceiling strictly above aggregate resources in every coordinate. -/
def resourceCap {I : Type*} [Fintype I] (e : I → Bundle L) : Bundle L := (∑ i, e i) + 1

end Internal
end MathEconLib.GeneralEquilibrium.PureExchange
