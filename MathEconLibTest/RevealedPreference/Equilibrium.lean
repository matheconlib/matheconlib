/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLib.RevealedPreference

/-!
# Finite exchange-equilibrium public API checks

The contracts keep joint allocations inside each existential. Finite observations
alone suffice for certificate equivalence; positive prices and nonempty observations
are used for the regular utility construction. This module imports only the public
umbrella. Empty observations and zero goods exercise boundaries; numerical examples
are checked separately in `EquilibriumExamples`.
-/

set_option linter.privateModule false

open scoped BigOperators
open MathEconLib MathEconLib.RevealedPreference MathEconLib.RevealedPreference.Equilibrium

example {L : ℕ} {I T : Type*} [Fintype I] (D : MarketData L I T)
    (x : I → T → Bundle L) (u : I → Utility L) :
    UtilityMaximizes D x u ↔
      ∀ i t y, Nonnegative y → dot (D.price t) y ≤ D.income i t →
        u i y ≤ u i (x i t) := Iff.rfl

example {L : ℕ} {I T : Type*} [Fintype I] (D : MarketData L I T)
    (x : I → T → Bundle L) (hx : AllocationFeasible D x) (t : T) :
    ∑ i, D.income i t = dot (D.price t) (D.resources t) := hx.budget_adding_up t

example {L : ℕ} {I T : Type*} [Fintype I] (D : MarketData L I T) :
    HasLocallyNonsatiatedEquilibriumRationalization D ↔
      ∃ (x : I → T → Bundle L) (u : I → Utility L),
        (∀ i t, Nonnegative (x i t)) ∧
        (∀ i t, dot (D.price t) (x i t) ≤ D.income i t) ∧
        (∀ t, ∑ i, x i t = D.resources t) ∧
        (∀ i, LocallyNonsatiatedOnNonnegative (u i)) ∧
        (∀ i t y, Nonnegative y → dot (D.price t) y ≤ D.income i t →
          u i y ≤ u i (x i t)) := Iff.rfl

example {L : ℕ} {I T : Type*} [Fintype I] (D : MarketData L I T) :
    HasGARPAllocation D ↔
      ∃ x, AllocationFeasible D x ∧ ∀ i, GraphGARP D.price (x i) := Iff.rfl

example {L : ℕ} {I T : Type*} [Fintype I] (D : MarketData L I T) :
    HasAfriatAllocation D ↔
      ∃ (x : I → T → Bundle L) (U lam : I → T → ℝ), AllocationFeasible D x ∧
        ∀ i, PositiveMultipliers (lam i) ∧ AfriatInequalities (U i) (lam i) D.price (x i) :=
  Iff.rfl

example {L : ℕ} {I T : Type*} [Fintype I] [Finite T] (D : MarketData L I T) :
    HasGARPAllocation D ↔ HasAfriatAllocation D :=
  hasGARPAllocation_iff_hasAfriatAllocation D

example {L : ℕ} {I T : Type*} [Fintype I] (D : MarketData L I T)
    (hp : ∀ t k, 0 < D.price t k) :
    HasIncreasingEquilibriumRationalization D → HasGARPAllocation D :=
  hasGARPAllocation_of_hasIncreasingEquilibriumRationalization D hp

example {L : ℕ} {I T : Type*} [Fintype I] [Finite T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) :
    HasRegularEquilibriumRationalization D ↔ HasAfriatAllocation D :=
  hasRegularEquilibriumRationalization_iff_hasAfriatAllocation D hp

example {L : ℕ} {I T : Type*} [Fintype I] [Finite T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) :
    HasIncreasingEquilibriumRationalization D ↔ HasRegularEquilibriumRationalization D :=
  hasIncreasingEquilibriumRationalization_iff_hasRegularEquilibriumRationalization D hp

example {L : ℕ} {I T : Type*} [Fintype I] [Finite T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) (hL : 0 < L) :
    HasLocallyNonsatiatedEquilibriumRationalization D ↔ HasAfriatAllocation D :=
  hasLocallyNonsatiatedEquilibriumRationalization_iff_hasAfriatAllocation D hp hL

-- Fully observable contracts retain only finite rank and eliminated-row quantification.
example {L : ℕ} {I T : Type*} [Fintype I] [Fintype T] (D : MarketData L I T) :
    GARE D ↔
      ∃ r : I → ObservationRanks T,
        FiniteLinearSystem.EliminationCondition (OrdinalEncoding.system D r) := Iff.rfl

example {L : ℕ} {I T : Type*} [Fintype I] [Fintype T] (D : MarketData L I T) :
    HasGARPAllocation D ↔ GARE D :=
  hasGARPAllocation_iff_gare D

example {L : ℕ} {I T : Type*} [Fintype I] [Fintype T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) :
    HasRegularEquilibriumRationalization D ↔ GARE D :=
  hasRegularEquilibriumRationalization_iff_gare D hp

example {L : ℕ} {I T : Type*} [Fintype I] [Fintype T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) (hL : 0 < L) :
    HasLocallyNonsatiatedEquilibriumRationalization D ↔
      GARE D :=
  hasLocallyNonsatiatedEquilibriumRationalization_iff_gare
    D hp hL

example {L : ℕ} {u : Utility L} (hlns : LocallyNonsatiatedOnNonnegative u)
    (p x : Bundle L) (m : ℝ) (hx : Nonnegative x) (hbudget : dot p x ≤ m)
    (hmax : ∀ y, Nonnegative y → dot p y ≤ m → u y ≤ u x) : dot p x = m :=
  budget_exhaustion_of_locallyNonsatiated hlns p x m hx hbudget hmax

-- Exact bridge contracts remain available from the public umbrella alone.
example {L : ℕ} {T : Type*} [Fintype T] (p q : T → Bundle L) :
    GraphGARP p q ↔ ∃ r : ObservationRanks T, RankCompatible p q (fun t => (r t).val) :=
  graphGARP_iff_exists_observationRanks p q

example {L : ℕ} {I T : Type*} [Fintype I] [Fintype T]
    (D : MarketData L I T) (r : I → ObservationRanks T)
    (z : Fin (Fintype.card (OrdinalEncoding.Coordinates L I T)) → ℝ) :
    FiniteLinearSystem.Satisfies (OrdinalEncoding.system D r) z ↔
      OrdinalAllocationFeasible D r (OrdinalEncoding.decode z) :=
  OrdinalEncoding.satisfies_iff D r z

example {n : ℕ} {R : Type*} [Finite R]
    (S : FiniteLinearSystem.System (n + 1) R) (x : Fin n → ℝ) :
    FiniteLinearSystem.Satisfies (FiniteLinearSystem.eliminate S) x ↔
      ∃ t : ℝ, FiniteLinearSystem.Satisfies S (Fin.cons t x) :=
  FiniteLinearSystem.satisfies_eliminate_iff S x

example {L : ℕ} {I T : Type*} [Fintype I] [Fintype T] (D : MarketData L I T) :
    GeneralizedAxiomOfRevealedEquilibrium D ↔ GARE D := Iff.rfl

-- Empty observations still admit a joint Afriat certificate.
example {L : ℕ} {I : Type*} [Fintype I] (D : MarketData L I PEmpty) :
    HasAfriatAllocation D := by
  refine ⟨(fun _ t => t.elim), (fun _ t => t.elim), (fun _ t => t.elim), ?_, ?_⟩
  · exact ⟨fun _ t => t.elim, fun _ t => t.elim, fun t => t.elim⟩
  · intro i
    exact ⟨fun t => t.elim, fun s => s.elim⟩

-- With zero goods, zero income is compatible with regular rationalization.
example : HasRegularEquilibriumRationalization
    ({ price := fun _ => 0, income := fun _ _ => 0, resources := fun _ => 0 } :
      MarketData 0 Unit Unit) := by
  apply (hasRegularEquilibriumRationalization_iff_hasAfriatAllocation _
    (fun _ k => Fin.elim0 k)).mpr
  refine ⟨(fun _ _ => 0), (fun _ _ => 0), (fun _ _ => 1), ?_, ?_⟩
  · constructor
    · intro i t k
      exact Fin.elim0 k
    · intro i t
      simp [dot, dotProduct]
    · intro t
      simp
  · intro i
    constructor
    · intro t
      norm_num
    · intro s t
      simp [globalAfriatSupport, dot, dotProduct]

-- Zero goods cannot support local nonsatiation: its domain has just one bundle.
example (u : Utility 0) : ¬ LocallyNonsatiatedOnNonnegative u := by
  intro h
  obtain ⟨y, _, _, hy⟩ := h 0 (fun k => Fin.elim0 k) 1 zero_lt_one
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [hy0] at hy
  exact (lt_irrefl (u 0)) hy

open FiniteLinearSystem

example {n : ℕ} {R : Type*} [Fintype R] (S : System n R) :
    (∃ x : Fin n → ℝ, ∀ r,
      S.rhs r ≤ dotProduct (S.coeff r) x ∧
        (S.strict r = true → S.rhs r < dotProduct (S.coeff r) x)) ↔ EliminationCondition S :=
  feasible_iff_eliminationCondition S

-- A strict lower bound and a coincident weak upper bound cannot share a point.
example : ¬ EliminationCondition
    ({ coeff := ![![1], ![-1]], rhs := ![0, 0], strict := ![true, false] } :
      System 1 (Fin 2)) := by
  intro h
  obtain ⟨x, hx⟩ := (feasible_iff_eliminationCondition _).mpr h
  have hpos := (hx 0).2 rfl
  have hnonpos := (hx 1).1
  norm_num [dot, dotProduct, Fin.sum_univ_succ] at hpos hnonpos
  linarith

-- Two coincident closed bounds do share their endpoint.
example : EliminationCondition
    ({ coeff := ![![1], ![-1]], rhs := ![0, 0], strict := ![false, false] } :
      System 1 (Fin 2)) := by
  apply (feasible_iff_eliminationCondition _).mp
  refine ⟨0, ?_⟩
  intro r
  fin_cases r <;> norm_num [FiniteLinearSystem.Rel, dot, dotProduct, Fin.sum_univ_succ]

-- Two open bounds with a positive gap have an interior solution.
example : EliminationCondition
    ({ coeff := ![![1], ![-1]], rhs := ![0, -1], strict := ![true, true] } :
      System 1 (Fin 2)) := by
  apply (feasible_iff_eliminationCondition _).mp
  refine ⟨fun _ => 1 / 2, ?_⟩
  intro r
  fin_cases r <;> norm_num [FiniteLinearSystem.Rel, dot, dotProduct, Fin.sum_univ_succ]

-- A zero-dimensional strict zero row is inconsistent.
example : ¬ EliminationCondition
    ({ coeff := fun _ => 0, rhs := fun _ => 0, strict := fun _ => true } :
      System 0 Unit) := by
  intro h
  obtain ⟨x, hx⟩ := (feasible_iff_eliminationCondition _).mpr h
  have himpossible := (hx ()).2 rfl
  norm_num [dot, dotProduct] at himpossible

-- Its weak counterpart imposes no restriction.
example : EliminationCondition
    ({ coeff := fun _ => 0, rhs := fun _ => 0, strict := fun _ => false } :
      System 0 Unit) := by
  apply (feasible_iff_eliminationCondition _).mp
  exact ⟨0, fun _ => by simp [FiniteLinearSystem.Rel, dotProduct]⟩

-- No rows constrain any coordinate, including after repeated elimination.
example (n : ℕ) (S : System n PEmpty) : EliminationCondition S := by
  apply (feasible_iff_eliminationCondition S).mp
  exact ⟨0, fun r => r.elim⟩
