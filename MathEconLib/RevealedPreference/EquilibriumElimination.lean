/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.EquilibriumAxiom
public import MathEconLib.RevealedPreference.EquilibriumAlternative
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.LinearAlgebra.Pi

/-!
# An observable generalized axiom of revealed equilibrium

Every ordinal allocation constraint is encoded as a weak or strict affine row.
Budget and market-clearing equalities use two opposite weak rows. Comparisons
not required by the rank profile become the harmless row `0 ≤ 0`. The same
variable vector supplies every row and every consumer. Fourier–Motzkin
elimination then removes every allocation variable. The resulting axiom is a
finite disjunction over ranks of observable coefficient inequalities, exactly
equivalent to joint GARP and, under the stated premises, utility maximization.
This does not claim an efficient implementation or empirical validation.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators

namespace MathEconLib.RevealedPreference.Equilibrium

namespace OrdinalEncoding

variable {L : ℕ} {I T : Type*}

/-- Coordinates of one joint allocation array. -/
abbrev Coordinates (L : ℕ) (I T : Type*) := I × T × Fin L

/-- One row for every nonnegativity or comparison constraint, and two rows for
each equality. The row type is finite, including empty market dimensions. -/
inductive Row (L : ℕ) (I T : Type*) where
  | nonneg : I → T → Fin L → Row L I T
  | budgetLower : I → T → Row L I T
  | budgetUpper : I → T → Row L I T
  | clearingLower : T → Fin L → Row L I T
  | clearingUpper : T → Fin L → Row L I T
  | comparison : I → T → T → Row L I T
  deriving Fintype

variable [Fintype I] [Fintype T]

/-- A fixed indexing of all latent consumption coordinates. -/
noncomputable def coordinate (i : I) (t : T) (k : Fin L) :
    Fin (Fintype.card (Coordinates L I T)) := Fintype.equivFin (Coordinates L I T) (i, t, k)

/-- Read a joint allocation from a single finite variable vector. -/
noncomputable def decode (z : Fin (Fintype.card (Coordinates L I T)) → ℝ) :
    I → T → Bundle L := fun i t k => z (coordinate i t k)

/-- Store the joint allocation in the same indexing used by every row. -/
noncomputable def encode (x : I → T → Bundle L) :
    Fin (Fintype.card (Coordinates L I T)) → ℝ := fun j =>
  let v := (Fintype.equivFin (Coordinates L I T)).symm j
  x v.1 v.2.1 v.2.2

@[simp] theorem decode_encode (x : I → T → Bundle L) : decode (encode x) = x := by
  funext i t k
  simp [decode, encode, coordinate]

/-- Projection onto a single indexed consumption coordinate. -/
noncomputable def projection (i : I) (t : T) (k : Fin L) :
    (Fin (Fintype.card (Coordinates L I T)) → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj (coordinate i t k)

/-- The left side of each row as a linear functional. -/
noncomputable def rowLinear (D : MarketData L I T) (r : I → ObservationRanks T) :
    Row L I T → ((Fin (Fintype.card (Coordinates L I T)) → ℝ) →ₗ[ℝ] ℝ) := by
  classical
  exact fun row => match row with
  | .nonneg i t k => projection i t k
  | .budgetLower i t => ∑ k, D.price t k • projection i t k
  | .budgetUpper i t => -(∑ k, D.price t k • projection i t k)
  | .clearingLower t k => ∑ i, projection i t k
  | .clearingUpper t k => -(∑ i, projection i t k)
  | .comparison i s t =>
      if r i t ≤ r i s then ∑ k, D.price t k • projection i s k else 0

/-- Observed right side of each row; there are no latent quantities here. -/
noncomputable def rowRhs (D : MarketData L I T) (r : I → ObservationRanks T) :
    Row L I T → ℝ := by
  classical
  exact fun row => match row with
  | .nonneg _ _ _ => 0
  | .budgetLower i t => D.income i t
  | .budgetUpper i t => -D.income i t
  | .clearingLower t k => D.resources t k
  | .clearingUpper t k => -D.resources t k
  | .comparison i s t => if r i t ≤ r i s then D.income i t else 0

/-- Only a strict rank comparison creates a strict affine row. -/
noncomputable def rowStrict (r : I → ObservationRanks T) : Row L I T → Bool := by
  classical
  exact fun row => match row with
  | .comparison i s t => decide (r i t < r i s)
  | _ => false

/-- Express any finite-dimensional linear functional by its coordinate row. -/
theorem linear_eq_dot {n : ℕ} (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) (z : Fin n → ℝ) :
    f z = dot (fun j => f (Pi.single j 1)) z := by
  calc
    f z = f (∑ j, z j • Pi.single j 1) := congrArg f (pi_eq_sum_univ' z)
    _ = ∑ j, z j * f (Pi.single j 1) := by simp
    _ = _ := by simp only [dot, dotProduct, mul_comm]

/-- Matrix presentation of the fixed-rank ordinal system, depending only on
the observed data and the selected finite rank profile. -/
noncomputable def system (D : MarketData L I T) (r : I → ObservationRanks T) :
    FiniteLinearSystem.System (Fintype.card (Coordinates L I T)) (Row L I T) where
  coeff row j := rowLinear D r row (Pi.single j 1)
  rhs := rowRhs D r
  strict := rowStrict r

theorem satisfies_iff (D : MarketData L I T) (r : I → ObservationRanks T)
    (z : Fin (Fintype.card (Coordinates L I T)) → ℝ) :
    FiniteLinearSystem.Satisfies (system D r) z ↔ OrdinalAllocationFeasible D r (decode z) := by
  classical
  have heval (row : Row L I T) :
      dot ((system D r).coeff row) z = rowLinear D r row z := (linear_eq_dot _ z).symm
  constructor
  · intro h
    have hn (i : I) (t : T) (k : Fin L) := (h (.nonneg i t k)).1
    have hbl (i : I) (t : T) := (h (.budgetLower i t)).1
    have hbu (i : I) (t : T) := (h (.budgetUpper i t)).1
    have hcl (t : T) (k : Fin L) := (h (.clearingLower t k)).1
    have hcu (t : T) (k : Fin L) := (h (.clearingUpper t k)).1
    simp only [heval] at hn hbl hbu hcl hcu
    simp only [system, rowRhs, rowLinear, projection, LinearMap.proj_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.neg_apply, smul_eq_mul]
      at hn hbl hbu hcl hcu
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact hn
    · intro i t
      exact le_antisymm (by simpa [decode, dot, dotProduct] using hbu i t)
        (by simpa [decode, dot, dotProduct] using hbl i t)
    · intro t
      ext k
      exact le_antisymm (by simpa [decode, Finset.sum_apply] using hcu t k)
        (by simpa [decode, Finset.sum_apply] using hcl t k)
    · intro i s t hst
      have ht := (h (.comparison i s t)).2
      rw [heval] at ht
      have hle := le_of_lt hst
      simpa [system, rowStrict, rowRhs, rowLinear, hst, hle,
        projection, decode, dot, dotProduct] using ht
    · intro i s t hst
      have ht := (h (.comparison i s t)).1
      rw [heval] at ht
      simpa [system, rowRhs, rowLinear, hst,
        projection, decode, dot, dotProduct] using ht
  · rintro ⟨hx, hstrict, hweak⟩ row
    rw [FiniteLinearSystem.Rel, heval]
    cases row with
    | nonneg i t k =>
      simpa [system, rowRhs, rowStrict, rowLinear, projection, decode] using hx.nonneg i t k
    | budgetLower i t =>
      have hb := hx.budget i t
      change (∑ k, D.price t k * z (coordinate i t k)) = D.income i t at hb
      simp [system, rowRhs, rowStrict, rowLinear, projection, hb]
    | budgetUpper i t =>
      have hb := hx.budget i t
      change (∑ k, D.price t k * z (coordinate i t k)) = D.income i t at hb
      simp [system, rowRhs, rowStrict, rowLinear, projection, hb]
    | clearingLower t k =>
      have hc := congrFun (hx.clearing t) k
      simpa [system, rowRhs, rowStrict, rowLinear, projection, decode, Finset.sum_apply] using hc.ge
    | clearingUpper t k =>
      have hc := congrFun (hx.clearing t) k
      simpa [system, rowRhs, rowStrict, rowLinear, projection, decode, Finset.sum_apply] using hc.le
    | comparison i s t =>
      by_cases hle : r i t ≤ r i s
      · constructor
        · simpa [system, rowRhs, rowLinear, hle, projection, decode, dot, dotProduct]
            using hweak i s t hle
        · intro hs
          have hlt : r i t < r i s := by simpa [system, rowStrict] using hs
          simpa [system, rowRhs, rowLinear, hle, projection, decode, dot, dotProduct]
            using hstrict i s t hlt
      · have hnlt : ¬ r i t < r i s := fun h => hle (le_of_lt h)
        simp [system, rowRhs, rowStrict, rowLinear, hle, hnlt]

/-- The finite linear system is feasible exactly when one common allocation
satisfies all the selected ordinal constraints. -/
theorem feasible_iff (D : MarketData L I T) (r : I → ObservationRanks T) :
    FiniteLinearSystem.Feasible (system D r) ↔ ∃ x, OrdinalAllocationFeasible D r x := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨decode z, (satisfies_iff D r z).mp hz⟩
  · rintro ⟨x, hx⟩
    refine ⟨encode x, (satisfies_iff D r (encode x)).mpr ?_⟩
    simpa only [decode_encode] using hx

end OrdinalEncoding

variable {L : ℕ} {I T : Type*}

/-- A generalized axiom of revealed equilibrium: one of the finitely many
ordinal profiles passes its fully eliminated observable inequalities. This is
a descriptive name for this formalization, not a priority claim or an assertion
that the phrase has a uniquely established meaning in the literature. -/
noncomputable def GeneralizedAxiomOfRevealedEquilibrium [Fintype I] [Fintype T]
    (D : MarketData L I T) : Prop :=
  ∃ r : I → ObservationRanks T,
    FiniteLinearSystem.EliminationCondition (OrdinalEncoding.system D r)

/-- Elimination removes all latent real quantities from the ordinal test. -/
theorem hasOrdinalAllocation_iff_generalizedAxiomOfRevealedEquilibrium
    [Fintype I] [Fintype T] (D : MarketData L I T) :
    HasOrdinalAllocation D ↔ GeneralizedAxiomOfRevealedEquilibrium D := by
  constructor
  · rintro ⟨r, x, hx⟩
    exact ⟨r, (FiniteLinearSystem.feasible_iff_eliminationCondition _).mp
      ((OrdinalEncoding.feasible_iff D r).mpr ⟨x, hx⟩)⟩
  · rintro ⟨r, hr⟩
    obtain ⟨x, hx⟩ := (OrdinalEncoding.feasible_iff D r).mp
      ((FiniteLinearSystem.feasible_iff_eliminationCondition _).mpr hr)
    exact ⟨r, x, hx⟩

/-- The observable axiom is exactly joint GARP, even for empty observations
and without sign assumptions on prices. -/
theorem hasGARPAllocation_iff_generalizedAxiomOfRevealedEquilibrium
    [Fintype I] [Fintype T] (D : MarketData L I T) :
    HasGARPAllocation D ↔ GeneralizedAxiomOfRevealedEquilibrium D :=
  (hasGARPAllocation_iff_hasOrdinalAllocation D).trans
    (hasOrdinalAllocation_iff_generalizedAxiomOfRevealedEquilibrium D)

/-- The eliminated observable axiom characterizes regular utility-maximizing
equilibrium. All economic regularity assumptions are explicit. -/
theorem hasRegularEquilibriumRationalization_iff_generalizedAxiomOfRevealedEquilibrium
    [Fintype I] [Fintype T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) :
    HasRegularEquilibriumRationalization D ↔ GeneralizedAxiomOfRevealedEquilibrium D :=
  (hasRegularEquilibriumRationalization_iff_hasOrdinalAllocation D hp).trans
    (hasOrdinalAllocation_iff_generalizedAxiomOfRevealedEquilibrium D)

/-- The same observable test characterizes increasing utility maximization,
without presupposing concavity or continuity of the initial rationalization. -/
theorem hasIncreasingEquilibriumRationalization_iff_generalizedAxiomOfRevealedEquilibrium
    [Fintype I] [Fintype T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) :
    HasIncreasingEquilibriumRationalization D ↔ GeneralizedAxiomOfRevealedEquilibrium D :=
  (hasIncreasingEquilibriumRationalization_iff_hasRegularEquilibriumRationalization D hp).trans
    (hasRegularEquilibriumRationalization_iff_generalizedAxiomOfRevealedEquilibrium D hp)

/-- Under positive prices and a nonzero commodity dimension, the observable
axiom also characterizes locally nonsatiated utility maximization. -/
theorem hasLocallyNonsatiatedEquilibriumRationalization_iff_generalizedAxiomOfRevealedEquilibrium
    [Fintype I] [Fintype T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) (hL : 0 < L) :
    HasLocallyNonsatiatedEquilibriumRationalization D ↔ GeneralizedAxiomOfRevealedEquilibrium D :=
  (hasLocallyNonsatiatedEquilibriumRationalization_iff_hasAfriatAllocation D hp hL).trans
    ((hasGARPAllocation_iff_hasAfriatAllocation D).symm.trans
      (hasGARPAllocation_iff_generalizedAxiomOfRevealedEquilibrium D))

end MathEconLib.RevealedPreference.Equilibrium
