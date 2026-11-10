/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Observed consumer data and expenditure geometry

Bundles lie in `Fin L → ℝ`. Budgets restrict alternatives to the nonnegative orthant.
`Dataset` retains strictly positive prices and nonnegative observed choices.
Separating its observations from regularity predicates is deliberately deferred;
the reusable Afriat geometry instead uses raw arrays with explicit hypotheses.
Unlike the downstream WGARP specialization, no lower bound on dimension or
nonzero-choice restriction is needed for the finite Afriat theorem.
Finiteness is a theorem hypothesis, rather than
a field of `Dataset`. Strict increase means weak coordinate dominance with unequal
bundles. Rationalization means that each observation weakly maximizes utility on
its budget; it does not impose unique choice.

## References and provenance

Sidney N. Afriat (1967), *The Construction of Utility Functions from Expenditure Data*,
International Economic Review **8**(1), 67–77.
[DOI: 10.2307/2525382](https://doi.org/10.2307/2525382).

Ported from Victor H. Aguiar's Apache-2.0 Lean development
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), modules
`Data`, `AffineBasics`, and the interior-budget lemma from `Necessity`.
The finite classical Afriat result is covered; the pairwise WGARP and infinite-data
extensions are outside this module's scope.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace MathEconLib.RevealedPreference

/-- A bundle of `L` commodities. -/
abbrev Bundle (L : ℕ) := Fin L → ℝ

/-- A utility function on commodity bundles. -/
abbrev Utility (L : ℕ) := Bundle L → ℝ

/-- The expenditure dot product, reusing Mathlib's `dotProduct`. -/
abbrev dot {L : ℕ} (p x : Bundle L) : ℝ := dotProduct p x

@[simp]
theorem dot_zero_right {L : ℕ} (p : Bundle L) : dot p 0 = 0 := by
  simp [dot, dotProduct]

@[simp]
theorem dot_zero_left {L : ℕ} (x : Bundle L) : dot 0 x = 0 := by
  simp [dot, dotProduct]

theorem dot_sub {L : ℕ} (p x y : Bundle L) : dot p (x - y) = dot p x - dot p y := by
  simp only [dot, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Coordinatewise nonnegativity of a commodity bundle. -/
def Nonnegative {L : ℕ} (x : Bundle L) : Prop := ∀ i, 0 ≤ x i

/--
The strict commodity dominance order: `x` weakly dominates `z` in every
coordinate and the two bundles are unequal.  In finite dimension this is
equivalent to weak dominance with a strict inequality in some coordinate.
-/
def StrictDominates {L : ℕ} (x z : Bundle L) : Prop :=
  (∀ i, z i ≤ x i) ∧ x ≠ z

/-- A utility is strictly increasing for strict commodity dominance. -/
def StrictlyIncreasing {L : ℕ} (u : Utility L) : Prop :=
  ∀ ⦃x z : Bundle L⦄, StrictDominates x z → u z < u x

/-- Strict commodity dominance is the strict product order, with the arguments reversed. -/
theorem strictDominates_iff_lt {L : ℕ} {x z : Bundle L} :
    StrictDominates x z ↔ z < x := by
  rw [lt_iff_le_and_ne]
  exact ⟨fun h => ⟨h.1, Ne.symm h.2⟩, fun h => ⟨h.1, Ne.symm h.2⟩⟩

/-- Economic strict increase agrees with Mathlib's strict monotonicity predicate. -/
theorem strictlyIncreasing_iff_strictMono {L : ℕ} {u : Utility L} :
    StrictlyIncreasing u ↔ StrictMono u := by
  constructor
  · intro h x z hxz
    exact h (strictDominates_iff_lt.mpr hxz)
  · intro h x z hxz
    exact h (strictDominates_iff_lt.mp hxz)

/--
A consumer dataset indexed by `T`, specialized to strictly positive prices and nonnegative
observed bundles. Finiteness is imposed by theorems; dimension and sample size are unrestricted.
-/
structure Dataset (L : ℕ) (T : Type*) where
  price : T → Bundle L
  choice : T → Bundle L
  price_pos : ∀ t i, 0 < price t i
  choice_nonneg : ∀ t i, 0 ≤ choice t i

variable {L : ℕ} {T : Type*}

/-- Expenditure at prices from observation `s`. -/
def expenditure (D : Dataset L T) (s : T) (x : Bundle L) : ℝ :=
  dot (D.price s) x

/--
The signed expenditure gap `pˢ (xˢ - xᵗ)`.  A nonnegative gap says that
`xˢ` is directly revealed preferred to `xᵗ`; a positive gap says so strictly.
-/
def expenditureGap (D : Dataset L T) (s t : T) : ℝ :=
  dot (D.price s) (D.choice s - D.choice t)

theorem expenditureGap_eq (D : Dataset L T) (s t : T) :
    expenditureGap D s t = expenditure D s (D.choice s) - expenditure D s (D.choice t) := by
  exact dot_sub _ _ _

@[simp]
theorem expenditureGap_self (D : Dataset L T) (s : T) : expenditureGap D s s = 0 := by
  simp [expenditureGap]

/-- A nonnegative candidate bundle lying in observation `t`'s budget set. -/
def Affordable (D : Dataset L T) (t : T) (y : Bundle L) : Prop :=
  Nonnegative y ∧ expenditure D t y ≤ expenditure D t (D.choice t)

theorem affordable_choice (D : Dataset L T) (t : T) : Affordable D t (D.choice t) := by
  exact ⟨D.choice_nonneg t, le_rfl⟩

/-- Ordinary utility rationalization on each observed nonnegative budget. -/
def UtilityRationalizes (D : Dataset L T) (u : Utility L) : Prop :=
  ∀ t y, Affordable D t y → u y ≤ u (D.choice t)

/-- A positive finite-dimensional price vector defines a strictly
increasing expenditure functional for weak coordinate dominance with unequal bundles. -/
theorem dot_strictlyIncreasing_of_pos
    {p x z : Bundle L} (hp : ∀ i, 0 < p i)
    (hxz : StrictDominates x z) :
    dot p z < dot p x := by
  rcases hxz with ⟨hle, hne⟩
  have hexists : ∃ i, z i < x i := by
    by_contra hnone
    apply hne
    funext i
    have hxle : x i ≤ z i := by
      apply le_of_not_gt
      intro hstrict
      exact hnone ⟨i, hstrict⟩
    exact le_antisymm hxle (hle i)
  unfold dot dotProduct
  apply Finset.sum_lt_sum
  · intro i _hi
    exact mul_le_mul_of_nonneg_left (hle i) (hp i).le
  · obtain ⟨i, hi⟩ := hexists
    exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hp i)⟩

/-- Observed expenditure is strictly increasing under strict dominance. -/
theorem expenditure_strictlyIncreasing
    (D : Dataset L T) (s : T) :
    StrictlyIncreasing (expenditure D s) := by
  intro x z hxz
  exact dot_strictlyIncreasing_of_pos (D.price_pos s) hxz

/-- The finite-dimensional dot product is continuous in its second
argument. -/
theorem continuous_dot (p : Bundle L) : Continuous (dot p) := by
  exact continuous_const.dotProduct continuous_id

/-- Dot products preserve affine combinations. -/
theorem dot_add_smul (p x y : Bundle L) (a b : ℝ) :
    dot p (a • x + b • y) = a * dot p x + b * dot p y := by
  simp only [dot, dotProduct_add, dotProduct_smul, smul_eq_mul]

private theorem positive_price_sum (D : Dataset L T) (s : T) (hL : 0 < L) :
    0 < ∑ k : Fin L, D.price s k := by
  apply Finset.sum_pos'
  · intro k _hk
    exact (D.price_pos s k).le
  · let k₀ : Fin L := ⟨0, hL⟩
    exact ⟨k₀, Finset.mem_univ k₀, D.price_pos s k₀⟩

private theorem dot_add_constant (p x : Bundle L) (ε : ℝ) :
    dot p (fun k => x k + ε) = dot p x + ε * ∑ k, p k := by
  unfold dot dotProduct
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    ∑ k : Fin L, p k * ε = ∑ k : Fin L, ε * p k := by
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = ε * ∑ k : Fin L, p k := by rw [Finset.mul_sum]

/-- A strictly cheaper nonnegative bundle can be improved in every
coordinate while remaining within the budget. -/
theorem exists_strictDominating_affordable
    (D : Dataset L T) (s t : T)
    (hcheap : 0 < expenditureGap D s t) :
    ∃ z : Bundle L,
      StrictDominates z (D.choice t) ∧ Affordable D s z := by
  have hL : 0 < L := by
    by_contra hL
    have hzero : L = 0 := Nat.eq_zero_of_not_pos hL
    subst L
    simp [expenditureGap, dot, dotProduct] at hcheap
  let priceSum : ℝ := ∑ k : Fin L, D.price s k
  have hsum : 0 < priceSum := by
    simpa [priceSum] using positive_price_sum D s hL
  let ε : ℝ := expenditureGap D s t / (2 * priceSum)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  let z : Bundle L := fun k => D.choice t k + ε
  have hdom : StrictDominates z (D.choice t) := by
    refine ⟨fun k => by dsimp [z]; linarith, ?_⟩
    intro heq
    have hk := congr_fun heq ⟨0, hL⟩
    dsimp [z] at hk
    linarith
  have hnonneg : Nonnegative z := by
    intro k
    dsimp [z]
    exact add_nonneg (D.choice_nonneg t k) hε.le
  have hεsum : ε * priceSum = expenditureGap D s t / 2 := by
    dsimp [ε]
    field_simp
  have hdot :
      expenditure D s z = expenditure D s (D.choice t) + ε * priceSum := by
    simpa [expenditure, z, priceSum] using
      dot_add_constant (D.price s) (D.choice t) ε
  refine ⟨z, hdom, hnonneg, ?_⟩
  rw [hdot, hεsum, expenditureGap_eq]
  rw [expenditureGap_eq] at hcheap
  linarith

end MathEconLib.RevealedPreference
