/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.Basic
public import Mathlib.Algebra.BigOperators.Field
public import MathEconLib.RevealedPreference.EquilibriumBounds

/-!
# Elimination of finite mixed linear inequalities

Finite Fourier–Motzkin elimination preserves both weak and strict constraints.
The resulting condition compares only the supplied coefficients and right-hand
sides. It provides an alternative to a general linear-programming duality theorem.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators

namespace MathEconLib.RevealedPreference.Equilibrium.FiniteLinearSystem

/-- A finite-dimensional linear system with a separate strictness flag per row. -/
structure System (n : ℕ) (R : Type*) where
  coeff : R → Fin n → ℝ
  rhs : R → ℝ
  strict : R → Bool

variable {n : ℕ} {R : Type*}

/-- Satisfaction of every row by one common variable vector. -/
def Satisfies (S : System n R) (x : Fin n → ℝ) : Prop :=
  ∀ r, Rel (S.strict r) (S.rhs r) (dot (S.coeff r) x)

/-- Joint feasibility of the finite affine inequalities. -/
def Feasible (S : System n R) : Prop := ∃ x, Satisfies S x

/-- Rows surviving one variable elimination: zero-coefficient rows and pairs of
positive/negative-coefficient rows. -/
def EliminationRows (S : System (n + 1) R) :=
  {r : R // S.coeff r 0 = 0} ⊕
    ({r : R // 0 < S.coeff r 0} × {r : R // S.coeff r 0 < 0})

noncomputable instance [Fintype R] (S : System (n + 1) R) : Fintype (EliminationRows S) := by
  classical
  unfold EliminationRows
  infer_instance

/-- Eliminate the first variable by comparing every lower bound with every
upper bound. Division occurs only by a coefficient certified nonzero by its row type. -/
noncomputable def eliminate (S : System (n + 1) R) : System n (EliminationRows S) where
  coeff := fun r => match r with
    | Sum.inl z => fun k => S.coeff z.1 k.succ
    | Sum.inr (p, q) => fun k =>
        S.coeff p.1 k.succ / S.coeff p.1 0 - S.coeff q.1 k.succ / S.coeff q.1 0
  rhs := fun r => match r with
    | Sum.inl z => S.rhs z.1
    | Sum.inr (p, q) => S.rhs p.1 / S.coeff p.1 0 - S.rhs q.1 / S.coeff q.1 0
  strict := fun r => match r with
    | Sum.inl z => S.strict z.1
    | Sum.inr (p, q) => S.strict p.1 || S.strict q.1

private def tailValue (S : System (n + 1) R) (r : R) (x : Fin n → ℝ) : ℝ :=
  dot (fun k => S.coeff r k.succ) x

private noncomputable def bound (S : System (n + 1) R) (r : R) (x : Fin n → ℝ) : ℝ :=
  (S.rhs r - tailValue S r x) / S.coeff r 0

private theorem dot_cons (S : System (n + 1) R) (r : R) (t : ℝ) (x : Fin n → ℝ) :
    dot (S.coeff r) (Fin.cons t x) = S.coeff r 0 * t + tailValue S r x := by
  simp [dot, dotProduct, Fin.sum_univ_succ, tailValue]

private theorem rel_pos_coeff (s : Bool) (a b v t : ℝ) (ha : 0 < a) :
    Rel s b (a * t + v) ↔ Rel s ((b - v) / a) t := by
  simp only [Rel, div_le_iff₀ ha, div_lt_iff₀ ha, sub_le_iff_le_add, sub_lt_iff_lt_add]
  rw [mul_comm t a]

private theorem rel_neg_coeff (s : Bool) (a b v t : ℝ) (ha : a < 0) :
    Rel s b (a * t + v) ↔ Rel s t ((b - v) / a) := by
  simp only [Rel, le_div_iff_of_neg ha, lt_div_iff_of_neg ha,
    sub_le_iff_le_add, sub_lt_iff_lt_add]
  rw [mul_comm t a]

private theorem rel_pair_iff (S : System (n + 1) R)
    (p : {r : R // 0 < S.coeff r 0}) (q : {r : R // S.coeff r 0 < 0})
    (x : Fin n → ℝ) :
    Rel ((eliminate S).strict (.inr (p, q))) ((eliminate S).rhs (.inr (p, q)))
      (dot ((eliminate S).coeff (.inr (p, q))) x) ↔
    Rel (S.strict p.1 || S.strict q.1) (bound S p.1 x) (bound S q.1 x) := by
  have hdot : dot ((eliminate S).coeff (.inr (p, q))) x =
      tailValue S p.1 x / S.coeff p.1 0 - tailValue S q.1 x / S.coeff q.1 0 := by
    simp only [eliminate, dot, dotProduct, sub_mul, Finset.sum_sub_distrib,
      div_mul_eq_mul_div, ← Finset.sum_div, tailValue]
  rw [hdot]
  simp only [eliminate, Rel, bound, sub_div]
  constructor <;> rintro ⟨hweak, hstrict⟩ <;> refine ⟨by linarith, ?_⟩ <;>
    intro hs <;> have := hstrict hs <;> linarith

/-- One Fourier–Motzkin step, preserving a common value for the eliminated variable. -/
theorem satisfies_eliminate_iff [Finite R] (S : System (n + 1) R) (x : Fin n → ℝ) :
    Satisfies (eliminate S) x ↔ ∃ t : ℝ, Satisfies S (Fin.cons t x) := by
  classical
  let := Fintype.ofFinite R
  constructor
  · intro h
    let lower : Finset (ℝ × Bool) := Finset.univ.image
      (fun p : {r : R // 0 < S.coeff r 0} => (bound S p.1 x, S.strict p.1))
    let upper : Finset (ℝ × Bool) := Finset.univ.image
      (fun q : {r : R // S.coeff r 0 < 0} => (bound S q.1 x, S.strict q.1))
    have hpairs : ∀ l ∈ lower, ∀ u ∈ upper, Rel (l.2 || u.2) l.1 u.1 := by
      intro l hl u hu
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hu
      exact (rel_pair_iff S p q x).mp (h (.inr (p, q)))
    obtain ⟨t, hlower, hupper⟩ := exists_between_finite_bounds lower upper hpairs
    refine ⟨t, fun r => ?_⟩
    rw [dot_cons]
    rcases lt_trichotomy (S.coeff r 0) 0 with hneg | hzero | hpos
    · apply (rel_neg_coeff _ _ _ _ _ hneg).mpr
      exact hupper (bound S r x, S.strict r)
        (Finset.mem_image.mpr ⟨⟨r, hneg⟩, Finset.mem_univ _, rfl⟩)
    · simpa [eliminate, hzero, tailValue] using h (.inl ⟨r, hzero⟩)
    · apply (rel_pos_coeff _ _ _ _ _ hpos).mpr
      exact hlower (bound S r x, S.strict r)
        (Finset.mem_image.mpr ⟨⟨r, hpos⟩, Finset.mem_univ _, rfl⟩)
  · rintro ⟨t, h⟩ r
    cases r with
    | inl z =>
      simpa [dot_cons, z.2, eliminate, tailValue] using h z.1
    | inr pq =>
      rcases pq with ⟨p, q⟩
      apply (rel_pair_iff S p q x).mpr
      have hp := (rel_pos_coeff (S.strict p.1) (S.coeff p.1 0) (S.rhs p.1)
        (tailValue S p.1 x) t p.2).mp (by simpa only [dot_cons] using h p.1)
      have hq := (rel_neg_coeff (S.strict q.1) (S.coeff q.1 0) (S.rhs q.1)
        (tailValue S q.1 x) t q.2).mp (by simpa only [dot_cons] using h q.1)
      refine ⟨hp.1.trans hq.1, fun hs => ?_⟩
      rcases Bool.or_eq_true_iff.mp hs with hs | hs
      · exact (hp.2 hs).trans_le hq.1
      · exact hp.1.trans_lt (hq.2 hs)

/-- Elimination preserves feasibility. -/
theorem feasible_eliminate_iff [Finite R] (S : System (n + 1) R) :
    Feasible (eliminate S) ↔ Feasible S := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨t, ht⟩ := (satisfies_eliminate_iff S x).mp hx
    exact ⟨Fin.cons t x, ht⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun k => x k.succ, (satisfies_eliminate_iff S _).mpr ⟨x 0, ?_⟩⟩
    change Satisfies S (Fin.cons (x 0) (Fin.tail x))
    rw [Fin.cons_self_tail]
    exact hx

/-- Repeated elimination ends with comparisons of observed coefficients and
right-hand sides only. No real-valued choice variables remain. -/
noncomputable def EliminationCondition : {n : ℕ} → {R : Type*} →
    [Fintype R] → System n R → Prop
  | 0, _, _, S => ∀ r, Rel (S.strict r) (S.rhs r) 0
  | n + 1, _, _, S => EliminationCondition (n := n) (eliminate S)

/-- A finite mixed weak/strict linear system is feasible exactly when its
fully eliminated coefficient condition holds. -/
theorem feasible_iff_eliminationCondition [Fintype R] (S : System n R) :
    Feasible S ↔ EliminationCondition S := by
  induction n generalizing R with
  | zero =>
    constructor
    · rintro ⟨x, hx⟩ r
      simpa [dot, dotProduct] using hx r
    · intro h
      exact ⟨fun k => Fin.elim0 k, fun r => by simpa [dot, dotProduct] using h r⟩
  | succ n ih =>
    rw [← feasible_eliminate_iff S]
    exact ih (eliminate S)

end MathEconLib.RevealedPreference.Equilibrium.FiniteLinearSystem
