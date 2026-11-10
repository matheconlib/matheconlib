/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.Basic

/-!
# Afriat support planes and finite envelopes

This module is independent of GARP and its certificate construction. Prices and
observed bundles are unrestricted arrays. Continuity, concavity, and interpolation
need no sign restrictions; strict increase requires positive prices and multipliers,
with no nonnegativity assumption on observed bundles. Coordinatewise monotonicity allows
nonnegative prices and multipliers. Weak budget maximization needs only nonnegative
multipliers. The finite lower envelope requires nonempty observations.

## References and provenance

Sidney N. Afriat (1967), *The Construction of Utility Functions from Expenditure Data*,
International Economic Review **8**(1), 67–77.
[DOI: 10.2307/2525382](https://doi.org/10.2307/2525382).

Ported from Victor H. Aguiar's Apache-2.0 Lean development
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), module `GlobalAfriat`.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace MathEconLib.RevealedPreference

variable {L : ℕ} {T : Type*}

/-- Afriat support plane based at observation `t`. -/
def globalAfriatSupport (U lam : T → ℝ) (p q : T → Bundle L)
    (t : T) (x : Bundle L) : ℝ :=
  U t + lam t * (dot (p t) x - dot (p t) (q t))

/-- Global Afriat inequalities, with no finiteness assumption on observations. -/
def AfriatInequalities (U lam : T → ℝ) (p q : T → Bundle L) : Prop :=
  ∀ s t, U s ≤ globalAfriatSupport U lam p q t (q s)

/-- Strict positivity of the global Afriat multipliers. -/
def PositiveMultipliers (lam : T → ℝ) : Prop :=
  ∀ t, 0 < lam t

/-- Lower envelope of the global Afriat support planes. -/
noncomputable def globalAfriatUtility [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L) : Utility L :=
  fun x => Finset.univ.inf' Finset.univ_nonempty
    (fun t => globalAfriatSupport U lam p q t x)

theorem globalAfriatUtility_le_support [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T) (x : Bundle L) :
    globalAfriatUtility U lam p q x ≤
      globalAfriatSupport U lam p q t x := by
  unfold globalAfriatUtility
  exact Finset.inf'_le _ (Finset.mem_univ t)

theorem le_globalAfriatUtility_of_le_supports [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L) {a : ℝ} {x : Bundle L}
    (h : ∀ t, a ≤ globalAfriatSupport U lam p q t x) :
    a ≤ globalAfriatUtility U lam p q x := by
  unfold globalAfriatUtility
  apply Finset.le_inf'
  intro t _ht
  exact h t

@[simp]
theorem globalAfriatSupport_choice_self
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T) :
    globalAfriatSupport U lam p q t (q t) = U t := by
  simp [globalAfriatSupport]

/-- The envelope interpolates every observed Afriat utility level. -/
theorem globalAfriatUtility_eq_observed [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hA : AfriatInequalities U lam p q) (s : T) :
    globalAfriatUtility U lam p q (q s) = U s := by
  apply le_antisymm
  · calc
      globalAfriatUtility U lam p q (q s) ≤
          globalAfriatSupport U lam p q s (q s) :=
        globalAfriatUtility_le_support U lam p q s (q s)
      _ = U s := globalAfriatSupport_choice_self U lam p q s
  · exact le_globalAfriatUtility_of_le_supports U lam p q (hA s)

/-- Every affine support plane is continuous. -/
theorem globalAfriatSupport_continuous
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T) :
    Continuous (globalAfriatSupport U lam p q t) := by
  unfold globalAfriatSupport
  exact continuous_const.add
    (continuous_const.mul ((continuous_dot (p t)).sub continuous_const))

/-- A finite lower envelope of continuous affine planes is continuous. -/
theorem globalAfriatUtility_continuous [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L) :
    Continuous (globalAfriatUtility U lam p q) := by
  unfold globalAfriatUtility
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun t _ht => globalAfriatSupport_continuous U lam p q t)

/-- Exact affine-combination identity for a global support plane. -/
theorem globalAfriatSupport_add_smul
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T)
    (x y : Bundle L) (a b : ℝ) (hab : a + b = 1) :
    globalAfriatSupport U lam p q t (a • x + b • y) =
      a * globalAfriatSupport U lam p q t x +
        b * globalAfriatSupport U lam p q t y := by
  unfold globalAfriatSupport
  rw [dot_add_smul]
  calc
    U t + lam t * (a * dot (p t) x + b * dot (p t) y - dot (p t) (q t)) =
        (a + b) * U t +
          lam t * (a * dot (p t) x + b * dot (p t) y -
            (a + b) * dot (p t) (q t)) := by rw [hab]; ring
    _ = a * (U t + lam t * (dot (p t) x - dot (p t) (q t))) +
        b * (U t + lam t * (dot (p t) y - dot (p t) (q t))) := by ring

/-- Every support plane is affine and hence concave. -/
theorem globalAfriatSupport_concaveOn
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T) :
    ConcaveOn ℝ Set.univ (globalAfriatSupport U lam p q t) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b _ha _hb hab
  rw [globalAfriatSupport_add_smul U lam p q t x y a b hab]
  simp only [smul_eq_mul]
  exact le_rfl

/-- A finite lower envelope of concave functions is concave. -/
theorem globalAfriatUtility_concaveOn [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L) :
    ConcaveOn ℝ Set.univ (globalAfriatUtility U lam p q) := by
  let envelope : Bundle L → ℝ :=
    Finset.univ.inf' Finset.univ_nonempty
      (fun t => globalAfriatSupport U lam p q t)
  have henvelope : ConcaveOn ℝ Set.univ envelope := by
    refine Finset.inf'_induction (s := Finset.univ)
      (H := Finset.univ_nonempty)
      (f := fun t => globalAfriatSupport U lam p q t) ?_ ?_
    · intro f hf g hg
      simpa using hf.inf hg
    · intro t _ht
      exact globalAfriatSupport_concaveOn U lam p q t
  have heq : envelope = globalAfriatUtility U lam p q := by
    funext x
    simp [envelope, globalAfriatUtility, Finset.inf'_apply]
  rw [← heq]
  exact henvelope

/-- A nonnegative price vector defines a coordinatewise nondecreasing linear
functional; the bundles themselves need not be nonnegative. -/
theorem dot_monotone_of_nonnegative {p : Bundle L} (hp : Nonnegative p) :
    Monotone (dot p) := by
  intro x y hxy
  unfold dot
  exact Finset.sum_le_sum fun i _hi => mul_le_mul_of_nonneg_left (hxy i) (hp i)

/-- A nonnegative multiplier and nonnegative prices at `t` make its affine
support coordinatewise nondecreasing. Other observations are unrestricted. -/
theorem globalAfriatSupport_monotone
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T)
    (hp : Nonnegative (p t)) (hlam : 0 ≤ lam t) :
    Monotone (globalAfriatSupport U lam p q t) := by
  intro x y hxy
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (dot_monotone_of_nonnegative hp hxy) _) hlam)

/-- Nonnegative prices and multipliers make the finite envelope coordinatewise
nondecreasing. Zero multipliers and zero-price goods are allowed. -/
theorem globalAfriatUtility_monotone [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hp : ∀ t, Nonnegative (p t)) (hlam : ∀ t, 0 ≤ lam t) :
    Monotone (globalAfriatUtility U lam p q) := by
  intro x y hxy
  apply le_globalAfriatUtility_of_le_supports
  intro t
  exact (globalAfriatUtility_le_support U lam p q t x).trans
    (globalAfriatSupport_monotone U lam p q t (hp t) (hlam t) hxy)

/-- A positive multiplier and strictly positive price vector make a global
support plane strictly increasing. -/
theorem globalAfriatSupport_strictlyIncreasing
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T)
    (hp : ∀ i, 0 < p t i) (hlam : 0 < lam t) :
    StrictlyIncreasing (globalAfriatSupport U lam p q t) := by
  intro x z hxz
  have hdot : dot (p t) z < dot (p t) x :=
    dot_strictlyIncreasing_of_pos hp hxz
  have hscaled :
      lam t * (dot (p t) z - dot (p t) (q t)) <
        lam t * (dot (p t) x - dot (p t) (q t)) :=
    mul_lt_mul_of_pos_left (sub_lt_sub_right hdot _) hlam
  exact add_lt_add_right hscaled _

/-- The lower envelope remains strictly increasing because all of its finite
support planes increase strictly. -/
theorem globalAfriatUtility_strictlyIncreasing [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hp : ∀ t i, 0 < p t i) (hpos : PositiveMultipliers lam) :
    StrictlyIncreasing (globalAfriatUtility U lam p q) := by
  intro x z hxz
  unfold globalAfriatUtility
  rw [Finset.lt_inf'_iff]
  intro t _ht
  exact (Finset.inf'_le _ (Finset.mem_univ t)).trans_lt
    (globalAfriatSupport_strictlyIncreasing U lam p q t (hp t) (hpos t) hxz)

/-- The envelope weakly maximizes at an observation over its full expenditure halfspace.
Only the multiplier at that observation must be nonnegative. -/
theorem globalAfriatUtility_le_observed_of_dot_le [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hA : AfriatInequalities U lam p q) (t : T) (hlam : 0 ≤ lam t)
    {y : Bundle L} (hy : dot (p t) y ≤ dot (p t) (q t)) :
    globalAfriatUtility U lam p q y ≤ globalAfriatUtility U lam p q (q t) := by
  have hscaled : lam t * (dot (p t) y - dot (p t) (q t)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (sub_nonpos.mpr hy)
  calc
    globalAfriatUtility U lam p q y ≤ globalAfriatSupport U lam p q t y :=
      globalAfriatUtility_le_support U lam p q t y
    _ ≤ U t := by unfold globalAfriatSupport; linarith
    _ = globalAfriatUtility U lam p q (q t) :=
      (globalAfriatUtility_eq_observed U lam p q hA t).symm

/-- The Afriat envelope weakly maximizes at each observed choice on its
budget. -/
theorem globalAfriatUtility_rationalizes [Fintype T] [Nonempty T]
    (D : Dataset L T) (U lam : T → ℝ)
    (hA : AfriatInequalities U lam D.price D.choice)
    (hpos : PositiveMultipliers lam) :
    UtilityRationalizes D (globalAfriatUtility U lam D.price D.choice) := by
  intro t y hy
  exact globalAfriatUtility_le_observed_of_dot_le U lam D.price D.choice hA t
    (hpos t).le hy.2

/-- The selected envelope ranks every strictly cheaper bundle strictly below
the observed choice, even without a nonnegativity assumption on that bundle. -/
theorem globalAfriatUtility_lt_observed_of_dot_lt [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hA : AfriatInequalities U lam p q) (t : T) (hlam : 0 < lam t)
    {y : Bundle L} (hy : dot (p t) y < dot (p t) (q t)) :
    globalAfriatUtility U lam p q y < globalAfriatUtility U lam p q (q t) := by
  have hscaled : lam t * (dot (p t) y - dot (p t) (q t)) < 0 :=
    mul_neg_of_pos_of_neg hlam (sub_neg.mpr hy)
  calc
    globalAfriatUtility U lam p q y ≤ globalAfriatSupport U lam p q t y :=
      globalAfriatUtility_le_support U lam p q t y
    _ < U t := by unfold globalAfriatSupport; linarith
    _ = globalAfriatUtility U lam p q (q t) :=
      (globalAfriatUtility_eq_observed U lam p q hA t).symm

end MathEconLib.RevealedPreference
