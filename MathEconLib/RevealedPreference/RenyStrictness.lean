/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.RenyData
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Data.Rat.Encodable

/-!
# Strictness bridges for infinite-data rationalization

These lemmas support the infinite-observation theorem in Philip J. Reny (2015),
*A Characterization of Rationalizable Consumer Behavior*, Econometrica 83(1),
175--192, DOI: 10.3982/ECTA12345. They separate weak maximization from strict
comparisons at strictly cheaper alternatives. The rational-pair reduction is
the countable strictness interface useful in the logical-compactness approach
of Yannai A. Gonczarowski, Scott Duke Kominers and Ran I. Shorrer (2025),
*To infinity and beyond: A general framework for scaling economic theories*,
Theoretical Economics 20(2), 511--542, DOI: 10.3982/TE5878.

This file proves strictness and density infrastructure; it does not by itself
assert the infinite-data Afriat sufficiency theorem.

## References and Lean provenance

Ported from Victor H. Aguiar's Apache-2.0 Lean development
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), module `RenyStrictness`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

open scoped BigOperators

variable {L : ℕ} {T : Type*}

/-- A nonzero nonnegative finite price vector has a positive sum. -/
theorem sum_pos_of_nonnegative_ne_zero (p : Bundle L)
    (hp : Nonnegative p) (hpne : p ≠ 0) : 0 < ∑ i, p i := by
  have hnonneg : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => hp i)
  apply lt_of_le_of_ne hnonneg
  intro hzero
  apply hpne
  funext i
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp i)).mp hzero.symm
  exact hall i (Finset.mem_univ i)

/-- A strictly cheaper alternative can be increased in every coordinate while
remaining affordable. Zero-price coordinates are permitted. -/
theorem exists_strictly_dominating_affordable (p x y : Bundle L)
    (hp : Nonnegative p) (hpne : p ≠ 0) (hy : Nonnegative y)
    (hcheap : dot p y < dot p x) :
    ∃ z : Bundle L, Nonnegative z ∧ (∀ i, y i < z i) ∧ dot p z ≤ dot p x := by
  let s : ℝ := ∑ i, p i
  have hs : 0 < s := sum_pos_of_nonnegative_ne_zero p hp hpne
  let ε : ℝ := (dot p x - dot p y) / (2 * s)
  have hε : 0 < ε := div_pos (sub_pos.mpr hcheap) (mul_pos (by norm_num) hs)
  let z : Bundle L := fun i => y i + ε
  refine ⟨z, (fun i => le_trans (hy i) (le_of_lt (lt_add_of_pos_right _ hε))),
    (fun i => lt_add_of_pos_right _ hε), ?_⟩
  have hdot : dot p z = dot p y + ε * s := by
    simp only [dot, dotProduct, z, mul_add, Finset.sum_add_distrib, s]
    rw [← Finset.sum_mul]
    ring
  rw [hdot]
  have hprod : ε * s = (dot p x - dot p y) / 2 := by
    dsimp [ε]
    field_simp
  rw [hprod]
  linarith

/-- Weak budget rationalization and strict increases in all coordinates imply
Reny's strict-affordability convention. This does not imply unique demand. -/
theorem renyRationalizes_of_weak_of_semiStrict
    (p q : T → Bundle L) (u : Utility L)
    (hp : RenyPriceAdmissible p)
    (hweak : WeakUtilityRationalizes p q u)
    (hstrict : SemiStrictlyIncreasingOnNonnegative u) :
    RenyRationalizes p q u := by
  intro t y hy
  refine ⟨hweak t y hy, ?_⟩
  intro hcheap
  obtain ⟨z, hz, hyz, hbudget⟩ :=
    exists_strictly_dominating_affordable (p t) (q t) y (hp t).1 (hp t).2 hy hcheap
  exact (hstrict y z hy hz hyz).trans_le (hweak t z hz hbudget)

/-- A countable set of rational, strongly ordered nonnegative bundle pairs.
The observation type remains unrestricted. -/
abbrev RationalStrongPair (L : ℕ) :=
  {ab : (Fin L → ℚ) × (Fin L → ℚ) // ∀ i, 0 ≤ ab.1 i ∧ ab.1 i < ab.2 i}

/-- Finite rational bundles and their strong-pair subtype are countable. -/
theorem rationalStrongPair_countable : Countable (RationalStrongPair L) := inferInstance

namespace RationalStrongPair

/-- The smaller rational bundle, viewed as a real commodity bundle. -/
def lower (ab : RationalStrongPair L) : Bundle L := fun i => (ab.val.1 i : ℝ)

/-- The larger rational bundle, viewed as a real commodity bundle. -/
def upper (ab : RationalStrongPair L) : Bundle L := fun i => (ab.val.2 i : ℝ)

theorem lower_nonnegative (ab : RationalStrongPair L) : Nonnegative ab.lower := by
  intro i
  unfold lower
  exact_mod_cast (ab.property i).1

theorem lower_lt_upper (ab : RationalStrongPair L) :
    ∀ i, ab.lower i < ab.upper i := by
  intro i
  unfold lower upper
  exact_mod_cast (ab.property i).2

theorem upper_nonnegative (ab : RationalStrongPair L) : Nonnegative ab.upper := by
  intro i
  exact (lower_nonnegative ab i).trans (lower_lt_upper ab i).le

end RationalStrongPair

/-- Two rational bundles can be placed strictly inside any strongly ordered
nonnegative real pair. This is a coordinatewise density result, not an
assumption about the observation support. -/
theorem exists_rationalStrongPair_between (x y : Bundle L)
    (hx : Nonnegative x) (hxy : ∀ i, x i < y i) :
    ∃ ab : RationalStrongPair L,
      (∀ i, x i < ab.lower i) ∧ (∀ i, ab.upper i < y i) := by
  classical
  have hex : ∀ i, ∃ a b : ℚ,
      x i < (a : ℝ) ∧ (a : ℝ) < (b : ℝ) ∧ (b : ℝ) < y i := by
    intro i
    obtain ⟨a, hxa, hay⟩ := exists_rat_btwn (hxy i)
    obtain ⟨b, hab, hby⟩ := exists_rat_btwn hay
    exact ⟨a, b, hxa, hab, hby⟩
  choose a b hxa hab hby using hex
  have hpair : ∀ i, 0 ≤ a i ∧ a i < b i := by
    intro i
    constructor
    · exact_mod_cast (hx i).trans (hxa i).le
    · exact_mod_cast hab i
  exact ⟨⟨(a, b), hpair⟩, hxa, hby⟩

/-- Under coordinatewise monotonicity, strictness on countably many rational
pairs is equivalent to strictness for every strong commodity comparison. -/
theorem semiStrict_iff_rationalStrongPair_strict (u : Utility L)
    (hmono : MonotoneOn u {x | Nonnegative x}) :
    SemiStrictlyIncreasingOnNonnegative u ↔
      ∀ ab : RationalStrongPair L, u ab.lower < u ab.upper := by
  constructor
  · intro hstrict ab
    exact hstrict ab.lower ab.upper ab.lower_nonnegative ab.upper_nonnegative
      ab.lower_lt_upper
  · intro hrat x y hx hy hxy
    obtain ⟨ab, hxa, hby⟩ := exists_rationalStrongPair_between x y hx hxy
    exact (hmono hx ab.lower_nonnegative (fun i => (hxa i).le)).trans_lt
      ((hrat ab).trans_le (hmono ab.upper_nonnegative hy (fun i => (hby i).le)))

/-- Prescribed positive margins on rational strong pairs suffice for global
semistrict monotonicity. Margins may differ across pairs. -/
theorem semiStrict_of_rationalStrongPair_margins (u : Utility L)
    (hmono : MonotoneOn u {x | Nonnegative x})
    (margin : RationalStrongPair L → ℝ)
    (hpositive : ∀ ab, 0 < margin ab)
    (hmargin : ∀ ab, u ab.lower + margin ab ≤ u ab.upper) :
    SemiStrictlyIncreasingOnNonnegative u := by
  apply (semiStrict_iff_rationalStrongPair_strict u hmono).mpr
  intro ab
  have hm := hmargin ab
  have hp := hpositive ab
  linarith

end MathEconLib.RevealedPreference
