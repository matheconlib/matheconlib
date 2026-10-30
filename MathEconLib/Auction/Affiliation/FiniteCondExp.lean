/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Auction.Affiliation.Basic
public import Mathlib

/-! # Finite conditional expectations

This file provides elementary infrastructure for conditional expectations
with respect to finite, possibly unnormalized weights.

For a weight function `f : α → ℝ`, a function `g : α → ℝ`, and a finite set
`A : Finset α`, `condExpOn f g A` is the `f`-weighted average of `g` on `A`:

`(∑ x ∈ A, g x * f x) / (∑ x ∈ A, f x)`.

The formula accepts arbitrary real weights. Its probability interpretation requires
nonnegative weights and positive total weight on the conditioning set. No global
unit-mass assumption is needed: positive rescaling cancels between numerator and
denominator. Zero total weight instead gives Lean's totalized value `0`, not a
conditional probability model. The normalized comparison theorems exclude this case through
strict positivity on the support and nonempty conditioning sets.

The definition itself is independent of affiliation.  The comparison
theorems in this file use affiliation to compare two finite conditioning
events related by the lattice order.  `MonotoneCondExp.lean` applies the
general result to signal slices for finite Lemma 7.3, and
`WinnersCurse.lean` applies it to winning and own-signal slices for finite
Proposition 7.4.
-/

namespace MathEconLib

@[expose] public section

open Finset
open scoped FinsetFamily

namespace Auction.Affiliation

/-- The weighted average of `g` on the finite set `A`, computed using
the possibly unnormalized weights `f`.

The denominator normalizes the restriction of `f` to `A`.  If the total
weight of `A` is zero, division has Lean's usual value `0`; comparison
theorems assume positive weights and a nonempty set whenever a genuine
conditional average is required. For nonnegative weights and positive total mass,
this is conditional expectation under the discrete law obtained by normalization;
it does not condition a separately supplied continuous signal law. -/
noncomputable def condExpOn {α : Type*} (f g : α → ℝ) (A : Finset α) : ℝ :=
  (∑ x ∈ A, g x * f x) / (∑ x ∈ A, f x)

/-- A nonempty finite set has positive total weight when every one of its
elements has positive weight.  The positivity assumption is stated on a
larger set `S`, matching later applications where `A` is a conditioning event
inside a finite support. -/
theorem sum_pos_on_of_pos {α : Type*} {f : α → ℝ} {S A : Finset α}
    (hpos : ∀ x ∈ S, 0 < f x) (hAS : A ⊆ S) (hA : A.Nonempty) :
    0 < ∑ x ∈ A, f x :=
  Finset.sum_pos (fun x hx => hpos x (hAS hx)) hA

/-- Adding a constant to `g` adds the same constant to its conditional
expectation on a finite set of nonzero total weight.

This elementary identity is what allows later comparison theorems to shift a
monotone function until it is nonnegative, apply a nonnegative result, and
then cancel the common shift. -/
theorem condExpOn_add_const {α : Type*} (f g : α → ℝ) (A : Finset α) (c : ℝ)
    (hmass : (∑ x ∈ A, f x) ≠ 0) :
    condExpOn f (fun x => g x + c) A = condExpOn f g A + c := by
  simp only [condExpOn]
  -- Separate the original weighted numerator from the contribution of `c`.
  rw [show (∑ x ∈ A, (g x + c) * f x) =
        (∑ x ∈ A, g x * f x) + c * ∑ x ∈ A, f x by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun x _ => by ring]
  -- Divide the two terms separately; the mass in the second term cancels.
  rw [add_div, mul_div_assoc, div_self hmass, mul_one]

/-! ## The affiliation comparison before normalization -/

/-- The cross-multiplied comparison for finite conditional expectations.

Let `f` be affiliated weights that are positive on a finite sublattice `S`,
and let `g` be a nondecreasing function that is nonnegative on `S`.  Suppose
that `A` and `B` are subsets of `S` such that, for every `a ∈ A` and `b ∈ B`,

* the pointwise supremum `a ⊔ b` belongs to `B`, and
* the pointwise infimum `a ⊓ b` belongs to `A`.

Then

`(∑ x ∈ A, g x * f x) * (∑ x ∈ B, f x) ≤`
`  (∑ x ∈ B, g x * f x) * (∑ x ∈ A, f x)`.

This is the numerator-and-denominator comparison that will yield
`condExpOn f g A ≤ condExpOn f g B` once both total weights are known to be
positive.  Its proof applies the four-functions theorem
(`four_functions_theorem`) to `f` and `g * f`, extended by zero outside `S`.
The lattice hypotheses then place the resulting infima back in `A` and the
suprema back in `B`.

This theorem is the common Ahlswede–Daykin step used by the finite versions
of Lemma 7.3 and Proposition 7.4. -/
theorem sum_mul_sum_le_of_affiliated {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {S A B : Finset (Fin n → ℝ)}
    (hf : Affiliated f) (hpos : ∀ x ∈ S, 0 < f x)
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    (hg : Monotone g) (hg0 : ∀ x ∈ S, 0 ≤ g x)
    (hAS : A ⊆ S) (hBS : B ⊆ S)
    (hsupAB : ∀ a ∈ A, ∀ b ∈ B, a ⊔ b ∈ B)
    (hinfAB : ∀ a ∈ A, ∀ b ∈ B, a ⊓ b ∈ A) :
    (∑ x ∈ A, g x * f x) * (∑ x ∈ B, f x) ≤
      (∑ x ∈ B, g x * f x) * (∑ x ∈ A, f x) := by
  classical
  -- Extend `f` and `g * f` by zero outside `S`.  This lets us apply the
  -- four-functions theorem, whose hypotheses are stated on the whole lattice.
  set F : (Fin n → ℝ) → ℝ := fun x => if x ∈ S then f x else 0 with hF
  set GF : (Fin n → ℝ) → ℝ := fun x => if x ∈ S then g x * f x else 0 with hGF
  -- Both extended functions are nonnegative everywhere.
  have hF_nonneg : ∀ x, 0 ≤ F x := by
    intro x
    simp only [hF]
    split_ifs with hx
    · exact (hpos x hx).le
    · exact le_rfl
  have hGF_nonneg : ∀ x, 0 ≤ GF x := by
    intro x
    simp only [hGF]
    split_ifs with hx
    · exact mul_nonneg (hg0 x hx) (hpos x hx).le
    · exact le_rfl
  -- Affiliation of `f` and monotonicity of `g` give the pointwise hypothesis
  -- of the four-functions theorem.
  have hfour : ∀ a b : Fin n → ℝ, GF a * F b ≤ F (a ⊓ b) * GF (a ⊔ b) := by
    intro a b
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · have hsupS : a ⊔ b ∈ S :=
          mem_coe.1 (hsub.supClosed (mem_coe.2 ha) (mem_coe.2 hb))
        have hinfS : a ⊓ b ∈ S :=
          mem_coe.1 (hsub.infClosed (mem_coe.2 ha) (mem_coe.2 hb))
        simp only [hF, hGF, ite_eq_left ha, ite_eq_left hb, ite_eq_left hsupS, ite_eq_left hinfS]
        have hg_le : g a ≤ g (a ⊔ b) := hg le_sup_left
        have hf_le : f a * f b ≤ f (a ⊔ b) * f (a ⊓ b) := hf a b
        calc
          g a * f a * f b = g a * (f a * f b) := by ring
          _ ≤ g (a ⊔ b) * (f (a ⊔ b) * f (a ⊓ b)) :=
            mul_le_mul hg_le hf_le
              (mul_nonneg (hpos a ha).le (hpos b hb).le) (hg0 _ hsupS)
          _ = f (a ⊓ b) * (g (a ⊔ b) * f (a ⊔ b)) := by ring
      · have hFb : F b = 0 := by
          simp only [hF]
          exact ite_eq_right hb
        rw [hFb, mul_zero]
        exact mul_nonneg (hF_nonneg _) (hGF_nonneg _)
    · have hGFa : GF a = 0 := by
        simp only [hGF]
        exact ite_eq_right ha
      rw [hGFa, zero_mul]
      exact mul_nonneg (hF_nonneg _) (hGF_nonneg _)
  -- Apply Ahlswede–Daykin to the two finite sets, using the global
  -- nonnegativity of both extended functions.
  have hfourFunctions := four_functions_theorem GF F F GF
    (Pi.le_def.mpr hGF_nonneg) (Pi.le_def.mpr hF_nonneg)
    (Pi.le_def.mpr hF_nonneg) (Pi.le_def.mpr hGF_nonneg)
    hfour A B
  -- The lattice assumptions put the pointwise infima back in `A` and the
  -- pointwise suprema back in `B`.
  have hinfs_subset : A ⊼ B ⊆ A := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_infs.1 hz
    exact hinfAB a ha b hb
  have hsups_subset : A ⊻ B ⊆ B := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sups.1 hz
    exact hsupAB a ha b hb
  have hinfs_sum_le : ∑ x ∈ A ⊼ B, F x ≤ ∑ x ∈ A, F x :=
    sum_le_sum_of_subset_of_nonneg hinfs_subset fun x _ _ => hF_nonneg x
  have hsups_sum_le : ∑ x ∈ A ⊻ B, GF x ≤ ∑ x ∈ B, GF x :=
    sum_le_sum_of_subset_of_nonneg hsups_subset fun x _ _ => hGF_nonneg x
  -- On `A` and `B`, which are subsets of `S`, the extended functions agree
  -- with the original functions.
  have hsumA_GF : ∑ x ∈ A, GF x = ∑ x ∈ A, g x * f x :=
    sum_congr rfl fun x hx => by
      simp only [hGF]
      exact ite_eq_left (hAS hx)
  have hsumB_F : ∑ x ∈ B, F x = ∑ x ∈ B, f x :=
    sum_congr rfl fun x hx => by
      simp only [hF]
      exact ite_eq_left (hBS hx)
  have hsumA_F : ∑ x ∈ A, F x = ∑ x ∈ A, f x :=
    sum_congr rfl fun x hx => by
      simp only [hF]
      exact ite_eq_left (hAS hx)
  have hsumB_GF : ∑ x ∈ B, GF x = ∑ x ∈ B, g x * f x :=
    sum_congr rfl fun x hx => by
      simp only [hGF]
      exact ite_eq_left (hBS hx)
  calc
    (∑ x ∈ A, g x * f x) * ∑ x ∈ B, f x =
        (∑ x ∈ A, GF x) * ∑ x ∈ B, F x := by
      rw [hsumA_GF, hsumB_F]
    _ ≤ (∑ x ∈ A ⊼ B, F x) * ∑ x ∈ A ⊻ B, GF x :=
      hfourFunctions
    _ ≤ (∑ x ∈ A, F x) * ∑ x ∈ B, GF x :=
      mul_le_mul hinfs_sum_le hsups_sum_le
        (sum_nonneg fun x _ => hGF_nonneg x)
        (sum_nonneg fun x _ => hF_nonneg x)
    _ = (∑ x ∈ B, g x * f x) * ∑ x ∈ A, f x := by
      rw [hsumA_F, hsumB_GF, mul_comm]

/-! ## Normalized comparison for nonnegative functions -/

/-- The normalized finite conditional-expectation comparison for a
nonnegative monotone function.

Under the assumptions of `sum_mul_sum_le_of_affiliated`, suppose in addition
that `A` and `B` are nonempty.  Positivity of `f` on `S`, together with
`A ⊆ S` and `B ⊆ S`, then makes the total weight of each set strictly
positive.  We may therefore divide the cross-multiplied comparison by those
two weights and obtain

`condExpOn f g A ≤ condExpOn f g B`.

The supremum and infimum assumptions say that `A` is lattice-lower than `B`:
combining a point of `A` with a point of `B` sends their infimum back to `A`
and their supremum back to `B`.  Affiliation then ensures that every
nondecreasing, nonnegative `g` has a weakly lower conditional expectation on
`A` than on `B`. -/
theorem condExpOn_le_condExpOn_of_affiliated_of_nonneg {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {S A B : Finset (Fin n → ℝ)}
    (hf : Affiliated f) (hpos : ∀ x ∈ S, 0 < f x)
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    (hg : Monotone g) (hg0 : ∀ x ∈ S, 0 ≤ g x)
    (hAS : A ⊆ S) (hBS : B ⊆ S)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hsupAB : ∀ a ∈ A, ∀ b ∈ B, a ⊔ b ∈ B)
    (hinfAB : ∀ a ∈ A, ∀ b ∈ B, a ⊓ b ∈ A) :
    condExpOn f g A ≤ condExpOn f g B := by
  have hA_mass : 0 < ∑ x ∈ A, f x :=
    sum_pos_on_of_pos hpos hAS hA
  have hB_mass : 0 < ∑ x ∈ B, f x :=
    sum_pos_on_of_pos hpos hBS hB
  unfold condExpOn
  rw [div_le_div_iff₀ hA_mass hB_mass]
  exact sum_mul_sum_le_of_affiliated
    hf hpos hsub hg hg0 hAS hBS hsupAB hinfAB

/-! ## Removing the nonnegativity assumption -/

/-- The normalized finite conditional-expectation comparison for an arbitrary
monotone function.

This strengthens `condExpOn_le_condExpOn_of_affiliated_of_nonneg` by removing
the assumption that `g` is nonnegative on `S`.  Since `S` is finite and
nonempty, `g` attains a minimum at some `m ∈ S`.  Adding the constant
`c = -g m` makes `x ↦ g x + c` nonnegative throughout `S` without changing
its monotonicity.

The nonnegative comparison applies to this shifted function.  Finally,
`condExpOn_add_const` shows that both conditional expectations increased by
the same constant `c`, which can be cancelled from the two sides of the
inequality. -/
theorem condExpOn_le_condExpOn_of_affiliated {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {S A B : Finset (Fin n → ℝ)}
    (hf : Affiliated f) (hpos : ∀ x ∈ S, 0 < f x)
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    (hg : Monotone g)
    (hAS : A ⊆ S) (hBS : B ⊆ S)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hsupAB : ∀ a ∈ A, ∀ b ∈ B, a ⊔ b ∈ B)
    (hinfAB : ∀ a ∈ A, ∀ b ∈ B, a ⊓ b ∈ A) :
    condExpOn f g A ≤ condExpOn f g B := by
  -- The nonempty subset `A` supplies a point of `S`, so `S` is nonempty.
  have hS : S.Nonempty :=
    hA.mono hAS
  -- Choose a point `m` where `g` has its minimum value on the finite set `S`.
  obtain ⟨m, _hmS, hm⟩ := S.exists_min_image g hS
  -- Translate `g` so that its minimum value becomes zero.
  set c : ℝ := -g m with hc
  have hshift_nonneg : ∀ x ∈ S, 0 ≤ g x + c := by
    intro x hx
    have hmin : g m ≤ g x := hm x hx
    rw [hc]
    exact sub_nonneg.mpr hmin
  have hshift_mono : Monotone (fun x => g x + c) :=
    hg.add_const c
  -- Apply the normalized nonnegative comparison to the shifted function.
  have hshifted :=
    condExpOn_le_condExpOn_of_affiliated_of_nonneg
      hf hpos hsub hshift_mono hshift_nonneg
      hAS hBS hA hB hsupAB hinfAB
  -- Both sets have positive total weight, so adding `c` shifts both
  -- conditional expectations by exactly `c`.
  have hA_mass : 0 < ∑ x ∈ A, f x :=
    sum_pos_on_of_pos hpos hAS hA
  have hB_mass : 0 < ∑ x ∈ B, f x :=
    sum_pos_on_of_pos hpos hBS hB
  rw [condExpOn_add_const f g A c hA_mass.ne',
      condExpOn_add_const f g B c hB_mass.ne'] at hshifted
  -- Cancel the same constant from the right of both sides.
  exact (add_le_add_iff_right c).mp hshifted

end Auction.Affiliation

end

end MathEconLib
