/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.Probability.FinDist.Basic

/-!
# Expectations for finite distributions

Expectation under a finite distribution is the probability-weighted sum of a function taking values
in a real module. It is linear, and taking a binary mixture of distributions takes the same convex
combination of expectations. Expectation is monotone when the order respects addition and
nonnegative scalar multiplication.

Distributions supported on maximizers achieve maximal expectation. Conversely, if a distribution's
expectation bounds the function everywhere, every outcome with positive probability attains that
expectation.

## Main definitions

* `FinDist.expect`: Expectation as a finite sum.

## Main statements

* `FinDist.expect_add`: Additivity of expectation.
* `FinDist.expect_mixture`: Expectation of a binary mixture.
* `FinDist.expect_le_expect_of_support_max`: Distributions supported on maximizers maximize
  expectation.
* `FinDist.eq_expect_of_pmf_pos_of_forall_le_expect`: Outcomes with positive probability attain a
  maximal expectation.

## Tags

probability, finite distributions, expectation
-/

@[expose] public section

open BigOperators

namespace MathEconLib.Probability

namespace FinDist

variable {α : Type*} [Fintype α]

section Module

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

/-- Expected value for a finite distribution. -/
noncomputable def expect (d : FinDist α) (f : α → V) : V :=
  ∑ a, d.pmf a • f a

/-- Expectation is its probability-weighted sum. -/
lemma expect_eq_sum (d : FinDist α) (f : α → V) :
    d.expect f = ∑ a, d.pmf a • f a := rfl

/-- The expectation of a constant is that constant. -/
lemma expect_const (d : FinDist α) (c : V) : d.expect (fun _ ↦ c) = c := by
  rw [expect, ← Finset.sum_smul, d.sum_one, one_smul]

/-- Expectation is additive. -/
lemma expect_add (d : FinDist α) (f g : α → V) :
    d.expect (f + g) = d.expect f + d.expect g := by
  simp only [expect, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Expectation is homogeneous in scalar multiplication. -/
lemma expect_smul (d : FinDist α) (c : ℝ) (f : α → V) :
    d.expect (c • f) = c • d.expect f := by
  simp only [expect, Pi.smul_apply, smul_comm (d.pmf _) c, Finset.smul_sum]

section Pure

variable [DecidableEq α]

/-- Expectation under a point mass is evaluation at its outcome. -/
lemma expect_pure (a : α) (f : α → V) : (FinDist.pure a).expect f = f a := by
  simp only [expect, pure_pmf]
  simp

end Pure

/-- A distribution assigning probability one to `a` has expectation `f a`. -/
lemma expect_of_pmf_eq_one {d : FinDist α} {a : α} (h : d.pmf a = 1) (f : α → V) :
    d.expect f = f a := by
  classical
  rw [eq_pure_of_pmf_eq_one h, expect_pure]

/-- Expectation of a binary mixture is the convex combination of the two expectations. -/
lemma expect_mixture (t : unitInterval) (d₁ d₂ : FinDist α) (f : α → V) :
    (FinDist.mixture t d₁ d₂).expect f =
      (t : ℝ) • d₁.expect f + (1 - (t : ℝ)) • d₂.expect f := by
  simp only [expect, mixture_pmf, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

section Ordered

variable [PartialOrder V] [IsOrderedAddMonoid V] [PosSMulMono ℝ V]

/-- The expectation of a nonnegative function is nonnegative. -/
lemma expect_nonneg (d : FinDist α) (f : α → V) (h : ∀ a, 0 ≤ f a) :
    0 ≤ d.expect f :=
  Finset.sum_nonneg fun a _ ↦ smul_nonneg (d.nonneg a) (h a)

/-- Expectation is monotone in the integrand. -/
lemma expect_mono (d : FinDist α) (f g : α → V) (h : ∀ a, f a ≤ g a) :
    d.expect f ≤ d.expect g :=
  Finset.sum_le_sum fun a _ ↦ smul_le_smul_of_nonneg_left (h a) (d.nonneg a)

/-- A distribution supported on maximizers of `f` has at least as large an expectation as every
other distribution. -/
lemma expect_le_expect_of_support_max {d : FinDist α} {f : α → V}
    (h : ∀ a, 0 < d.pmf a → ∀ b, f b ≤ f a) (d' : FinDist α) :
    d'.expect f ≤ d.expect f := by
  obtain ⟨a₀, ha₀⟩ := d.exists_pmf_pos
  have hmax : ∀ b, f b ≤ f a₀ := h a₀ ha₀
  have hexpect_le : d'.expect f ≤ f a₀ :=
    le_of_le_of_eq (expect_mono d' f (fun _ ↦ f a₀) hmax) (expect_const d' (f a₀))
  have hexpect_eq : d.expect f = f a₀ := by
    calc
      d.expect f = d.expect (fun _ ↦ f a₀) := by
        apply Finset.sum_congr rfl
        intro a _
        rcases eq_or_lt_of_le (d.nonneg a) with hz | hp
        · simp only [← hz, zero_smul]
        · rw [le_antisymm (hmax a) (h a hp a₀)]
      _ = f a₀ := expect_const d _
  exact hexpect_eq ▸ hexpect_le

end Ordered

end Module

/-- If the expectation of `f` bounds `f` everywhere, every outcome with positive probability
attains that expectation. -/
lemma eq_expect_of_pmf_pos_of_forall_le_expect {V : Type*} [AddCommGroup V] [Module ℝ V]
    [PartialOrder V] [IsOrderedAddMonoid V] [PosSMulMono ℝ V]
    {d : FinDist α} {f : α → V} (h : ∀ b, f b ≤ d.expect f) {a : α} (ha : 0 < d.pmf a) :
    f a = d.expect f := by
  have hnonneg : ∀ b ∈ Finset.univ, 0 ≤ d.pmf b • (d.expect f - f b) :=
    fun b _ ↦ smul_nonneg (d.nonneg b) (sub_nonneg.mpr (h b))
  have hsum : ∑ b, d.pmf b • (d.expect f - f b) = 0 := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, d.sum_one, one_smul]
    exact sub_self _
  have hterm : d.pmf a • (d.expect f - f a) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum a (Finset.mem_univ a)
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hterm).resolve_left ha.ne')).symm

end FinDist

end MathEconLib.Probability
