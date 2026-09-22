/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Probability distributions over finite types

A distribution `FinDist α` assigns nonnegative real probability masses summing to one to a finite
type `α`. Its support consists of outcomes with positive mass, and its modes are outcomes of
maximal probability.

Point masses, uniform distributions, binary convex combinations, and finite mixtures provide
elementary distributions. Every probability is at most one, and a mixture with both weights
positive has support equal to the union of its components' supports.

## Main definitions

* `FinDist`: A pmf `α → ℝ` that is nonnegative and sums to one.
* `FinDist.support`: The set of outcomes with positive probability.
* `FinDist.IsMode`: The probability mass is maximized at an outcome.
* `FinDist.pure`: Point mass at a single outcome.
* `FinDist.uniform`: The uniform distribution on a nonempty finite type.
* `FinDist.mixture`: Convex combination of two distributions.
* `FinDist.finMixture`: Finite mixture indexed by a finite type.

## Main statements

* `FinDist.pmf_le_one`: Each probability is at most one.
* `FinDist.support_mixture`: Support of a strict mixture is the union of supports.

## Tags

probability, finite distributions, pmf, dirac, uniform, mixture
-/

@[expose] public section

open BigOperators

namespace Auctionlib.Probability

/-- A probability distribution over a finite type `α`. -/
abbrev FinDist (α : Type*) [Fintype α] : Type _ := stdSimplex ℝ α

namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Probability mass assigned to each outcome. -/
abbrev pmf (d : FinDist α) : α → ℝ := d.val

/-- Probability masses are nonnegative. -/
lemma nonneg (d : FinDist α) (a : α) : 0 ≤ d.pmf a := d.2.1 a

/-- Total probability mass is one. -/
lemma sum_one (d : FinDist α) : ∑ a, d.pmf a = 1 := d.2.2

/-- The probability mass function agrees with evaluation of the distribution. -/
@[simp] lemma pmf_eq_coe (d : FinDist α) (a : α) : d.pmf a = d a := rfl

/-- The finite set of outcomes with positive probability. -/
noncomputable def support (d : FinDist α) : Finset α :=
  Finset.univ.filter (fun a ↦ 0 < d.pmf a)

/-- A mode maximizes probability mass. Modes need not be unique; every outcome is a mode of the
uniform distribution. -/
def IsMode (d : FinDist α) (a : α) : Prop :=
  ∀ b, d.pmf b ≤ d.pmf a

/-- Each probability is at most one. -/
lemma pmf_le_one (d : FinDist α) (a : α) : d.pmf a ≤ 1 :=
  d.sum_one ▸ Finset.single_le_sum (fun b _ ↦ d.nonneg b) (Finset.mem_univ a)

/-- The two probability masses of a distribution on `Fin 2` sum to one. -/
lemma sum_pmf_two (d : FinDist (Fin 2)) : d.pmf 0 + d.pmf 1 = 1 := by
  have h := d.sum_one
  rwa [Fin.sum_univ_two] at h

/-- Every distribution assigns positive probability to some outcome. -/
lemma exists_pmf_pos (d : FinDist α) : ∃ a, 0 < d.pmf a := by
  by_contra h
  push Not at h
  have hzero : ∑ a, d.pmf a = 0 :=
    Finset.sum_eq_zero fun a _ ↦ le_antisymm (h a) (d.nonneg a)
  rw [d.sum_one] at hzero
  norm_num at hzero

/-- Two distributions are equal when their pmfs agree pointwise. -/
@[ext] lemma ext (d₁ d₂ : FinDist α) (h : ∀ a, d₁.pmf a = d₂.pmf a) : d₁ = d₂ := by
  exact Subtype.ext (funext h)

/-! ### Pure (Dirac) distribution -/

section Pure

variable [DecidableEq α]

/-- The point mass assigning probability one to a single outcome. -/
noncomputable def pure (a : α) : FinDist α :=
  ⟨fun b ↦ if a = b then 1 else 0, ite_eq_mem_stdSimplex ℝ a⟩

/-- A point mass assigns one to its designated outcome and zero to every other outcome. -/
@[simp] lemma pure_apply (a b : α) :
    (FinDist.pure a : FinDist α) b = if a = b then 1 else 0 := rfl

/-- The probability mass function of a point mass is the indicator of its outcome. -/
lemma pure_pmf (a b : α) : (FinDist.pure a).pmf b = if a = b then 1 else 0 := rfl

/-- A point mass assigns probability one to its own outcome. -/
lemma pure_pmf_self (a : α) : (FinDist.pure a).pmf a = 1 := by
  rw [pure_pmf, if_pos rfl]

/-- A point mass assigns probability zero to every other outcome. -/
lemma pure_pmf_of_ne {a b : α} (h : a ≠ b) : (FinDist.pure a).pmf b = 0 := by
  rw [pure_pmf, if_neg h]

/-- A distribution assigning probability one to an outcome is the point mass at that outcome. -/
lemma eq_pure_of_pmf_eq_one {d : FinDist α} {a : α} (h : d.pmf a = 1) :
    d = FinDist.pure a := by
  -- The remaining outcomes share total mass `1 - 1 = 0`, and each term is nonnegative.
  have herase : ∑ b ∈ Finset.univ.erase a, d.pmf b = 0 := by
    have hsplit := Finset.add_sum_erase Finset.univ d.pmf (Finset.mem_univ a)
    have hsum := d.sum_one
    linarith
  have hzero : ∀ b, b ≠ a → d.pmf b = 0 := fun b hb ↦
    (Finset.sum_eq_zero_iff_of_nonneg (fun c _ ↦ d.nonneg c)).mp herase b
      (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩)
  apply FinDist.ext
  intro b
  by_cases hb : b = a
  · subst hb
    rw [h, pure_pmf_self]
  · rw [hzero b hb, pure_pmf_of_ne (fun hab ↦ hb hab.symm)]

/-- Two distributions on `Fin 2` with disjoint supports are opposite point masses. -/
lemma eq_pure_pair_of_disjoint_fin_two {d₁ d₂ : FinDist (Fin 2)}
    (h : ∀ m, ¬(0 < d₁.pmf m ∧ 0 < d₂.pmf m)) :
    ∃ m₁ m₂ : Fin 2, m₁ ≠ m₂ ∧ d₁ = FinDist.pure m₁ ∧ d₂ = FinDist.pure m₂ := by
  obtain ⟨m₁, hm₁⟩ := d₁.exists_pmf_pos
  -- With only two outcomes, disjoint nonempty supports must be complementary singletons.
  have h₂m₁ : d₂.pmf m₁ = 0 := by
    by_contra hne
    exact h m₁ ⟨hm₁, lt_of_le_of_ne (d₂.nonneg m₁) (Ne.symm hne)⟩
  by_cases hcase : m₁ = 0
  · subst hcase
    have hd₂ : d₂ = FinDist.pure 1 :=
      eq_pure_of_pmf_eq_one (by linarith [d₂.sum_pmf_two])
    have h₁1 : d₁.pmf 1 = 0 := by
      by_contra hne
      refine h 1 ⟨lt_of_le_of_ne (d₁.nonneg 1) (Ne.symm hne), ?_⟩
      rw [hd₂, pure_pmf_self]
      norm_num
    have hd₁ : d₁ = FinDist.pure 0 :=
      eq_pure_of_pmf_eq_one (by linarith [d₁.sum_pmf_two])
    exact ⟨0, 1, by decide, hd₁, hd₂⟩
  · have hcase1 : m₁ = 1 := by omega
    subst hcase1
    have hd₂ : d₂ = FinDist.pure 0 :=
      eq_pure_of_pmf_eq_one (by linarith [d₂.sum_pmf_two])
    have h₁0 : d₁.pmf 0 = 0 := by
      by_contra hne
      refine h 0 ⟨lt_of_le_of_ne (d₁.nonneg 0) (Ne.symm hne), ?_⟩
      rw [hd₂, pure_pmf_self]
      norm_num
    have hd₁ : d₁ = FinDist.pure 1 :=
      eq_pure_of_pmf_eq_one (by linarith [d₁.sum_pmf_two])
    exact ⟨1, 0, by decide, hd₁, hd₂⟩

/-- The support of a point mass is the singleton at that outcome. -/
lemma support_pure (a : α) : (FinDist.pure a).support = {a} := by
  ext b
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, pure_pmf]
  split_ifs with hab <;> simp [hab, eq_comm]

end Pure

/-! ### Uniform distribution -/

/-- Uniform distribution over a nonempty finite type. -/
noncomputable def uniform [Nonempty α] : FinDist α := stdSimplex.barycenter

/-- Uniform probability is the reciprocal of the number of outcomes. -/
lemma uniform_pmf [Nonempty α] (a : α) :
    (FinDist.uniform (α := α)).pmf a = (Fintype.card α : ℝ)⁻¹ := rfl

/-! ### Mixtures -/

/-- The convex combination assigning weights `t` and `1 - t` to two distributions. -/
noncomputable def mixture (t : unitInterval) (d₁ d₂ : FinDist α) : FinDist α :=
  ⟨fun a ↦ (t : ℝ) * d₁.pmf a + (1 - (t : ℝ)) * d₂.pmf a,
    fun a ↦ add_nonneg (mul_nonneg t.2.1 (d₁.nonneg a))
      (mul_nonneg (by linarith [t.2.2]) (d₂.nonneg a)), by
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [d₁.sum_one, d₂.sum_one]
    ring⟩

/-- A mixture's probability mass is the corresponding convex combination of component masses. -/
lemma mixture_pmf (t : unitInterval) (d₁ d₂ : FinDist α) (a : α) :
    (FinDist.mixture t d₁ d₂).pmf a = (t : ℝ) * d₁.pmf a + (1 - (t : ℝ)) * d₂.pmf a := rfl

/-- The support of a strict mixture is the union of the two supports. -/
lemma support_mixture [DecidableEq α] (t : unitInterval) (d₁ d₂ : FinDist α)
    (h₀ : (0 : ℝ) < (t : ℝ)) (h₁ : (t : ℝ) < 1) :
    (FinDist.mixture t d₁ d₂).support = d₁.support ∪ d₂.support := by
  ext a
  simp only [support, mixture_pmf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hmass₁_eq_zero := le_antisymm hcon.1 (d₁.nonneg a)
    have hmass₂_eq_zero := le_antisymm hcon.2 (d₂.nonneg a)
    simp only [hmass₁_eq_zero, hmass₂_eq_zero, mul_zero, add_zero, lt_self_iff_false] at h
  · rintro (h | h)
    · exact add_pos_of_pos_of_nonneg (mul_pos h₀ h)
        (mul_nonneg (by linarith) (d₂.nonneg a))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (le_of_lt h₀) (d₁.nonneg a))
        (mul_pos (by linarith) h)

/-- A finite mixture assigns each outcome the weighted average of its component probabilities. A
Bayes-plausible splitting represents a prior as such a mixture of posterior beliefs. -/
noncomputable def finMixture (weights : FinDist β) (beliefs : β → FinDist α) :
    FinDist α :=
  ⟨fun a ↦ ∑ s, weights.pmf s * (beliefs s).pmf a,
    fun a ↦ Finset.sum_nonneg fun s _ ↦ mul_nonneg (weights.nonneg s) ((beliefs s).nonneg a), by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp_rw [fun s ↦ (beliefs s).sum_one, mul_one, weights.sum_one]⟩

/-- A finite mixture's probability mass is the weighted sum of component masses. -/
@[simp] lemma finMixture_pmf (weights : FinDist β) (beliefs : β → FinDist α)
    (a : α) :
    (FinDist.finMixture weights beliefs).pmf a = ∑ s, weights.pmf s * (beliefs s).pmf a :=
  rfl

end FinDist

end Auctionlib.Probability
