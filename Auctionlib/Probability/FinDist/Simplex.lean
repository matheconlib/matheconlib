/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Probability.FinDist.ConditionalOn

/-!
# Dependent products of finite distributions

Dependent products of finite distributions form independent laws on profiles; marginals and
conditional masses describe coordinate beliefs. Conditional masses are zero when the conditioning
coordinate has zero probability.

## Main definitions

* `FinDist.productD`: Independent law on dependent profiles.
* `FinDist.marginalD`, `FinDist.condProbD`: Coordinate marginals and conditional masses.

## Main statements

* `FinDist.marginalD_sum_one`: Coordinate marginals sum to one.
* `FinDist.condProbD_sum_one_of_pos`: Positive-marginal conditionals sum to one.
* `FinDist.marginalD_mul_condProbD`: Conditional masses recover joint masses.

## Tags

probability, finite distributions, product distribution, marginal, conditional probability
-/

@[expose] public section

open BigOperators

namespace Auctionlib.Probability
namespace FinDist

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]

/-- Product distribution over a dependent finite profile space. -/
noncomputable def productD (d : ∀ i, FinDist (β i)) : FinDist (∀ i, β i) := by
  classical
  refine ⟨fun x ↦ ∏ i, d i (x i),
    fun x ↦ Finset.prod_nonneg fun i _ ↦ (d i).nonneg (x i), ?_⟩
  have h : ∑ x : (∀ i, β i), ∏ i, d i (x i) = ∏ i, ∑ b : β i, d i b := by
    rw [← Fintype.piFinset_univ]
    exact (Finset.prod_univ_sum (fun _ ↦ Finset.univ) (fun i b ↦ d i b)).symm
  rw [h]
  exact Finset.prod_eq_one (fun i _ ↦ (d i).sum_one)

/-- Marginal mass of a coordinate value under a distribution on dependent finite profiles. -/
noncomputable def marginalD (d : FinDist (∀ i, β i)) (i : ι) (b : β i) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : (∀ i, β i) => x i = b), d x

/-- The coordinate marginal is nonnegative. -/
lemma marginalD_nonneg (d : FinDist (∀ i, β i)) (i : ι) (b : β i) :
    0 ≤ marginalD d i b :=
  Finset.sum_nonneg fun x _ => d.nonneg x

/-- The coordinate marginals at coordinate `i` sum to one. -/
lemma marginalD_sum_one (d : FinDist (∀ i, β i)) (i : ι) :
    ∑ b : β i, marginalD d i b = 1 := by
  simp_rw [marginalD]
  rw [Finset.sum_fiberwise Finset.univ (fun x : (∀ i, β i) => x i) (fun x => d x)]
  exact d.sum_one

/-- The probability of a coordinate fiber `{y | y i = b}` is the coordinate marginal. -/
lemma probEvent_coordFiber (d : FinDist (∀ i, β i)) (i : ι) (b : β i) :
    d.probEvent {y | y i = b} = d.marginalD i b := by
  unfold probEvent marginalD
  exact Finset.sum_congr (Finset.filter_congr fun x _ => Iff.rfl) fun x _ => rfl

/-- The conditional mass of a profile given coordinate `i` has value `b`. It equals
`d x / d.marginalD i b` when `x i = b` and the marginal is positive, and zero otherwise. -/
noncomputable def condProbD (d : FinDist (∀ i, β i)) (i : ι) (b : β i)
    (x : ∀ j, β j) : ℝ :=
  d.condProb {y | y i = b} x

/-- The coordinate conditional is nonnegative. -/
lemma condProbD_nonneg (d : FinDist (∀ i, β i)) (i : ι) (b : β i) (x : ∀ j, β j) :
    0 ≤ d.condProbD i b x :=
  d.condProb_nonneg _ x

/-- A profile off the coordinate fiber `{y | y i = b}` has zero conditional probability. -/
@[simp] lemma condProbD_of_ne (d : FinDist (∀ i, β i)) (i : ι) (b : β i)
    {x : ∀ j, β j} (hx : x i ≠ b) : d.condProbD i b x = 0 :=
  d.condProb_eq_zero_of_notMem _ hx

/-- On the coordinate fiber with positive marginal, the conditional is `d x / d.marginalD i b`. -/
lemma condProbD_eq_of_pos (d : FinDist (∀ i, β i)) (i : ι) (b : β i)
    {x : ∀ j, β j} (hx : x i = b) (hpos : 0 < d.marginalD i b) :
    d.condProbD i b x = d x / d.marginalD i b := by
  rw [condProbD, ← probEvent_coordFiber d i b] at *
  exact d.condProb_eq_of_pos _ hx hpos

/-- The coordinate conditional vanishes everywhere when the conditioning marginal is zero. -/
lemma condProbD_eq_zero_of_not_pos (d : FinDist (∀ i, β i)) (i : ι) (b : β i)
    (x : ∀ j, β j) (hnot : ¬ 0 < d.marginalD i b) :
    d.condProbD i b x = 0 :=
  if_neg fun h => hnot (probEvent_coordFiber d i b ▸ h.2)

/-- On a positive-mass coordinate fiber the conditional distribution sums to one. -/
lemma condProbD_sum_one_of_pos (d : FinDist (∀ i, β i)) (i : ι) (b : β i)
    (hpos : 0 < d.marginalD i b) :
    ∑ x : ∀ j, β j, d.condProbD i b x = 1 :=
  d.condProb_sum_one_of_pos _ (probEvent_coordFiber d i b ▸ hpos)

/-- Coordinate marginals of a point mass are point masses at the prescribed coordinate. -/
@[simp] lemma marginalD_pure (x : ∀ j, β j) (i : ι) (b : β i) :
    (FinDist.pure x).marginalD i b = if x i = b then 1 else 0 := by
  simp [marginalD]

/-- A profile's mass does not exceed the marginal mass of any of its coordinates. -/
lemma pmf_le_marginalD (d : FinDist (∀ i, β i)) (i : ι) (x : ∀ j, β j) :
    d x ≤ d.marginalD i (x i) := by
  exact Finset.single_le_sum (fun y _ => d.nonneg y) (by simp)

/-- Multiplying a conditional mass by the conditioning marginal recovers the joint mass on its
coordinate fiber, including zero-mass fibers. -/
lemma marginalD_mul_condProbD (d : FinDist (∀ i, β i)) (i : ι) (b : β i)
    (x : ∀ j, β j) :
    d.marginalD i b * d.condProbD i b x = if x i = b then d x else 0 := by
  by_cases hx : x i = b
  · rw [if_pos hx]
    by_cases hp : 0 < d.marginalD i b
    · rw [d.condProbD_eq_of_pos i b hx hp]
      exact mul_div_cancel₀ _ hp.ne'
    · have hm : d.marginalD i b = 0 := le_antisymm (le_of_not_gt hp)
        (d.marginalD_nonneg i b)
      have hx0 : d x = 0 := le_antisymm
        (by simpa [hx, hm] using d.pmf_le_marginalD i x) (d.nonneg x)
      simp [hm, hx0]
  · rw [if_neg hx, d.condProbD_of_ne i b hx, mul_zero]

end FinDist

end Auctionlib.Probability
