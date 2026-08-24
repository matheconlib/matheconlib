/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Mechanism.Feasible
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Highest-Score Allocations

The highest-score allocation awards the unit to a bidder with a nonnegative maximal score. Ties are
broken in favor of the least bidder index.
-/

@[expose] public section

open Function Set

namespace Mechanism

variable {n : ℕ}

/-- Bidder `i` is the top scorer at `θ`. The last field implements the least-index tie break. -/
@[mk_iff]
structure IsTopScorer (v : Fin n → ℝ → ℝ) (θ : Fin n → ℝ) (i : Fin n) : Prop where
  nonneg : 0 ≤ v i (θ i)
  le : ∀ j, v j (θ j) ≤ v i (θ i)
  lt_of_lt : ∀ j, j < i → v j (θ j) < v i (θ i)

/-- The least-index tie break makes the top scorer unique. -/
theorem IsTopScorer.unique {v : Fin n → ℝ → ℝ} {θ : Fin n → ℝ} {i i' : Fin n}
    (hi : IsTopScorer v θ i) (hi' : IsTopScorer v θ i') : i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd (hi'.lt_of_lt i hlt) (not_lt.mpr (hi.le i'))
  · exact heq
  · exact absurd (hi.lt_of_lt i' hgt) (not_lt.mpr (hi'.le i))

/-- The set of profiles where bidder `i` is the top scorer is measurable. -/
theorem measurableSet_isTopScorer (v : Fin n → ℝ → ℝ)
    (hv : ∀ i, Measurable (v i)) (i : Fin n) :
    MeasurableSet {θ : Fin n → ℝ | IsTopScorer v θ i} := by
  have hvi : ∀ j : Fin n, Measurable (fun θ : Fin n → ℝ ↦ v j (θ j)) :=
    fun j ↦ (hv j).comp (measurable_pi_apply j)
  have hnonneg : MeasurableSet {θ : Fin n → ℝ | 0 ≤ v i (θ i)} :=
    measurableSet_le measurable_const (hvi i)
  have hmax : MeasurableSet {θ : Fin n → ℝ | ∀ j, v j (θ j) ≤ v i (θ i)} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j ↦ measurableSet_le (hvi j) (hvi i))
  have htie : MeasurableSet
      {θ : Fin n → ℝ | ∀ j, j < i → v j (θ j) < v i (θ i)} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter (fun j ↦ ?_)
    rcases lt_or_ge j i with hji | hji
    · simpa [hji] using measurableSet_lt (hvi j) (hvi i)
    · simp [not_lt.mpr hji]
  have heq : {θ : Fin n → ℝ | IsTopScorer v θ i} =
      {θ | 0 ≤ v i (θ i)} ∩ {θ | ∀ j, v j (θ j) ≤ v i (θ i)} ∩
        {θ | ∀ j, j < i → v j (θ j) < v i (θ i)} := by
    ext θ
    simp only [isTopScorer_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  rw [heq]
  exact (hnonneg.inter hmax).inter htie

/-- Award one unit to the unique top scorer and zero to every other bidder. -/
noncomputable def highestScoreAlloc (v : Fin n → ℝ → ℝ) :
    Fin n → (Fin n → ℝ) → ℝ :=
  fun i ↦ { θ : Fin n → ℝ | IsTopScorer v θ i }.indicator (fun _ ↦ 1)

/-- A top scorer receives the unit. -/
@[simp] lemma highestScoreAlloc_of_isTopScorer {v : Fin n → ℝ → ℝ}
    {θ : Fin n → ℝ} {i : Fin n} (h : IsTopScorer v θ i) :
    highestScoreAlloc v i θ = 1 := by
  exact Set.indicator_of_mem h (fun _ ↦ (1 : ℝ))

/-- A bidder that is not the top scorer receives zero. -/
@[simp] lemma highestScoreAlloc_of_not_isTopScorer {v : Fin n → ℝ → ℝ}
    {θ : Fin n → ℝ} {i : Fin n} (h : ¬ IsTopScorer v θ i) :
    highestScoreAlloc v i θ = 0 := by
  exact Set.indicator_of_notMem h (fun _ ↦ (1 : ℝ))

lemma highestScoreAlloc_nonneg (v : Fin n → ℝ → ℝ) (i : Fin n) (θ : Fin n → ℝ) :
    0 ≤ highestScoreAlloc v i θ :=
  Set.indicator_nonneg (fun _ _ ↦ zero_le_one) θ

lemma highestScoreAlloc_le_one (v : Fin n → ℝ → ℝ) (i : Fin n) (θ : Fin n → ℝ) :
    highestScoreAlloc v i θ ≤ 1 := by
  by_cases h : IsTopScorer v θ i
  · rw [highestScoreAlloc_of_isTopScorer h]
  · rw [highestScoreAlloc_of_not_isTopScorer h]
    exact zero_le_one

lemma highestScoreAlloc_mem_Icc (v : Fin n → ℝ → ℝ) (i : Fin n) (θ : Fin n → ℝ) :
    highestScoreAlloc v i θ ∈ Icc 0 1 :=
  ⟨highestScoreAlloc_nonneg v i θ, highestScoreAlloc_le_one v i θ⟩

/-- At most one unit is allocated by the highest-score rule. -/
lemma sum_highestScoreAlloc_le_one (v : Fin n → ℝ → ℝ) (θ : Fin n → ℝ) :
    ∑ i, highestScoreAlloc v i θ ≤ 1 := by
  by_cases hex : ∃ i, IsTopScorer v θ i
  · obtain ⟨w, hw⟩ := hex
    have hsum := Finset.sum_eq_single_of_mem (a := w) (Finset.mem_univ w)
      (f := fun i ↦ highestScoreAlloc v i θ) (fun i _ hiw ↦ by
        change highestScoreAlloc v i θ = 0
        rw [highestScoreAlloc_of_not_isTopScorer]
        exact fun hi ↦ hiw (hi.unique hw))
    rw [hsum]
    change highestScoreAlloc v w θ ≤ 1
    rw [highestScoreAlloc_of_isTopScorer hw]
  · push_neg at hex
    simp only [highestScoreAlloc_of_not_isTopScorer (hex _), Finset.sum_const_zero]
    exact zero_le_one

lemma measurable_highestScoreAlloc (v : Fin n → ℝ → ℝ)
    (hv : ∀ i, Measurable (v i)) (i : Fin n) :
    Measurable (highestScoreAlloc v i) :=
  measurable_const.indicator (measurableSet_isTopScorer v hv i)

/-- If the maximal score is nonnegative, a top scorer exists and attains it. -/
lemma exists_isTopScorer_of_sup'_nonneg [NeZero n] (v : Fin n → ℝ → ℝ)
    (θ : Fin n → ℝ)
    (hm : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ v i (θ i))) :
    ∃ w, IsTopScorer v θ w ∧
      v w (θ w) = Finset.univ.sup' Finset.univ_nonempty (fun i ↦ v i (θ i)) := by
  set m := Finset.univ.sup' Finset.univ_nonempty (fun i ↦ v i (θ i))
  obtain ⟨i₀, _, hi₀⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ v i (θ i))
  set S := Finset.univ.filter (fun i ↦ v i (θ i) = m)
  have hSne : S.Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀.symm⟩⟩
  refine ⟨S.min' hSne, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [(Finset.mem_filter.mp (S.min'_mem hSne)).2]
    exact hm
  · intro j
    rw [(Finset.mem_filter.mp (S.min'_mem hSne)).2]
    exact Finset.le_sup' (fun i ↦ v i (θ i)) (Finset.mem_univ j)
  · intro j hjw
    rw [(Finset.mem_filter.mp (S.min'_mem hSne)).2]
    have hjnotS : j ∉ S := fun hjS ↦
      absurd (S.min'_le j hjS) (not_le.mpr hjw)
    have hjne : v j (θ j) ≠ m := fun h ↦
      hjnotS (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
    exact lt_of_le_of_ne
      (Finset.le_sup' (fun i ↦ v i (θ i)) (Finset.mem_univ j)) hjne
  · exact (Finset.mem_filter.mp (S.min'_mem hSne)).2

/-- Pointwise surplus attained by the highest-score allocation. -/
theorem sum_score_mul_highestScoreAlloc [NeZero n]
    (v : Fin n → ℝ → ℝ) (θ : Fin n → ℝ) :
    ∑ i, v i (θ i) * highestScoreAlloc v i θ =
      max 0 (Finset.univ.sup' Finset.univ_nonempty (fun i ↦ v i (θ i))) := by
  set m := Finset.univ.sup' Finset.univ_nonempty (fun i ↦ v i (θ i))
  by_cases hm : 0 ≤ m
  · obtain ⟨w, hw, hwm⟩ := exists_isTopScorer_of_sup'_nonneg v θ hm
    rw [max_eq_right hm]
    have hsum := Finset.sum_eq_single_of_mem (a := w) (Finset.mem_univ w)
      (f := fun i ↦ v i (θ i) * highestScoreAlloc v i θ) (fun i _ hiw ↦ by
        change v i (θ i) * highestScoreAlloc v i θ = 0
        rw [highestScoreAlloc_of_not_isTopScorer, mul_zero]
        exact fun hi ↦ hiw (hi.unique hw))
    rw [hsum]
    change v w (θ w) * highestScoreAlloc v w θ = m
    rw [highestScoreAlloc_of_isTopScorer hw, mul_one, hwm]
  · push_neg at hm
    rw [max_eq_left hm.le]
    have hzero : ∀ i, v i (θ i) * highestScoreAlloc v i θ = 0 := by
      intro i
      rw [highestScoreAlloc_of_not_isTopScorer, mul_zero]
      intro hi
      exact (not_le.mpr hm)
        (le_trans hi.nonneg
          (Finset.le_sup' (fun j ↦ v j (θ j)) (Finset.mem_univ i)))
    simp [hzero]

/-- Any feasible allocation has pointwise score surplus at most the highest-score allocation. -/
theorem sum_score_mul_x_le [NeZero n] (M : Mechanism n) [M.IsFeasible]
    (v : Fin n → ℝ → ℝ) (θ : Fin n → ℝ) :
    ∑ i, v i (θ i) * M.x i θ ≤
      max 0 (Finset.univ.sup' Finset.univ_nonempty (fun i ↦ v i (θ i))) := by
  set V := max 0 (Finset.univ.sup' Finset.univ_nonempty (fun i ↦ v i (θ i)))
  have hV0 : 0 ≤ V := le_max_left _ _
  have hv_le : ∀ i, v i (θ i) ≤ V := fun i ↦
    le_trans (Finset.le_sup' (fun j ↦ v j (θ j)) (Finset.mem_univ i))
      (le_max_right _ _)
  calc
    ∑ i, v i (θ i) * M.x i θ ≤ ∑ i, V * M.x i θ :=
      Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_right (hv_le i) (IsFeasible.x_nonneg (M := M) i θ)
    _ = V * ∑ i, M.x i θ := by rw [Finset.mul_sum]
    _ ≤ V * 1 := mul_le_mul_of_nonneg_left
      (IsFeasible.sum_x_le_one (M := M) θ) hV0
    _ = V := mul_one V

/-- Raising bidder `i`'s score preserves top-scorer status. -/
lemma isTopScorer_update_of_le (v : Fin n → ℝ → ℝ)
    {S : Set ℝ} {i : Fin n} (hmono : MonotoneOn (v i) S)
    {θ : Fin n → ℝ} {t t' : ℝ} (ht : t ∈ S) (ht' : t' ∈ S)
    (htt' : t ≤ t') (h : IsTopScorer v (update θ i t) i) :
    IsTopScorer v (update θ i t') i := by
  have hvle : v i t ≤ v i t' := hmono ht ht' htt'
  obtain ⟨h0, hmax, hlt⟩ := h
  rw [update_self] at h0 hmax hlt
  refine ⟨by rw [update_self]; exact le_trans h0 hvle, fun j ↦ ?_, fun j hji ↦ ?_⟩
  · rw [update_self]
    by_cases hj : j = i
    · subst hj
      rw [update_self]
    · rw [update_of_ne hj]
      exact le_trans (by simpa [update_of_ne hj] using hmax j) hvle
  · rw [update_self]
    have hjne : j ≠ i := ne_of_lt hji
    rw [update_of_ne hjne]
    exact lt_of_lt_of_le (by simpa [update_of_ne hjne] using hlt j hji) hvle

/-- Top-scorer status depends on an own report only through its score. -/
lemma isTopScorer_update_congr (v : Fin n → ℝ → ℝ)
    {i : Fin n} {θ : Fin n → ℝ} {t t' : ℝ} (h : v i t = v i t')
    (htop : IsTopScorer v (update θ i t) i) :
    IsTopScorer v (update θ i t') i := by
  obtain ⟨h0, hmax, hlt⟩ := htop
  rw [update_self] at h0 hmax hlt
  refine ⟨by rw [update_self, ← h]; exact h0, fun j ↦ ?_, fun j hji ↦ ?_⟩
  · rw [update_self, ← h]
    by_cases hj : j = i
    · subst hj
      rw [update_self]
      exact h.ge
    · simpa [update_of_ne hj] using hmax j
  · rw [update_self, ← h]
    have hjne : j ≠ i := ne_of_lt hji
    simpa [update_of_ne hjne] using hlt j hji

/-- The winner indicator is monotone in a bidder's own report when its score is. -/
lemma highestScoreAlloc_update_le (v : Fin n → ℝ → ℝ)
    {S : Set ℝ} {i : Fin n} (hmono : MonotoneOn (v i) S)
    {θ : Fin n → ℝ} {t t' : ℝ} (ht : t ∈ S) (ht' : t' ∈ S)
    (htt' : t ≤ t') :
    highestScoreAlloc v i (update θ i t) ≤
      highestScoreAlloc v i (update θ i t') := by
  by_cases htop : IsTopScorer v (update θ i t) i
  · rw [highestScoreAlloc_of_isTopScorer htop,
      highestScoreAlloc_of_isTopScorer
        (isTopScorer_update_of_le v hmono ht ht' htt' htop)]
  · rw [highestScoreAlloc_of_not_isTopScorer htop]
    exact highestScoreAlloc_nonneg v i _

/-- Equal own scores give equal winner indicators. -/
lemma highestScoreAlloc_update_congr (v : Fin n → ℝ → ℝ)
    {i : Fin n} {θ : Fin n → ℝ} {t t' : ℝ} (h : v i t = v i t') :
    highestScoreAlloc v i (update θ i t) =
      highestScoreAlloc v i (update θ i t') := by
  by_cases htop : IsTopScorer v (update θ i t) i
  · rw [highestScoreAlloc_of_isTopScorer htop,
      highestScoreAlloc_of_isTopScorer (isTopScorer_update_congr v h htop)]
  · rw [highestScoreAlloc_of_not_isTopScorer htop,
      highestScoreAlloc_of_not_isTopScorer]
    exact fun htop' ↦ htop (isTopScorer_update_congr v h.symm htop')

/-- Build a mechanism from the highest-score allocation and any payment rule. -/
noncomputable def ofHighestScore (v : Fin n → ℝ → ℝ) (hv : ∀ i, Measurable (v i))
    (t : Fin n → (Fin n → ℝ) → ℝ) : Mechanism n where
  x := highestScoreAlloc v
  x_measurable := measurable_highestScoreAlloc v hv
  t := t

@[simp] lemma ofHighestScore_x (v : Fin n → ℝ → ℝ) (hv : ∀ i, Measurable (v i))
    (t : Fin n → (Fin n → ℝ) → ℝ) :
    (ofHighestScore v hv t).x = highestScoreAlloc v := rfl

@[simp] lemma ofHighestScore_t (v : Fin n → ℝ → ℝ) (hv : ∀ i, Measurable (v i))
    (t : Fin n → (Fin n → ℝ) → ℝ) :
    (ofHighestScore v hv t).t = t := rfl

instance instIsFeasibleOfHighestScore (v : Fin n → ℝ → ℝ)
    (hv : ∀ i, Measurable (v i)) (t : Fin n → (Fin n → ℝ) → ℝ) :
    (ofHighestScore v hv t).IsFeasible where
  x_nonneg := highestScoreAlloc_nonneg v
  sum_x_le_one := sum_highestScoreAlloc_le_one v

end Mechanism

end
