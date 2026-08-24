/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Mechanism.Basic

/-!
# Feasible Mechanisms

This file adds the single-unit feasibility condition for an allocation rule. It is separate from
`Mechanism.Basic`, whose declarations are design-first.
-/

@[expose] public section

open Set

namespace Mechanism

variable {n : ℕ} (M : Mechanism n)

/-- A single-unit allocation is feasible when every allocation is nonnegative and the total
allocation is at most one at every report profile. -/
class IsFeasible : Prop where
  x_nonneg : ∀ i b, 0 ≤ M.x i b
  sum_x_le_one : ∀ b, ∑ i, M.x i b ≤ 1

/-- Every component of a feasible allocation is at most one. -/
lemma IsFeasible.x_le_one [M.IsFeasible] (i : Fin n) (b : Fin n → ℝ) :
    M.x i b ≤ 1 := by
  calc
    M.x i b ≤ ∑ j, M.x j b :=
      Finset.single_le_sum (fun j _ ↦ IsFeasible.x_nonneg (M := M) j b)
        (Finset.mem_univ i)
    _ ≤ 1 := IsFeasible.sum_x_le_one (M := M) b

/-- A feasible allocation has values in `[0, 1]`. -/
instance IsFeasible.instHasValidAllocation [M.IsFeasible] : M.HasValidAllocation where
  x_range i b := ⟨IsFeasible.x_nonneg (M := M) i b, IsFeasible.x_le_one (M := M) i b⟩

/-- The efficient allocation from `Mechanism.Basic` is feasible. -/
instance IsEfficient.instIsFeasible [M.IsEfficient] : M.IsFeasible where
  x_nonneg i b := by
    rw [IsEfficient.x_efficient]
    exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) b
  sum_x_le_one b := by
    have hx (i : Fin n) : M.x i b =
        {f : Fin n → ℝ | ∀ j ≠ i, f j < f i}.indicator (fun _ ↦ (1 : ℝ)) b :=
      congrFun (IsEfficient.x_efficient (M := M) i) b
    by_cases hex : ∃ i, ∀ j ≠ i, b j < b i
    · obtain ⟨w, hw⟩ := hex
      have hsum := Finset.sum_eq_single_of_mem (a := w) (Finset.mem_univ w)
        (f := fun i ↦ M.x i b) (fun i _ hiw ↦ by
          change M.x i b = 0
          rw [hx i, Set.indicator_of_notMem]
          intro hi
          exact (lt_asymm (hi w (Ne.symm hiw)) (hw i hiw)).elim)
      rw [hsum]
      change M.x w b ≤ 1
      rw [hx w, Set.indicator_of_mem
        (show b ∈ {f : Fin n → ℝ | ∀ j ≠ w, f j < f w} from hw)]
    · push_neg at hex
      have hzero : ∀ i, M.x i b = 0 := fun i ↦ by
        rw [hx i, Set.indicator_of_notMem]
        intro hi
        obtain ⟨j, hji, hij⟩ := hex i
        exact (not_lt_of_ge hij) (hi j hji)
      simp [hzero]

end Mechanism

end
