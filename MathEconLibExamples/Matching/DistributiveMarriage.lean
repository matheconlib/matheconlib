/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.Distributive
public import Mathlib.Tactic.FinCases

/-!
# A two-by-two stable marriage lattice

Both men prefer the diagonal matching, while both women prefer the crossed
matching. We construct and check both stable matchings, calculate their join
and meet, and distinguish their representations as lower sets.
-/

@[expose] public section

namespace MathEconLibExamples.Matching.DistributiveMarriage

open MathEconLib.Matching MarriageMarket

/-- Rank an option for an agent whose favorite partner has the same index. -/
def rank (i : Fin 2) : Option (Fin 2) → Fin 3
  | none => 0
  | some j => if i = j then 2 else 1

theorem rank_injective (i : Fin 2) : Function.Injective (rank i) := by
  intro a b h
  fin_cases i <;> cases a with
  | none => cases b with
    | none => rfl
    | some b => fin_cases b <;> simp_all [rank]
  | some a => cases b with
    | none => fin_cases a <;> simp_all [rank]
    | some b => fin_cases a <;> fin_cases b <;> simp_all [rank]

/-- The order with `none` lowest and the partner with index `i` highest. -/
@[instance_reducible] def preference (i : Fin 2) : LinearOrder (Option (Fin 2)) :=
  LinearOrder.lift' (rank i) (rank_injective i)

/-- Men prefer equal indices, women unequal indices. -/
def market : MarriageMarket (Fin 2) (Fin 2) where
  prefM := preference
  prefW := fun w => preference (1 - w)

/-- The diagonal partial equivalence matches every agent. -/
def diagonal : Fin 2 ≃. Fin 2 :=
  Equiv.toPEquiv (Equiv.refl _)

/-- The crossed partial equivalence matches each agent to the other index. -/
def crossed : Fin 2 ≃. Fin 2 :=
  Equiv.toPEquiv (Equiv.swap (0 : Fin 2) 1)

/-- The diagonal matching has no blocking pair. -/
theorem diagonal_stable : market.IsStableMatching diagonal := by
  decide

/-- The crossed matching has no blocking pair. -/
theorem crossed_stable : market.IsStableMatching crossed := by
  decide

/-- The stable diagonal outcome. -/
def menBest : market.StableMatching := ⟨diagonal, diagonal_stable⟩

/-- The stable crossed outcome. -/
def womenBest : market.StableMatching := ⟨crossed, crossed_stable⟩

/-- Both men prefer the diagonal outcome. -/
theorem womenBest_le_menBest : womenBest ≤ menBest := by
  apply (StableMatching.le_iff_menWeaklyPrefer market).2
  intro m
  change rank m (womenBest.matching m) ≤ rank m (menBest.matching m)
  fin_cases m <;> decide

/-- The two stable outcomes really differ. -/
theorem outcomes_ne : womenBest ≠ menBest := by
  intro h
  have h0 := congrArg (fun x : market.StableMatching => x.matching 0) h
  change some (1 : Fin 2) = some 0 at h0
  cases h0

/-- The join picks the diagonal outcome. -/
theorem join_outcomes : womenBest ⊔ menBest = menBest :=
  sup_eq_right.mpr womenBest_le_menBest

/-- The meet picks the crossed outcome. -/
theorem meet_outcomes : womenBest ⊓ menBest = womenBest :=
  inf_eq_left.mpr womenBest_le_menBest

/-- The lattice formula computes the join assignment of the first man. -/
theorem join_first_man : (womenBest ⊔ menBest).matching 0 = some 0 := by
  rw [StableMatching.matching_sup_apply]
  decide

/-- The lattice formula computes the meet assignment of the first man. -/
theorem meet_first_man : (womenBest ⊓ menBest).matching 0 = some 1 := by
  rw [StableMatching.matching_inf_apply]
  decide

/-- The canonical lower-set representation distinguishes the two outcomes. -/
theorem represented_outcomes_ne :
    StableMatching.lowerSetSupIrred market womenBest ≠
      StableMatching.lowerSetSupIrred market menBest := by
  intro h
  exact outcomes_ne ((StableMatching.lowerSetSupIrred market).injective h)

/-- The representation recovers the diagonal outcome. -/
theorem menBest_roundtrip :
    (StableMatching.lowerSetSupIrred market).symm
      (StableMatching.lowerSetSupIrred market menBest) = menBest :=
  (StableMatching.lowerSetSupIrred market).symm_apply_apply menBest

/-- The representation recovers the crossed outcome. -/
theorem womenBest_roundtrip :
    (StableMatching.lowerSetSupIrred market).symm
      (StableMatching.lowerSetSupIrred market womenBest) = womenBest :=
  (StableMatching.lowerSetSupIrred market).symm_apply_apply womenBest

end MathEconLibExamples.Matching.DistributiveMarriage
