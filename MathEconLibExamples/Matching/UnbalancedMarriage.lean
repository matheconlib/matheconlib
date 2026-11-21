/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.Distributive

/-!
# A stable marriage lattice with unequal sides and unacceptable partners

Three men and two women. Men `0` and `1` and both women form the two-by-two
market of `MathEconLibExamples.Matching.DistributiveMarriage`: the men prefer
the diagonal matching and the women prefer the crossed one. Man `2` finds
woman `0` acceptable but woman `1` unacceptable, and both women find man `2`
unacceptable. He is therefore unmatched in every stable matching.

The example exercises the boundaries that the two-by-two example does not:
populations of different sizes, unacceptable partners, and a participant who
stays unmatched. We check both stable matchings, compute their join and meet
with the pointwise formulas, and distinguish their lower-set representations.
-/

@[expose] public section

namespace MathEconLibExamples.Matching.UnbalancedMarriage

open MathEconLib.Matching MarriageMarket

/-- Men's ranks; higher is better. Men `0` and `1` most prefer the woman with
their own index. Man `2` ranks woman `1` below staying single. -/
def manRank (i : Fin 3) : Option (Fin 2) → Fin 3
  | none => if i = 2 then 1 else 0
  | some j => if i = 2 then (if j = 0 then 2 else 0) else if i.val = j.val then 2 else 1

/-- Women's ranks; higher is better. Each woman most prefers the man in
`{0, 1}` with the other index and ranks man `2` below staying single. -/
def womanRank (j : Fin 2) : Option (Fin 3) → Fin 4
  | none => 1
  | some i => if i = 2 then 0 else if i.val = j.val then 2 else 3

theorem manRank_injective : ∀ i, Function.Injective (manRank i) := by
  decide

theorem womanRank_injective : ∀ j, Function.Injective (womanRank j) := by
  decide

/-- Man `i`'s preference order over women and staying single. -/
@[instance_reducible] def manPreference (i : Fin 3) : LinearOrder (Option (Fin 2)) :=
  LinearOrder.lift' (manRank i) (manRank_injective i)

/-- Woman `j`'s preference order over men and staying single. -/
@[instance_reducible] def womanPreference (j : Fin 2) : LinearOrder (Option (Fin 3)) :=
  LinearOrder.lift' (womanRank j) (womanRank_injective j)

/-- A market with three men, two women, and unacceptable partners. -/
def market : MarriageMarket (Fin 3) (Fin 2) where
  prefM := manPreference
  prefW := womanPreference

/-- Man `i < 2` marries woman `i`; man `2` is single. -/
def diagonal : Fin 3 ≃. Fin 2 where
  toFun i := if i = 0 then some 0 else if i = 1 then some 1 else none
  invFun j := if j = 0 then some 0 else some 1
  inv := by decide

/-- Man `i < 2` marries woman `1 - i`; man `2` is single. -/
def crossed : Fin 3 ≃. Fin 2 where
  toFun i := if i = 0 then some 1 else if i = 1 then some 0 else none
  invFun j := if j = 0 then some 1 else some 0
  inv := by decide

/-- A matching that marries man `2` to the woman he finds acceptable. -/
def withThirdMan : Fin 3 ≃. Fin 2 where
  toFun i := if i = 0 then none else if i = 1 then some 1 else some 0
  invFun j := if j = 0 then some 2 else some 1
  inv := by decide

theorem diagonal_stable : market.IsStableMatching diagonal := by
  decide

theorem crossed_stable : market.IsStableMatching crossed := by
  decide

/-- Woman `0` would rather stay single than keep man `2`, so marrying him is
not individually rational. -/
theorem withThirdMan_not_stable : ¬ market.IsStableMatching withThirdMan := by
  decide

/-- The stable diagonal outcome. -/
def menBest : market.StableMatching := ⟨diagonal, diagonal_stable⟩

/-- The stable crossed outcome. -/
def womenBest : market.StableMatching := ⟨crossed, crossed_stable⟩

/-- The men weakly prefer the diagonal outcome. -/
theorem womenBest_le_menBest : womenBest ≤ menBest := by
  apply (StableMatching.le_iff_menWeaklyPrefer market).2
  intro m
  change manRank m (womenBest.matching m) ≤ manRank m (menBest.matching m)
  revert m
  decide

/-- The two stable outcomes differ. -/
theorem outcomes_ne : womenBest ≠ menBest := by
  intro h
  have h0 := congrArg (fun x : market.StableMatching => x.matching 0) h
  change some (1 : Fin 2) = some 0 at h0
  cases h0

/-- The pointwise formula for the join leaves the unmatched man single. -/
theorem join_third_man : (womenBest ⊔ menBest).matching 2 = none := by
  rw [StableMatching.matching_sup_apply]
  decide

/-- The pointwise formula for the meet leaves the unmatched man single. -/
theorem meet_third_man : (womenBest ⊓ menBest).matching 2 = none := by
  rw [StableMatching.matching_inf_apply]
  decide

/-- The pointwise formula computes the join assignment of man `0`. -/
theorem join_first_man : (womenBest ⊔ menBest).matching 0 = some 0 := by
  rw [StableMatching.matching_sup_apply]
  decide

/-- The pointwise formula computes the meet assignment of man `0`. -/
theorem meet_first_man : (womenBest ⊓ menBest).matching 0 = some 1 := by
  rw [StableMatching.matching_inf_apply]
  decide

/-- The canonical lower-set representation distinguishes the two outcomes. -/
theorem represented_outcomes_ne :
    StableMatching.lowerSetSupIrred market womenBest ≠
      StableMatching.lowerSetSupIrred market menBest := by
  intro h
  exact outcomes_ne ((StableMatching.lowerSetSupIrred market).injective h)

end MathEconLibExamples.Matching.UnbalancedMarriage
