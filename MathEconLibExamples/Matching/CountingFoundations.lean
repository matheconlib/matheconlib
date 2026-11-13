/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage
public import MathEconLibExamples.Matching.UnbalancedMarriage
public import Mathlib.Tactic.FinCases

/-!
# Applications of the marriage counting foundations

These checked applications use the threshold generators, the reservation-cutoff
transfer lemmas, the rank-list bridges and the counting bounds on concrete markets:

* `UnbalancedMarriage.market` (three men, two women, man `2` unmatched in every
  stable matching) gives an infeasible threshold, the generator at an attained
  threshold, a transfer through an acceptable cutoff, and the counting bounds.
* `cutoffInput` has one man ranking `[0, 1]` (woman `0`, then single) and one
  woman ranking `[1, 0]`. Moving his cutoff below the originally unacceptable
  woman creates a new stable matching, so the acceptability assumption of
  `stable_of_stable_truncateMan` cannot be dropped.
* `emptyInput` has no participants; its only stable matching is the empty one.
-/

@[expose] public section

namespace MathEconLibExamples.Matching.CountingFoundations

open MathEconLib.Matching MarriageMarket

/-! ### Unequal sides and an unmatched man -/

section Unbalanced

open UnbalancedMarriage

/-- In every stable matching, man `2` is unmatched: woman `0` finds him
unacceptable and he finds woman `1` unacceptable. -/
theorem matching_third_man (μ : market.StableMatching) : μ.matching 2 = none := by
  have hrank : ∀ w : Fin 2, manRank 2 none ≤ manRank 2 (some w) →
      womanRank w none ≤ womanRank w (some 2) → False := by
    decide
  rcases h : μ.matching 2 with _ | w
  · rfl
  · exfalso
    have hm : market.leM 2 none (μ.matching 2) := μ.isStable.1.1 2
    have hw : market.leW w none (μ.matching.symm w) := μ.isStable.1.2 w
    rw [h] at hm
    rw [(PEquiv.eq_some_iff _).mpr h] at hw
    exact hrank w hm hw

/-- Man `2` getting woman `0` is an infeasible threshold. -/
theorem not_exists_meetsThreshold_third_man :
    ¬ ∃ μ : market.StableMatching,
      StableMatching.MeetsThreshold market 2 (some 0) μ := by
  rintro ⟨μ, hμ⟩
  change market.leM 2 (some 0) (μ.matching 2) at hμ
  rw [matching_third_man μ] at hμ
  change manRank 2 (some 0) ≤ manRank 2 none at hμ
  revert hμ
  decide

/-- The generator of the infeasible threshold is the top stable matching and
does not meet the threshold. -/
theorem thresholdGenerator_third_man :
    StableMatching.thresholdGenerator market 2 (some 0) = ⊤ ∧
      ¬ StableMatching.MeetsThreshold market 2 (some 0)
        (StableMatching.thresholdGenerator market 2 (some 0)) :=
  ⟨StableMatching.thresholdGenerator_eq_top_of_not_exists market
      not_exists_meetsThreshold_third_man,
    fun h => not_exists_meetsThreshold_third_man
      ((StableMatching.meetsThreshold_thresholdGenerator_iff market).mp h)⟩

/-- At the threshold he attains in the men-preferred outcome, man `0` keeps
woman `0` in the least stable matching meeting that threshold. -/
theorem thresholdGenerator_first_man :
    (StableMatching.thresholdGenerator market 0 (menBest.matching 0)).matching 0 =
      some 0 :=
  StableMatching.thresholdGenerator_matching market menBest 0

/-- Woman `1` is acceptable to man `0`. -/
theorem first_man_accepts_second_woman : market.leM 0 none (some 1) := by
  change manRank 0 none ≤ manRank 0 (some 1)
  decide

/-- Moving man `0`'s cutoff just below woman `1` keeps the crossed outcome,
in which he is matched to her, stable. -/
theorem crossed_stable_truncateMan :
    (market.truncateMan 0 1).IsStableMatching crossed :=
  stable_truncateMan_of_stable market crossed_stable (current := 1) rfl
    (by change manRank 0 (some 1) ≤ manRank 0 (some 1); exact le_rfl)

/-- Because woman `1` was acceptable, stability transfers back, even though
man `2` stays unmatched. -/
theorem crossed_stable_of_truncateMan : market.IsStableMatching crossed :=
  stable_of_stable_truncateMan market first_man_accepts_second_woman
    crossed_stable_truncateMan (current := 1) rfl

/-- The two distinct stable outcomes and the partner-assignment bound. -/
theorem card_stableMatching_bounds :
    2 ≤ Nat.card market.StableMatching ∧ Nat.card market.StableMatching ≤ 27 := by
  refine ⟨?_, ?_⟩
  · have h := Nat.card_le_card_of_injective (α := Fin 2)
      (fun i => if i = 0 then womenBest else menBest) (by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact absurd hij outcomes_ne
        · exact absurd hij.symm outcomes_ne
        · rfl)
    simpa using h
  · simpa using StableMatching.card_le_partner_assignments market

/-- At most `3 * 3` join-irreducible stable matchings. -/
theorem card_supIrred_le_nine :
    Nat.card {μ : market.StableMatching // SupIrred μ} ≤ 9 := by
  simpa using StableMatching.card_supIrred_le market

end Unbalanced

/-! ### An originally unacceptable cutoff -/

section Cutoff

/-- One man ranks woman `0` below staying single; one woman prefers him. -/
def cutoffInput : RankInput where
  men := [[0, 1]]
  women := [[1, 0]]
  women_length := rfl
  men_row_length := by decide
  women_row_length := by decide
  men_row_nodup := by decide
  women_row_nodup := by decide

/-- The only man. -/
def cutoffMan : Fin cutoffInput.men.length := ⟨0, by decide⟩

/-- The only woman. -/
def cutoffWoman : Fin cutoffInput.men.length := ⟨0, by decide⟩

/-- The matching of the only man with the only woman. -/
def fullMatching : Fin 1 ≃. Fin 1 := PEquiv.refl (Fin 1)

/-- The market after the man's cutoff moves just below the woman. -/
abbrev movedMarket : MarriageMarket (Fin cutoffInput.men.length) (Fin cutoffInput.men.length) :=
  cutoffInput.market.truncateMan cutoffMan cutoffWoman

/-- Through the rank bridge, the woman is unacceptable to the man. -/
theorem cutoff_unacceptable : cutoffInput.market.ltM cutoffMan (some cutoffWoman) none := by
  rw [RankInput.ltM_iff]
  decide

/-- Through the rank bridge, the man is acceptable to the woman. -/
theorem cutoff_woman_accepts : cutoffInput.market.ltW cutoffWoman none (some cutoffMan) := by
  rw [RankInput.ltW_iff]
  decide

/-- The full matching is not stable originally: the man would rather be single. -/
theorem fullMatching_not_stable : ¬ cutoffInput.market.IsStableMatching fullMatching := by
  intro h
  have hm := h.1.1 cutoffMan
  change cutoffInput.market.leM cutoffMan none (some cutoffWoman) at hm
  let := cutoffInput.market.prefM cutoffMan
  exact absurd hm (not_le.mpr cutoff_unacceptable)

/-- After the cutoff moves below the woman she becomes acceptable to him. -/
theorem cutoff_acceptable_after : movedMarket.leM cutoffMan none (some cutoffWoman) :=
  (truncateMan_none_le_some _ _ _ _).mpr (by
    let := cutoffInput.market.prefM cutoffMan
    exact le_rfl)

/-- The full matching is stable after the cutoff moves. Hence
`stable_of_stable_truncateMan` needs its acceptability assumption. -/
theorem fullMatching_stable_truncateMan :
    movedMarket.IsStableMatching fullMatching := by
  refine ⟨⟨fun m => ?_, fun w => ?_⟩, ?_⟩
  · fin_cases m
    exact cutoff_acceptable_after
  · fin_cases w
    change cutoffInput.market.leW cutoffWoman none (some cutoffMan)
    let := cutoffInput.market.prefW cutoffWoman
    exact cutoff_woman_accepts.le
  · refine (movedMarket.unblocked_iff_no_blockingPair _).mpr ?_
    intro m w hb
    fin_cases m
    fin_cases w
    have h := hb.1
    change movedMarket.ltM cutoffMan (some cutoffWoman) (some cutoffWoman) at h
    let := movedMarket.prefM cutoffMan
    exact lt_irrefl _ h

/-- The reservation-cutoff change enlarges the acceptable set here, so stability
does not transfer back. -/
theorem cutoff_counterexample :
    cutoffInput.market.ltM cutoffMan (some cutoffWoman) none ∧
      movedMarket.IsStableMatching fullMatching ∧
      ¬ cutoffInput.market.IsStableMatching fullMatching :=
  ⟨cutoff_unacceptable, fullMatching_stable_truncateMan, fullMatching_not_stable⟩

end Cutoff

/-! ### The empty population -/

section Empty

/-- No men and no women. -/
def emptyInput : RankInput where
  men := []
  women := []
  women_length := rfl
  men_row_length := by simp
  women_row_length := by simp
  men_row_nodup := by simp
  women_row_nodup := by simp

/-- The empty market has exactly one stable matching. -/
theorem card_stableMatching_empty : Nat.card emptyInput.market.StableMatching = 1 := by
  have hle := StableMatching.card_le_partner_assignments emptyInput.market
  have hpos : 0 < Nat.card emptyInput.market.StableMatching :=
    Nat.card_pos_iff.mpr ⟨⟨⊤⟩, inferInstance⟩
  have h1 : (Fintype.card (Fin emptyInput.men.length) + 1) ^
      Fintype.card (Fin emptyInput.men.length) = 1 := by
    decide
  omega

/-- The empty market has no join-irreducible stable matching. -/
theorem card_supIrred_empty :
    Nat.card {μ : emptyInput.market.StableMatching // SupIrred μ} = 0 := by
  have h := StableMatching.card_supIrred_le emptyInput.market
  have h0 : Fintype.card (Fin emptyInput.men.length) *
      (Fintype.card (Fin emptyInput.men.length) + 1) = 0 := by
    decide
  omega

end Empty

end MathEconLibExamples.Matching.CountingFoundations
