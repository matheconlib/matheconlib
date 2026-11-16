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
transfer lemmas, the equivalences between numeric ranks and market preferences,
and the counting bounds on concrete markets:

* `UnbalancedMarriage.market` (three men, two women, man `2` unmatched in every
  stable matching) gives an infeasible threshold, the generator at an attained
  threshold, a transfer through an acceptable cutoff, and the counting bounds.
* `cutoffInput` has one man ranking `[0, 1]` (woman `0`, then single) and one
  woman ranking `[1, 0]`. Moving his cutoff below the originally unacceptable
  woman creates a new stable matching, so the acceptability assumption of
  `stable_of_stable_truncateMan` cannot be dropped.
* `UnmatchedCutoff.market` has one man and two women. Raising his cutoff to
  the woman who rejects him leaves everyone single. That outcome is stable
  after the change but blocked originally, even though the cutoff was
  acceptable. Thus the changed man's matchedness assumption is also necessary.
* `emptyInput` has no participants; its only stable matching is the empty one.
-/

@[expose] public section

namespace MathEconLibExamples.Matching.CountingFoundations

open MathEconLib.Matching MarriageMarket

/-! ### Unequal sides and an unmatched man -/

section Unbalanced

open UnbalancedMarriage

-- Side-specific notation distinguishes the men from the women.
local notation "manA" => (0 : Fin 3)
local notation "manC" => (2 : Fin 3)
local notation "womanA" => (0 : Fin 2)
local notation "womanB" => (1 : Fin 2)

/-- In every stable matching, man `manC` is unmatched: woman `womanA` finds him
unacceptable and he finds woman `womanB` unacceptable. -/
theorem matching_third_man (μ : market.StableMatching) : μ.matching manC = none := by
  have hrank : ∀ w : Fin 2, manRank manC none ≤ manRank manC (some w) →
      womanRank w none ≤ womanRank w (some manC) → False := by
    decide
  rcases h : μ.matching manC with _ | w
  · rfl
  · exfalso
    have hm : market.leM manC none (μ.matching manC) := μ.isStable.1.1 manC
    have hw : market.leW w none (μ.matching.symm w) := μ.isStable.1.2 w
    rw [h] at hm
    rw [(PEquiv.eq_some_iff _).mpr h] at hw
    exact hrank w hm hw

/-- Man `manC` getting woman `womanA` is an infeasible threshold. -/
theorem not_exists_meetsThreshold_third_man :
    ¬ ∃ μ : market.StableMatching,
      StableMatching.MeetsThreshold market manC (some womanA) μ := by
  rintro ⟨μ, hμ⟩
  change market.leM manC (some womanA) (μ.matching manC) at hμ
  rw [matching_third_man μ] at hμ
  change manRank manC (some womanA) ≤ manRank manC none at hμ
  revert hμ
  decide

/-- The generator of the infeasible threshold is the top stable matching and
does not meet the threshold. -/
theorem thresholdGenerator_third_man :
    StableMatching.thresholdGenerator market manC (some womanA) = ⊤ ∧
      ¬ StableMatching.MeetsThreshold market manC (some womanA)
        (StableMatching.thresholdGenerator market manC (some womanA)) :=
  ⟨StableMatching.thresholdGenerator_eq_top_of_not_exists market
      not_exists_meetsThreshold_third_man,
    fun h => not_exists_meetsThreshold_third_man
      ((StableMatching.meetsThreshold_thresholdGenerator_iff market).mp h)⟩

/-- At the threshold he attains in the men-preferred outcome, man `manA` keeps
woman `womanA` in the least stable matching meeting that threshold. -/
theorem thresholdGenerator_first_man :
    (StableMatching.thresholdGenerator market manA (menBest.matching manA)).matching manA =
      some womanA :=
  StableMatching.thresholdGenerator_matching market menBest manA

/-- The feasible-threshold interface identifies exactly the outcomes above
the generator for man A receiving woman A. -/
theorem thresholdGenerator_first_man_le_iff (μ : market.StableMatching) :
    StableMatching.thresholdGenerator market manA (some womanA) ≤ μ ↔
      StableMatching.MeetsThreshold market manA (some womanA) μ :=
  StableMatching.thresholdGenerator_le_iff market
    ⟨menBest, by change manRank manA (some womanA) ≤ manRank manA (some womanA); decide⟩ μ

/-- The men-preferred outcome is recovered from its three attained-threshold
generators, including the threshold `none` of the unmatched man. -/
theorem sup_thresholdGenerators_menBest :
    (Finset.univ : Finset (Fin 3)).sup
      (fun m => StableMatching.thresholdGenerator market m (menBest.matching m)) = menBest :=
  StableMatching.sup_thresholdGenerator_matching market menBest

/-- Woman `womanB` is acceptable to man `manA`. -/
theorem first_man_accepts_second_woman : market.leM manA none (some womanB) := by
  change manRank manA none ≤ manRank manA (some womanB)
  decide

/-- Moving man `manA`'s cutoff just below woman `womanB` keeps the crossed outcome,
in which he is matched to her, stable. -/
theorem crossed_stable_truncateMan :
    (market.truncateMan manA womanB).IsStableMatching crossed :=
  stable_truncateMan_of_stable market crossed_stable (current := womanB) rfl
    (by change manRank manA (some womanB) ≤ manRank manA (some womanB); exact le_rfl)

/-- Because woman `womanB` was acceptable, stability transfers back, even though
man `manC` stays unmatched. -/
theorem crossed_stable_of_truncateMan : market.IsStableMatching crossed :=
  stable_of_stable_truncateMan market first_man_accepts_second_woman
    crossed_stable_truncateMan (current := womanB) rfl

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
def cutoffInput : BalancedRankInput where
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

/-- The numeric-rank comparison shows that the woman is unacceptable to the man. -/
theorem cutoff_unacceptable : cutoffInput.market.ltM cutoffMan (some cutoffWoman) none := by
  rw [BalancedRankInput.ltM_iff]
  decide

/-- The numeric-rank comparison shows that the man is acceptable to the woman. -/
theorem cutoff_woman_accepts : cutoffInput.market.ltW cutoffWoman none (some cutoffMan) := by
  rw [BalancedRankInput.ltW_iff]
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

/-! ### An acceptable cutoff that leaves the changed man unmatched -/

namespace UnmatchedCutoff

local notation "manA" => (0 : Fin 1)
local notation "womanA" => (0 : Fin 2)
local notation "womanB" => (1 : Fin 2)

/-- The man prefers `womanA` to `womanB` to being single. Woman A rejects
him; woman B prefers him to being single. -/
def market : MarriageMarket (Fin 1) (Fin 2) where
  prefM _ := rankRowOrder [2, 1, 0] rfl (by decide)
  prefW w := if w = womanA then rankRowOrder [0, 1] rfl (by decide)
    else rankRowOrder [1, 0] rfl (by decide)

/-- The outcome in which all three participants stay single. -/
def allSingle : Fin 1 ≃. Fin 2 := ⊥

/-- The raised cutoff was originally acceptable to the changed man. -/
theorem threshold_acceptable : market.leM manA none (some womanA) := by
  change (0 : Nat) ≤ 2
  decide

/-- The changed man is unmatched, so the matchedness guard does not hold. -/
theorem changed_man_unmatched : allSingle manA = none := rfl

/-- Woman B and the man block the all-single outcome in the original market. -/
theorem original_blockingPair : market.IsBlockingPair allSingle manA womanB := by
  change (0 : Nat) < 1 ∧ (0 : Nat) < 1
  decide

/-- Hence the all-single outcome is not stable in the original market. -/
theorem allSingle_not_stable : ¬ market.IsStableMatching allSingle := by
  intro h
  exact h.2.1 manA womanB original_blockingPair

/-- After raising the cutoff, woman B is unacceptable to the man, while
woman A still rejects him. Thus the all-single outcome is stable. -/
theorem allSingle_stable_truncateMan :
    (market.truncateMan manA womanA).IsStableMatching allSingle := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro m
    change (market.truncateMan manA womanA).leM m none none
    let := (market.truncateMan manA womanA).prefM m
    exact le_rfl
  · intro w
    change market.leW w none none
    let := market.prefW w
    exact le_rfl
  · apply ((market.truncateMan manA womanA).unblocked_iff_no_blockingPair _).mpr
    intro m w hb
    fin_cases m
    fin_cases w
    · have h := hb.2
      change (1 : Nat) < 0 at h
      exact (by decide : ¬ (1 : Nat) < 0) h
    · have h := (truncateMan_none_lt_some market manA womanA womanB).mp hb.1
      change (2 : Nat) ≤ 1 at h
      exact (by decide : ¬ (2 : Nat) ≤ 1) h

/-- Acceptability of the threshold alone does not suffice for stability
transfer back: the man whose cutoff changes must also remain matched. -/
theorem matchedness_counterexample :
    market.leM manA none (some womanA) ∧
      allSingle manA = none ∧
      (market.truncateMan manA womanA).IsStableMatching allSingle ∧
      ¬ market.IsStableMatching allSingle :=
  ⟨threshold_acceptable, changed_man_unmatched,
    allSingle_stable_truncateMan, allSingle_not_stable⟩

end UnmatchedCutoff

/-! ### The empty population -/

section Empty

/-- No men and no women. -/
def emptyInput : BalancedRankInput where
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
