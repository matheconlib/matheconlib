/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.RankPreferencesDA
import Lean

/-! Deterministic DA checks, including an import guard against probability dependencies. -/

open Lean Elab Command in
run_cmd do
  for entry in (← getEnv).header.modules do
    if (`Mathlib.Probability).isPrefixOf entry.module ||
        (`MathEconLib.Probability).isPrefixOf entry.module then
      logError m!"Rank-profile DA imports probability through {entry.module}."

namespace MathEconLibTest.Matching.RankPreferencesDA

open MathEconLib.Matching.MarriageMarket
open RankProfile

example {m n : ℕ} (p : RankProfile m n) : p.toMarriageMarket.UniversallyAcceptable :=
  p.toMarriageMarket_universallyAcceptable

-- Smaller positions are better, and the adapter supplies that order to the existing API.
example (p : RankProfile 2 2) (i : Fin 2) :
    p.toMarriageMarket.ltM i (some ((p.manRank i).symm 1))
      (some ((p.manRank i).symm 0)) := by simp [rank]

example (p : RankProfile 2 2) (i : Fin 2) :
    (p.toMarriageMarket.galeShapleyComputable i).isSome := isSome_galeShapleyComputable p i

example (p : RankProfile 2 2) (j : Fin 2) :
    (p.toMarriageMarket.galeShapleyComputable.symm j).isSome :=
  isSome_symm_galeShapleyComputable p j

-- Unequal-size adapters use the opposite population's size for the outside option.
example (p : RankProfile 1 2) : rank (p.manRank 0) none = 3 := rfl

example (p : RankProfile 1 2) (j : Fin 2) : rank (p.womanRank j) none = 2 := rfl

example (p : RankProfile 1 2) :
    p.toMarriageMarket.IsStableMatching p.toMarriageMarket.galeShapleyComputable :=
  p.toMarriageMarket.stable_galeShapleyComputable

-- Balance is unnecessary for the average, or for completeness of the short side.
example (p : RankProfile 1 2) (μ : Fin 1 ≃. Fin 2) :
    p.averageProposerRank μ = (p.totalProposerRank μ : ℝ) := by
  simp [averageProposerRank_eq_total_div]

example (p : RankProfile 1 2) (i : Fin 1) :
    (p.toMarriageMarket.galeShapleyComputable i).isSome :=
  isSome_galeShapleyComputable_of_le p (by decide) i

example (p : RankProfile 2 1) (j : Fin 1) :
    (p.toMarriageMarket.galeShapleyComputable.symm j).isSome :=
  isSome_symm_galeShapleyComputable_of_le p (by decide) j

-- On the long side completeness fails: this DA leaves the second proposer unmatched.
example : ((default : RankProfile 2 1).toMarriageMarket.galeShapleyComputable 1) = none := by
  decide +kernel

-- The stronger general theorem needs no individual-rationality hypothesis.
example {M W : Type*} [Fintype M] [Fintype W]
    (mkt : MathEconLib.Matching.MarriageMarket M W) {μ : M ≃. W}
    (hμ : mkt.Unblocked μ) (hcard : Fintype.card M ≤ Fintype.card W)
    (hA : mkt.UniversallyAcceptable) (m : M) :
    (μ m).isSome := Unblocked.isSome_of_card_le mkt hμ hcard hA m

-- Rank comparisons use the existing economic preference and DA optimality interfaces.
example {m n : ℕ} (p : RankProfile m n) {ν : Fin m ≃. Fin n}
    (hν : p.toMarriageMarket.IsStableMatching ν) :
    p.averageProposerRank p.toMarriageMarket.galeShapleyComputable ≤ p.averageProposerRank ν :=
  averageProposerRank_galeShapleyComputable_le p hν

-- Side exchange also turns existing receiver pessimality into a rank-statistic comparison.
example {m n : ℕ} (p : RankProfile m n) {ν : Fin m ≃. Fin n}
    (hν : p.toMarriageMarket.IsStableMatching ν) :
    p.symm.averageProposerRank ν.symm ≤
      p.symm.averageProposerRank p.toMarriageMarket.galeShapleyComputable.symm := by
  apply p.symm.averageProposerRank_le
  exact p.toMarriageMarket.galeShapleyComputable_womanPessimal hν

example {m n : ℕ} (p : RankProfile m n) {μ ν : Fin m ≃. Fin n}
    (h : p.toMarriageMarket.MenWeaklyPrefer μ ν) :
    p.totalProposerRank μ ≤ p.totalProposerRank ν := p.totalProposerRank_le h

example {m n : ℕ} (p : RankProfile m n) (μ : Fin m ≃. Fin n) :
    p.symm.symm.averageProposerRank μ = p.averageProposerRank μ := by simp

#print axioms MathEconLib.Matching.MarriageMarket.IsStableMatching.isSome_of_card_eq
#print axioms MathEconLib.Matching.MarriageMarket.Unblocked.isSome_of_card_le
#print axioms PEquiv.isSome_of_forall_symm_isSome_of_card_le
#print axioms RankProfile.averageProposerRank_galeShapleyComputable_le

end MathEconLibTest.Matching.RankPreferencesDA
