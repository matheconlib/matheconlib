/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.IncompleteRankPreferencesDA
import MathEconLib.Matching.Classical.Marriage.RankPreferencesDA
import Lean

/-! Public deterministic API applications and empty/unequal population regressions. -/

open Lean Elab Command in
run_cmd do
  for entry in (← getEnv).header.modules do
    if (`Mathlib.Probability).isPrefixOf entry.module ||
        (`MathEconLib.Probability).isPrefixOf entry.module then
      logError m!"Incomplete-profile DA imports probability through {entry.module}."

namespace MathEconLibTest.Matching.IncompleteRankPreferences

open MathEconLib.Matching.MarriageMarket

-- A genuine complete-profile specialization preserves both markets and partial ranks.
example {m n : ℕ} (p : RankProfile m n) :
    p.toIncomplete.toMarriageMarket = p.toMarriageMarket := p.toIncomplete_toMarriageMarket

example {m n : ℕ} (p : RankProfile m n) (μ : Fin m ≃. Fin n) :
    p.toIncomplete.averageProposerRank μ = p.averageProposerRank μ :=
  p.toIncomplete_averageProposerRank μ

-- The old complete result applies after the explicit adapter without new hypotheses.
example (p : RankProfile 1 2) (i : Fin 1) :
    (p.toIncomplete.toMarriageMarket.galeShapleyComputable i).isSome := by
  simpa only [RankProfile.toIncomplete_toMarriageMarket] using
    RankProfile.isSome_galeShapleyComputable_of_le p (by decide) i

-- Full matching in the new general family retains the required acceptability assumption.
example {m n : ℕ} (p : IncompleteRankProfile m n) (h : m ≤ n)
    (hA : p.toMarriageMarket.NoUnacceptablePartners) (i : Fin m) :
    (p.toMarriageMarket.galeShapleyComputable i).isSome :=
  p.isSome_galeShapleyComputable_of_le h hA i

-- A concrete market discharges the acceptability hypothesis through the complete embedding.
example : ((default : RankProfile 1 2).toIncomplete.toMarriageMarket.galeShapleyComputable
    0).isSome :=
  IncompleteRankProfile.isSome_galeShapleyComputable_of_le _ (by decide)
    (RankProfile.toIncomplete_noUnacceptablePartners _) 0

example {m n : ℕ} (p : IncompleteRankProfile m n) {ν : Fin m ≃. Fin n}
    (hν : p.toMarriageMarket.IsStableMatching ν) :
    p.averageProposerRank p.toMarriageMarket.galeShapleyComputable ≤ p.averageProposerRank ν :=
  p.averageProposerRank_galeShapleyComputable_le hν

-- Empty averages stay well defined, including an empty proposer side facing receivers.
example (p : IncompleteRankProfile 0 2) (μ : Fin 0 ≃. Fin 2) :
    p.averageProposerRank μ = 0 := by
  simp [IncompleteRankProfile.averageProposerRank]

-- With no potential partners, the only optional rank is one and DA leaves agents unmatched.
example (r : OptionalRanking 0) : r.rank none = 1 := by
  have h := (r none).isLt
  change (r none).val + 1 = 1
  omega

example : (default : IncompleteRankProfile 2 0).toMarriageMarket.galeShapleyComputable 0 =
    none := by
  decide +kernel

-- On unequal sides the complete specialization preserves the familiar long-side unmatched case.
example : (default : RankProfile 2 1).toIncomplete.toMarriageMarket.galeShapleyComputable 1 =
    none := by
  rw [RankProfile.toIncomplete_toMarriageMarket]
  decide +kernel

end MathEconLibTest.Matching.IncompleteRankPreferences
