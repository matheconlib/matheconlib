/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching

/-!
Client applications through the matching umbrella alone. The incomplete deterministic, DA,
and random-law interfaces must all be available without importing their leaf modules.
-/

namespace MathEconLibTest.Matching.IncompletePublicImport

open MathEconLib.Matching.MarriageMarket

-- The umbrella exports the complete specialization and DA's conditional full-matching result.
example : ((default : RankProfile 1 2).toIncomplete.toMarriageMarket.galeShapleyComputable
    0).isSome :=
  IncompleteRankProfile.isSome_galeShapleyComputable_of_le _ (by decide)
    (RankProfile.toIncomplete_noUnacceptablePartners _) 0

-- Empty receiver populations also reach the executable DA through this entrypoint.
example : (default : IncompleteRankProfile 1 0).toMarriageMarket.galeShapleyComputable 0 =
    none := by
  decide +kernel

-- A concrete joint law is evaluated with the existing DA through the public random API.
example : IncompleteRankProfile.expectedAverageProposerRank
    (PMF.pure (default : IncompleteRankProfile 1 1))
      (fun p ↦ p.toMarriageMarket.galeShapleyComputable) = 1 := by
  have h : (default : IncompleteRankProfile 1 1).totalProposerRank
      (default : IncompleteRankProfile 1 1).toMarriageMarket.galeShapleyComputable = 1 := by
    decide +kernel
  simp [IncompleteRankProfile.expectedAverageProposerRank,
    IncompleteRankProfile.averageProposerRank_eq_total_div, PMF.toMeasure_pure, h]

-- The complete joint-law bridge is usable from the same narrow public umbrella.
example {m n : ℕ} (μ : PMF (RankProfile m n))
    (outcome : IncompleteRankProfile m n → Fin m ≃. Fin n) :
    IncompleteRankProfile.expectedAverageProposerRank (RankProfile.toIncompleteLaw μ) outcome =
      RankProfile.expectedAverageProposerRank μ (fun p ↦ outcome p.toIncomplete) :=
  RankProfile.expectedAverageProposerRank_toIncompleteLaw μ outcome

end MathEconLibTest.Matching.IncompletePublicImport
