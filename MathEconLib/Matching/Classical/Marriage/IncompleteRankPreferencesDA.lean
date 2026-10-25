/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.DeferredAcceptanceComputable
import MathEconLib.Matching.Classical.Marriage.IncompleteRankPreferences

/-!
# Deferred acceptance with incomplete acceptable lists

Optional ranks feed directly into the existing executable proposer DA. Its stability and
proposer optimality apply without universal acceptability. Full matching of the shorter side
requires the explicit `NoUnacceptablePartners` assumption; balance alone does not suffice.
The complete-profile embedding preserves the market, hence also the DA outcome and its ranks.
-/

namespace MathEconLib.Matching.MarriageMarket.IncompleteRankProfile

variable {m n : ℕ}

/-- Individual rationality bounds every proposer's assignment by their own outside rank. -/
theorem rank_le_outside_of_individuallyRational (p : IncompleteRankProfile m n)
    {μ : Fin m ≃. Fin n} (hμ : p.toMarriageMarket.IndividuallyRationalM μ) (i : Fin m) :
    (p.manRank i).rank (μ i) ≤ (p.manRank i).rank none :=
  hμ i

/-- Stable outcomes, in particular DA, never assign an unacceptable partner. -/
theorem rank_le_outside_galeShapleyComputable (p : IncompleteRankProfile m n) (i : Fin m) :
    (p.manRank i).rank (p.toMarriageMarket.galeShapleyComputable i) ≤
      (p.manRank i).rank none :=
  p.rank_le_outside_of_individuallyRational
    p.toMarriageMarket.stable_galeShapleyComputable.1.1 i

/-- The shorter proposer side is fully matched under universal mutual acceptability. -/
theorem isSome_galeShapleyComputable_of_le (p : IncompleteRankProfile m n) (h : m ≤ n)
    (hA : p.toMarriageMarket.NoUnacceptablePartners) (i : Fin m) :
    (p.toMarriageMarket.galeShapleyComputable i).isSome :=
  Unblocked.isSome_of_card_le p.toMarriageMarket
    p.toMarriageMarket.stable_galeShapleyComputable.2 (by simpa using h) hA i

/-- The shorter receiver side is fully matched under universal mutual acceptability. -/
theorem isSome_symm_galeShapleyComputable_of_le (p : IncompleteRankProfile m n) (h : n ≤ m)
    (hA : p.toMarriageMarket.NoUnacceptablePartners) (j : Fin n) :
    (p.toMarriageMarket.galeShapleyComputable.symm j).isSome :=
  Unblocked.isSome_of_card_le p.toMarriageMarket.symm
    ((p.toMarriageMarket.isStableMatching_symm _).mpr
      p.toMarriageMarket.stable_galeShapleyComputable).2 (by simpa using h) hA.symm j

/-- Proposer DA minimizes average ordinal position among stable outcomes, even with
unmatched agents and profile-dependent outside ranks. -/
theorem averageProposerRank_galeShapleyComputable_le (p : IncompleteRankProfile m n)
    {ν : Fin m ≃. Fin n} (hν : p.toMarriageMarket.IsStableMatching ν) :
    p.averageProposerRank p.toMarriageMarket.galeShapleyComputable ≤ p.averageProposerRank ν :=
  p.averageProposerRank_le (p.toMarriageMarket.galeShapleyComputable_manOptimal hν)

end MathEconLib.Matching.MarriageMarket.IncompleteRankProfile
