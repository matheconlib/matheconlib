/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.DeferredAcceptanceComputable
import MathEconLib.Matching.Classical.Marriage.RankPreferences

/-!
# Deferred acceptance for finite rank profiles

This deterministic layer combines `RankPreferences` with the existing executable proposer DA.
Universal mutual acceptability and no blocking pairs ensure that the shorter side is fully
matched under any stable matching. The corollaries here apply that fact to the DA outcome;
proposer optimality also gives weakly lower average ordinal rank than any other stable outcome.
No probability assumptions are needed, and `RankPreferences` itself remains independent of DA.
-/

namespace MathEconLib.Matching.MarriageMarket

namespace RankProfile

variable {m n : ℕ}

/-- Every proposer is matched when the proposer population is no larger. -/
theorem isSome_galeShapleyComputable_of_le (p : RankProfile m n) (h : m ≤ n) (i : Fin m) :
    (p.toMarriageMarket.galeShapleyComputable i).isSome :=
  Unblocked.isSome_of_card_le p.toMarriageMarket
    p.toMarriageMarket.stable_galeShapleyComputable.2 (by simpa using h)
    p.toMarriageMarket_noUnacceptablePartners i

/-- Every receiver is matched when the receiver population is no larger. -/
theorem isSome_symm_galeShapleyComputable_of_le (p : RankProfile m n) (h : n ≤ m)
    (j : Fin n) : (p.toMarriageMarket.galeShapleyComputable.symm j).isSome := by
  have hs := p.toMarriageMarket.stable_galeShapleyComputable
  exact Unblocked.isSome_of_card_le p.toMarriageMarket.symm
    ((p.toMarriageMarket.isStableMatching_symm _).mpr hs).2 (by simpa using h)
    p.toMarriageMarket_noUnacceptablePartners.symm j

/-- Balanced rank profiles give complete outcomes under the existing executable proposer DA. -/
theorem isSome_galeShapleyComputable (p : RankProfile n n) (i : Fin n) :
    (p.toMarriageMarket.galeShapleyComputable i).isSome :=
  isSome_galeShapleyComputable_of_le p le_rfl i

/-- The same balanced DA outcome matches every receiver. -/
theorem isSome_symm_galeShapleyComputable (p : RankProfile n n) (j : Fin n) :
    (p.toMarriageMarket.galeShapleyComputable.symm j).isSome :=
  isSome_symm_galeShapleyComputable_of_le p le_rfl j

/-- The existing proposer-optimality result gives weakly lower average rank than any stable
outcome, including in unequal markets. This compares ordinal positions, not cardinal utilities. -/
theorem averageProposerRank_galeShapleyComputable_le (p : RankProfile m n)
    {ν : Fin m ≃. Fin n} (hν : p.toMarriageMarket.IsStableMatching ν) :
    p.averageProposerRank p.toMarriageMarket.galeShapleyComputable ≤ p.averageProposerRank ν :=
  p.averageProposerRank_le (p.toMarriageMarket.galeShapleyComputable_manOptimal hν)


end RankProfile
end MathEconLib.Matching.MarriageMarket
