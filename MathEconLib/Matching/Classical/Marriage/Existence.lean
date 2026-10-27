/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Matching.Classical.Marriage.ToContracts
public import MathEconLib.Matching.Contracts.StableFixedPoints

/-!
# Stable matching existence via contracts

The embedding into contracts carries stable contracts outcomes back to stable
marriage matchings. The general contracts fixed-point theorem therefore proves
existence for finite marriage markets.
-/

@[expose] public section

namespace MathEconLib.Matching

open Function OrderDual

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}
variable (mkt : MarriageMarket M W)
variable [Finite M] [Finite W]

/-- Existence of a stable marriage matching. -/
theorem exists_stableMatching :
    ∃ μ : M ≃. W, mkt.IsStableMatching μ := by
  let hsub := mkt.substitutable_toContractsMarket
  let hcons := mkt.consistent_toContractsMarket
  obtain ⟨A, hA⟩ := mkt.toContractsMarket.exists_stable hsub hcons
  exact ⟨mkt.matchingOfStable hA, mkt.stable_matchingOfStable hA⟩

end MarriageMarket

end MathEconLib.Matching
