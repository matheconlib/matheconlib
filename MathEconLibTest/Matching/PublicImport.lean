/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib

/-!
Client checks through the full public root. These exercise the raw fixed-point
lattice, its IRC-dependent economic interpretation, structural locality, and
the agreement of both executable algorithms with their optimal endpoints.
-/

@[expose] public section

namespace MathEconLibTest.Matching

open MathEconLib.Choice MathEconLib.Matching

#check MathEconLib.Auction
#check MathEconLib.Choice.ChoiceFunction
#check MathEconLib.Matching.Market
#check MathEconLib.Matching.MarriageMarket
#check MathEconLib.Matching.Market.FixedPointStates.state
#check MathEconLib.Matching.Market.StableOutcomes.state

section Contracts

variable {B S X : Type*} (mkt : Market B S X)

example (hsub : mkt.Substitutable) : CompleteLattice (mkt.FixedPointStates hsub) :=
  inferInstance

example (hsub : mkt.Substitutable) (hcons : mkt.Consistent) :
    CompleteLattice (mkt.StableOutcomes hsub hcons) := inferInstance

example (hsub : mkt.Substitutable) (hcons : mkt.Consistent)
    (A : mkt.StableOutcomes hsub hcons) : mkt.Stable A.outcome :=
  Market.StableOutcomes.stable hcons A

example (hcons : mkt.Consistent) : mkt.Local :=
  Market.Consistent.local mkt hcons

example (hsub : mkt.Substitutable) (hcons : mkt.Consistent) :
    mkt.Stable (mkt.sellerOptimal hsub hcons) :=
  mkt.stable_sellerOptimal hsub hcons

example (hsub : mkt.Substitutable) (hcons : mkt.Consistent) :
    mkt.Stable (mkt.buyerOptimal hsub hcons) :=
  mkt.stable_buyerOptimal hsub hcons

end Contracts

section Marriage

variable {M W : Type*} (mkt : MarriageMarket M W)

-- Locality requires no finite population or consistency assumption.
example : mkt.toContractsMarket.Local := mkt.local_toContractsMarket

variable [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

example : mkt.galeShapleyComputable = mkt.manOptimalMatching :=
  mkt.galeShapleyComputable_eq_manOptimalMatching

example : mkt.womanGaleShapleyComputable = mkt.womanOptimalMatching :=
  mkt.womanGaleShapleyComputable_eq_womanOptimalMatching

example : mkt.IsStableMatching mkt.galeShapleyComputable :=
  mkt.stable_galeShapleyComputable_via_fixedPoints

example : mkt.IsStableMatching mkt.womanGaleShapleyComputable :=
  mkt.stable_womanGaleShapleyComputable_via_fixedPoints

end Marriage

end MathEconLibTest.Matching
