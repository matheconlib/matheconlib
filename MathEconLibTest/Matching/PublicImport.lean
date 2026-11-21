/-
Copyright (c) 2026 Scott Duke Kominers, Ayan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers, Ayan
-/
module

public import MathEconLib

/-!
Client checks through the full public root. These exercise the raw fixed-point
lattice, its IRC-dependent economic interpretation, structural locality, and
the agreement of both executable algorithms with their optimal endpoints, and
fixed-menu choice under unambiguous improvements.
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

section Improvements

open MarriageMarket

/-! The fixed-menu result and its finite form, reached through the public root and applied to an
unambiguous improvement through its first clause. No finiteness is needed for the first. -/

example {M W : Type} (old new : MarriageMarket M W) {w : W} {m : M} {Y : Set (M × W)}
    (h : IsUnambiguousImprovement (new.prefW w) (old.prefW w) m)
    (hm : (m, w) ∈ old.inducedChoiceW w Y) : (m, w) ∈ new.inducedChoiceW w Y :=
  old.mem_inducedChoiceW_of_forall_lt_some new h.lt_some_of_lt_some hm

example {M W : Type} [Fintype M] (old new : MarriageMarket M W) {w : W} {m : M}
    {Y : Set (M × W)} (h : IsUnambiguousImprovement (new.prefW w) (old.prefW w) m)
    (hm : old.bestW w Y = some m) : new.bestW w Y = some m :=
  old.bestW_eq_some_of_forall_lt_some new h.lt_some_of_lt_some hm

example {M : Type} {old new : LinearOrder (Option M)} {m a b : M}
    (h : IsUnambiguousImprovement new old m) (ha : a ≠ m) (hb : b ≠ m) :
    old.lt (some b) (some a) ↔ new.lt (some b) (some a) :=
  h.some_lt_some_iff ha hb

example {M : Type} {old new : LinearOrder (Option M)} {m a : M}
    (h : IsUnambiguousImprovement new old m) (ha : a ≠ m) (hacc : old.lt none (some a)) :
    new.lt none (some a) :=
  h.none_lt_some_of_none_lt_some ha hacc

/-! The relation is reflexive, so it is satisfiable on every preference. -/

example {M : Type} (ord : LinearOrder (Option M)) (m : M) : IsUnambiguousImprovement ord ord m :=
  ⟨fun _ h => h, fun _ _ _ _ => Iff.rfl, fun _ _ h => h⟩

end Improvements

end MathEconLibTest.Matching
