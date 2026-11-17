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
the blocking lemma and weak Pareto optimality of deferred acceptance.
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

section BlockingLemma

open MarriageMarket

/-! The two forms of the blocking lemma, reached through the public root. -/

example {M W : Type} [Fintype M] [Fintype W] (mkt : MarriageMarket M W) {μ ν : M ≃. W}
    (hμ : mkt.IsManOptimal μ) (hν : mkt.IndividuallyRational ν) {m₀ : M}
    (h₀ : mkt.ltM m₀ (μ m₀) (ν m₀)) :
    ∃ m w, ¬ mkt.ltM m (μ m) (ν m) ∧ (∃ m', mkt.ltM m' (μ m') (ν m') ∧ ν m' = some w) ∧
      mkt.IsBlockingPair ν m w :=
  IsManOptimal.exists_isBlockingPair_of_ltM mkt hμ hν.2 h₀

example {M W : Type} [Fintype M] [Fintype W] (mkt : MarriageMarket M W) {ν : M ≃. W}
    (hν : mkt.IndividuallyRational ν) {m₀ : M} (h₀ : mkt.ltM m₀ (mkt.galeShapley m₀) (ν m₀)) :
    ∃ m w, ¬ mkt.ltM m (mkt.galeShapley m) (ν m) ∧
      (∃ m', mkt.ltM m' (mkt.galeShapley m') (ν m') ∧ ν m' = some w) ∧
      mkt.IsBlockingPair ν m w :=
  mkt.exists_isBlockingPair_of_ltM_galeShapley hν.2 h₀

/-! A matching that some man strictly prefers to deferred acceptance is not stable. -/

example {M W : Type} [Fintype M] [Fintype W] (mkt : MarriageMarket M W) {ν : M ≃. W}
    (hν : mkt.IndividuallyRational ν) {m₀ : M} (h₀ : mkt.ltM m₀ (mkt.galeShapley m₀) (ν m₀)) :
    ∃ m w, mkt.IsBlockingPair ν m w := by
  obtain ⟨m, w, -, -, h⟩ := mkt.exists_isBlockingPair_of_ltM_galeShapley hν.2 h₀
  exact ⟨m, w, h⟩

/-! The three forms of weak Pareto optimality, reached through the public root. -/

example {M W : Type} [Fintype M] [Fintype W] [Nonempty M] (mkt : MarriageMarket M W)
    {μ ν : M ≃. W} (hμ : mkt.IsManOptimal μ) (hν : mkt.IndividuallyRational ν) :
    ¬ ∀ m, mkt.ltM m (μ m) (ν m) :=
  IsManOptimal.not_forall_ltM mkt hμ hν.2

example {M W : Type} [Fintype M] [Fintype W] [Nonempty M] (mkt : MarriageMarket M W)
    {ν : M ≃. W} (hν : mkt.IndividuallyRational ν) :
    ¬ ∀ m, mkt.ltM m (mkt.galeShapley m) (ν m) :=
  mkt.not_forall_ltM_galeShapley hν.2

example {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] [Nonempty M]
    (mkt : MarriageMarket M W) {ν : M ≃. W} (hν : mkt.IndividuallyRational ν) :
    ¬ ∀ m, mkt.ltM m (mkt.galeShapleyComputable m) (ν m) :=
  mkt.not_forall_ltM_galeShapleyComputable hν.2

/-! With no men, every alternative vacuously makes every man strictly better off. -/

example (mkt : MarriageMarket Empty Unit) (ν : Empty ≃. Unit) :
    ∀ m, mkt.ltM m (mkt.galeShapley m) (ν m) :=
  fun m => m.elim

end BlockingLemma

end MathEconLibTest.Matching
