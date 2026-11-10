/-
Copyright (c) 2026 Ayan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayan
-/
module

import MathEconLib
import MathEconLibExamples.Matching.BlockingLemma

/-! Public import and regression checks for the blocking lemma and weak Pareto optimality of
deferred acceptance. -/

open MathEconLib.Matching MarriageMarket
open MathEconLibExamples.Matching.BlockingLemma

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

/-! The blocking pair in the trade market, and the failure without the women's half. -/

example : Trade.market.IsBlockingPair Trade.traded 0 1 := Trade.isBlockingPair_traded.2.2

example : (∀ m, Unwilling.market.ltM m (Unwilling.market.galeShapley m) (Unwilling.paired m)) ∧
    ∀ m w, ¬ Unwilling.market.IsBlockingPair Unwilling.paired m w :=
  ⟨Unwilling.forall_ltM_galeShapley_paired, Unwilling.paired_not_isBlockingPair⟩

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

/-! The women's half of individual rationality cannot be dropped. -/

example : Unwilling.market.IndividuallyRationalM Unwilling.paired ∧
    ∀ m, Unwilling.market.ltM m (Unwilling.market.galeShapley m) (Unwilling.paired m) :=
  ⟨Unwilling.paired_individuallyRationalM, Unwilling.forall_ltM_galeShapley_paired⟩

/-! With no men, every alternative vacuously makes every man strictly better off. -/

example (mkt : MarriageMarket Empty Unit) (ν : Empty ≃. Unit) :
    ∀ m, mkt.ltM m (mkt.galeShapley m) (ν m) :=
  fun m => m.elim

/-! Full Pareto efficiency fails. -/

example : Trade.market.IndividuallyRational Trade.traded ∧
    (∀ m, Trade.market.leM m (Trade.market.galeShapley m) (Trade.traded m)) ∧
    ∃ m, Trade.market.ltM m (Trade.market.galeShapley m) (Trade.traded m) :=
  ⟨Trade.traded_individuallyRational, Trade.forall_leM_galeShapley_traded,
    1, Trade.ltM_galeShapley_traded.1⟩

/-! The result is specific to the man-optimal stable matching. -/

example : Apply.market.IsStableMatching Apply.womenFavored ∧
    Apply.market.IndividuallyRational Apply.diagonal ∧
    ∀ m, Apply.market.ltM m (Apply.womenFavored m) (Apply.diagonal m) :=
  ⟨Apply.womenFavored_stable, Apply.diagonal_individuallyRational,
    Apply.forall_ltM_womenFavored_diagonal⟩

example : ¬ Apply.market.IsManOptimal Apply.womenFavored :=
  Apply.womenFavored_not_isManOptimal

example : Apply.market.galeShapley 0 = some 0 := Apply.galeShapley_apply 0
