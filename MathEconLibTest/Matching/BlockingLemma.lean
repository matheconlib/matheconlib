/-
Copyright (c) 2026 Ayan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayan
-/
module

import MathEconLibExamples.Matching.BlockingLemma

/-! Regression checks reusing the blocking-lemma examples. Generic API applications
through the public root are in `MathEconLibTest.Matching.PublicImport`. -/

open MathEconLib.Matching MarriageMarket
open MathEconLibExamples.Matching.BlockingLemma

/-! The blocking pair in the trade market, and the failure without the women's half. -/

example : Trade.market.IsBlockingPair Trade.traded 0 1 := Trade.isBlockingPair_traded.2.2

example : (∀ m, Unwilling.market.ltM m (Unwilling.market.galeShapley m) (Unwilling.paired m)) ∧
    ∀ m w, ¬ Unwilling.market.IsBlockingPair Unwilling.paired m w :=
  ⟨Unwilling.forall_ltM_galeShapley_paired, Unwilling.paired_not_isBlockingPair⟩

/-! The women's half of individual rationality cannot be dropped. -/

example : Unwilling.market.IndividuallyRationalM Unwilling.paired ∧
    ∀ m, Unwilling.market.ltM m (Unwilling.market.galeShapley m) (Unwilling.paired m) :=
  ⟨Unwilling.paired_individuallyRationalM, Unwilling.forall_ltM_galeShapley_paired⟩

/-! Full Pareto efficiency for men fails. -/

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
