/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

import MathEconLib.Matching
import MathEconLibExamples.Matching.UnbalancedMarriage

/-! The matching adapter retains outside options and the argument order of the marriage API. -/

open MathEconLib.Matching MathEconLib.Welfare

variable {M W : Type*} (mkt : MarriageMarket M W)

example (μ ν : M ≃. W) :
    (unanimousPreference mkt.matchingPreferenceM).le μ ν ↔ mkt.MenWeaklyPrefer ν μ :=
  mkt.unanimousPreference_matchingPreferenceM_le_iff μ ν

example (w : W) (μ ν : M ≃. W) :
    (mkt.symm.matchingPreferenceM w).lt μ.symm ν.symm ↔ mkt.ltW w (μ.symm w) (ν.symm w) :=
  mkt.symm.matchingPreferenceM_lt w μ.symm ν.symm

example (μ : M ≃. W) :
    IsWeaklyParetoEfficient mkt.matchingPreferenceM mkt.IndividuallyRationalW μ ↔
      mkt.IndividuallyRationalW μ ∧
        ∀ ν, mkt.IndividuallyRationalW ν → ¬ ∀ m, mkt.ltM m (μ m) (ν m) :=
  mkt.isWeaklyParetoEfficient_matchingPreferenceM_iff _ _

open MathEconLibExamples.Matching.UnbalancedMarriage

-- Man 2 is single in the diagonal matching and prefers his partner in withThirdMan.
example : (market.matchingPreferenceM 2).lt diagonal withThirdMan := by
  rw [market.matchingPreferenceM_lt]
  change manRank 2 (diagonal 2) < manRank 2 (withThirdMan 2)
  decide
