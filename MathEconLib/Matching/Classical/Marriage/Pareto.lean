/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Classical.Marriage.Basic
public import MathEconLib.Welfare.Pareto

/-!
# Men's preferences over partial matchings

A man ranks matchings by his assigned partner. The assignment `none` means he remains single.
He is indifferent between matchings that give him the same assignment.
In the reversed market, `mkt.symm.matchingPreferenceM w` ranks the reversed matchings for woman `w`.
Choose the feasible set separately. For proposer-side weak Pareto optimality, use
`mkt.IndividuallyRationalW` to admit every matching that the women find individually rational.
-/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

open Preferences Welfare

variable {M W : Type*} (mkt : MarriageMarket M W)

/-- Man `m`'s ranking of partial matchings by the partner they assign him. -/
def matchingPreferenceM (m : M) : Preference (M ≃. W) :=
  (Preference.ofPreorder (mkt.prefM m).toPreorder).comap (fun μ ↦ μ m)

@[simp]
theorem matchingPreferenceM_le (m : M) (μ ν : M ≃. W) :
    (mkt.matchingPreferenceM m).le μ ν ↔ mkt.leM m (μ m) (ν m) := Iff.rfl

@[simp]
theorem matchingPreferenceM_lt (m : M) (μ ν : M ≃. W) :
    (mkt.matchingPreferenceM m).lt μ ν ↔ mkt.ltM m (μ m) (ν m) := by
  let := mkt.prefM m
  exact lt_iff_le_not_ge.symm

/-- `MenWeaklyPrefer` takes the preferred matching first. -/
theorem unanimousPreference_matchingPreferenceM_le_iff (μ ν : M ≃. W) :
    (unanimousPreference mkt.matchingPreferenceM).le μ ν ↔ mkt.MenWeaklyPrefer ν μ := Iff.rfl

/-- Weak efficiency rules out a feasible matching that gives every man a strictly better partner. -/
theorem isWeaklyParetoEfficient_matchingPreferenceM_iff (F : Set (M ≃. W)) (μ : M ≃. W) :
    IsWeaklyParetoEfficient mkt.matchingPreferenceM F μ ↔
      μ ∈ F ∧ ∀ ν ∈ F, ¬ ∀ m, mkt.ltM m (μ m) (ν m) := by
  simp only [isWeaklyParetoEfficient_iff, UnanimousStrictImprovement, matchingPreferenceM_lt]

end MathEconLib.Matching.MarriageMarket
