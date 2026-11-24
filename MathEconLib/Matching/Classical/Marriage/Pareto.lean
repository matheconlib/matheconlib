/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Classical.Marriage.Basic
public import MathEconLib.Welfare.Choice

/-!
# Men's preferences over partial matchings

A man ranks matchings by his assigned partner. The assignment `none` means he remains single.
He is indifferent between matchings that give him the same assignment.
In the reversed market, `mkt.symm.matchingPreferenceM w` ranks the reversed matchings for woman `w`.
On the stable set, man-optimality is greatestness for the men's unanimous preference, which
implies Pareto efficiency there. For proposer-side weak Pareto optimality on the larger set,
use `mkt.IndividuallyRationalW` to admit every matching that is individually rational for women.
-/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

open Preferences Welfare

variable {M W : Type*} (mkt : MarriageMarket M W)

/-- Pull man `m`'s complete partner ranking back to partial matchings. -/
def completeMatchingPreferenceM (m : M) : CompletePreference (M ≃. W) :=
  (CompletePreference.ofLinearOrder (mkt.prefM m)).comap (fun μ ↦ μ m)

/-- Man `m`'s ranking of partial matchings by the partner they assign him. -/
def matchingPreferenceM (m : M) : Preference (M ≃. W) :=
  (mkt.completeMatchingPreferenceM m).toPreference

instance (m : M) : Std.Total (mkt.matchingPreferenceM m).le :=
  (mkt.completeMatchingPreferenceM m).isTotal

@[simp]
theorem matchingPreferenceM_le (m : M) (μ ν : M ≃. W) :
    (mkt.matchingPreferenceM m).le μ ν ↔ mkt.leM m (μ m) (ν m) := Iff.rfl

@[simp]
theorem matchingPreferenceM_lt (m : M) (μ ν : M ≃. W) :
    (mkt.matchingPreferenceM m).lt μ ν ↔ mkt.ltM m (μ m) (ν m) := by
  let := mkt.prefM m
  exact lt_iff_le_not_ge.symm

/-- Two matchings are tied for a man exactly when they assign him the same partner. -/
@[simp]
theorem matchingPreferenceM_antisymmRel_iff (m : M) (μ ν : M ≃. W) :
    AntisymmRel (mkt.matchingPreferenceM m).le μ ν ↔ μ m = ν m := by
  let := mkt.prefM m
  exact le_antisymm_iff.symm

/-- `MenWeaklyPrefer` takes the preferred matching first. -/
theorem unanimousPreference_matchingPreferenceM_le_iff (μ ν : M ≃. W) :
    (unanimousPreference mkt.matchingPreferenceM).le μ ν ↔ mkt.MenWeaklyPrefer ν μ := Iff.rfl

/-- Weak efficiency rules out a feasible matching that gives every man a strictly better partner. -/
theorem isWeaklyParetoEfficient_matchingPreferenceM_iff (F : Set (M ≃. W)) (μ : M ≃. W) :
    IsWeaklyParetoEfficient mkt.matchingPreferenceM F μ ↔
      μ ∈ F ∧ ∀ ν ∈ F, ¬ ∀ m, mkt.ltM m (μ m) (ν m) := by
  simp only [isWeaklyParetoEfficient_iff, UnanimousStrictImprovement, matchingPreferenceM_lt]

/-- A man-optimal stable matching is a greatest feasible choice for the men's unanimous ranking
on the stable set. -/
theorem isManOptimal_iff_mem_maximizers (μ : M ≃. W) :
    mkt.IsManOptimal μ ↔
      μ ∈ Choice.maximizers (unanimousPreference mkt.matchingPreferenceM) mkt.IsStableMatching :=
  Iff.rfl

variable {mkt}

/-- A man-optimal stable matching is Pareto efficient for the men among stable matchings. -/
theorem IsManOptimal.isParetoEfficient_among_stable {μ : M ≃. W} (hμ : mkt.IsManOptimal μ) :
    IsParetoEfficient mkt.matchingPreferenceM mkt.IsStableMatching μ :=
  isParetoEfficient_of_mem_maximizers ((mkt.isManOptimal_iff_mem_maximizers μ).mp hμ)

end MathEconLib.Matching.MarriageMarket
