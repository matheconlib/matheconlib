/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Matching.Classical.Marriage

/-!
Public-import checks for the marriage model's shared preference interface.
-/

@[expose] public section

namespace MathEconLibTest.Matching.MarriagePreferences

open MathEconLib.Matching MathEconLib.Preferences

variable {M W : Type*} (mkt : MarriageMarket M W)

example (m : M) : mkt.preferenceM m =
    CompletePreference.ofLinearOrder (mkt.prefM m) := rfl

example (m : M) : Std.Antisymm (mkt.preferenceM m).le := inferInstance

example (m : M) (y z : Option W) :
    mkt.leM m y z ↔ y ≼[mkt.preferenceM m] z :=
  mkt.leM_iff_preferenceM_le m y z

example (m : M) (y z : Option W) :
    mkt.ltM m y z ↔ y ≺[mkt.preferenceM m] z :=
  mkt.ltM_iff_preferenceM_lt m y z

example (m : M) (partner : W) :
    mkt.AcceptableM m partner ↔ none ≺[mkt.preferenceM m] some partner :=
  mkt.acceptableM_iff_preferenceM_lt m partner

example (μ : M ≃. W) (m : M) :
    mkt.IndividuallyRationalForM μ m ↔ none ≼[mkt.preferenceM m] (μ m) :=
  mkt.individuallyRationalForM_iff_preferenceM_le μ m

example (w : W) : mkt.preferenceW w =
    CompletePreference.ofLinearOrder (mkt.prefW w) := rfl

example (w : W) : Std.Antisymm (mkt.preferenceW w).le := inferInstance

example (w : W) (y z : Option M) :
    mkt.leW w y z ↔ y ≼[mkt.preferenceW w] z :=
  mkt.leW_iff_preferenceW_le w y z

example (w : W) (y z : Option M) :
    mkt.ltW w y z ↔ y ≺[mkt.preferenceW w] z :=
  mkt.ltW_iff_preferenceW_lt w y z

example (w : W) (partner : M) :
    mkt.AcceptableW w partner ↔ none ≺[mkt.preferenceW w] some partner :=
  mkt.acceptableW_iff_preferenceW_lt w partner

example (μ : M ≃. W) (w : W) :
    mkt.IndividuallyRationalForW μ w ↔ none ≼[mkt.preferenceW w] (μ.symm w) :=
  mkt.individuallyRationalForW_iff_preferenceW_le μ w

example (μ : M ≃. W) (m : M) (w : W) :
    mkt.IsBlockingPair μ m w ↔
      (μ m) ≺[mkt.preferenceM m] some w ∧ (μ.symm w) ≺[mkt.preferenceW w] some m :=
  mkt.isBlockingPair_iff_preference_lt μ m w

example (m : M) : mkt.symm.preferenceW m = mkt.preferenceM m := by simp

example (w : W) : mkt.symm.preferenceM w = mkt.preferenceW w := by simp

/-- Rank being single lowest and partner `n` at height `n + 1`. -/
def rank : Option ℕ → ℕ
  | none => 0
  | some n => n + 1

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

/-- Men rank being single below every partner. -/
@[instance_reducible] def singleLowest : LinearOrder (Option ℕ) :=
  LinearOrder.lift' rank rank_injective

/-- Women reverse that ranking, so being single is their favorite option. -/
@[instance_reducible] def singleHighest : LinearOrder (Option ℕ) :=
  LinearOrder.lift' (OrderDual.toDual ∘ rank) (OrderDual.toDual.injective.comp rank_injective)

/-- Opposite rankings on the two sides ensure acceptability need not be mutual. -/
def asymmetric : MarriageMarket ℕ ℕ where
  prefM _ := singleLowest
  prefW _ := singleHighest

example : none ≺[asymmetric.preferenceM 0] some 0 := by
  rw [← asymmetric.acceptableM_iff_preferenceM_lt]
  change rank none < rank (some 0)
  decide

example : ¬ none ≺[asymmetric.preferenceW 0] some 0 := by
  rw [← asymmetric.acceptableW_iff_preferenceW_lt]
  change ¬ OrderDual.toDual (rank none) < OrderDual.toDual (rank (some 0))
  rw [OrderDual.toDual_lt_toDual]
  decide

end MathEconLibTest.Matching.MarriagePreferences
