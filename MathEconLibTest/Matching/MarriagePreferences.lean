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

example (μ : M ≃. W) (m : M) (partner : W) :
    mkt.BlocksM μ m partner ↔ (μ m) ≺[mkt.preferenceM m] some partner :=
  mkt.blocksM_iff_preferenceM_lt μ m partner

example (μ : M ≃. W) (w : W) (partner : M) :
    mkt.BlocksW μ w partner ↔ (μ.symm w) ≺[mkt.preferenceW w] some partner :=
  mkt.blocksW_iff_preferenceW_lt μ w partner

example (m : M) : mkt.symm.preferenceW m = mkt.preferenceM m := mkt.preferenceW_symm m

example (w : W) : mkt.symm.preferenceM w = mkt.preferenceW w := mkt.preferenceM_symm w

example (m : M) : mkt.symm.preferenceW m = mkt.preferenceM m := by simp

example (w : W) : mkt.symm.preferenceM w = mkt.preferenceW w := by simp

/-- Opposite rankings on the two sides ensure acceptability need not be mutual: men use
`WithBot ℕ`, where being single is worst, and women use `WithTop ℕ`, where it is best. -/
def asymmetric : MarriageMarket ℕ ℕ where
  prefM _ := inferInstanceAs (LinearOrder (WithBot ℕ))
  prefW _ := inferInstanceAs (LinearOrder (WithTop ℕ))

example : none ≺[asymmetric.preferenceM 0] some 0 := by
  rw [← asymmetric.acceptableM_iff_preferenceM_lt]
  exact WithBot.bot_lt_coe (0 : ℕ)

example : ¬ none ≺[asymmetric.preferenceW 0] some 0 := by
  rw [← asymmetric.acceptableW_iff_preferenceW_lt]
  exact not_top_lt (a := ((0 : ℕ) : WithTop ℕ))

/-- Opposite rankings of real partners: men rank by `WithBot ℕ`, women by its order dual, so
the two sides compare `some 0` and `some 1` in opposite directions. -/
def reversed : MarriageMarket ℕ ℕ where
  prefM _ := inferInstanceAs (LinearOrder (WithBot ℕ))
  prefW _ := inferInstanceAs (LinearOrder (WithBot ℕ)ᵒᵈ)

example : some 0 ≺[reversed.preferenceM 0] some 1 := by
  rw [← reversed.ltM_iff_preferenceM_lt]
  change ((0 : ℕ) : WithBot ℕ) < ((1 : ℕ) : WithBot ℕ)
  exact WithBot.coe_lt_coe.mpr Nat.zero_lt_one

example : some 1 ≺[reversed.preferenceW 0] some 0 := by
  rw [← reversed.ltW_iff_preferenceW_lt]
  change ((0 : ℕ) : WithBot ℕ) < ((1 : ℕ) : WithBot ℕ)
  exact WithBot.coe_lt_coe.mpr Nat.zero_lt_one

end MathEconLibTest.Matching.MarriagePreferences
