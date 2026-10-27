/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Preferences.Complete
public import MathEconLib.ForMathlib.Order.Refinement

/-!
# Fixed tie-breaking for complete preferences

`CompletePreference.tieBreak` is the preference-facing form of `Order.tieBreakOrder`.
It uses the supplied complete preference and a fixed injective priority; larger priorities
resolve indifference. It does not complete missing comparisons or assert attainment on a menu.
-/

@[expose] public section

namespace MathEconLib.Preferences.CompletePreference

variable {X U : Type*} [LinearOrder U]

/-- Resolve indifference by the supplied priority using the shared total-preorder construction. -/
@[instance_reducible]
noncomputable def tieBreak (R : CompletePreference X) (priority : X ↪ U) : LinearOrder X :=
  Order.tieBreakOrder R.toPreference.toPreorder R.isTotal priority

/-- The tie-break preserves weak preference and compares priorities only within indifference. -/
theorem tieBreak_le_iff (R : CompletePreference X) (priority : X ↪ U) (x y : X) :
    (R.tieBreak priority).le x y ↔
      R.le x y ∧ (AntisymmRel R.le x y → priority x ≤ priority y) :=
  Order.tieBreakOrder_le_iff R.toPreference.toPreorder R.isTotal priority x y

/-- A comparison after tie-breaking is a comparison in the original preference. -/
theorem le_of_tieBreak_le (R : CompletePreference X) (priority : X ↪ U) {x y : X}
    (h : (R.tieBreak priority).le x y) : R.le x y :=
  (R.tieBreak_le_iff priority x y).mp h |>.1

/-- Tie-breaking the complete preference of a linear order recovers that order. -/
@[simp] theorem tieBreak_ofLinearOrder (L : LinearOrder X) (priority : X ↪ U) :
    (ofLinearOrder L).tieBreak priority = L := by
  simpa only [tieBreak, toPreorder_ofLinearOrder] using
    Order.tieBreakOrder_of_linearOrder L priority

end MathEconLib.Preferences.CompletePreference
