/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/

module

public import MathEconLib.Preferences.Complete
public import Mathlib.Order.Filter.Extr

/-!
# Ordinal Utility Representations

This file relates preferences to utilities. A utility `u : X → U` represents a preference when
`x ≼[R] y` holds exactly when `u x ≤ u y`, so larger utilities are better. The codomain `U` may be
any preorder: vector-valued utilities ordered coordinate by coordinate represent incomplete
preferences. A representation is ordinal; it determines only the ranking of alternatives, and
differences between utility values carry no economic meaning.

## Main Definitions

* `Preference.IsRepresentedBy` — a utility represents a preference.
* `Preference.ofUtility` — the preference determined by comparing utility values.
* `CompletePreference.ofUtility` — the complete preference determined by a utility valued in a total
  preorder.

## Main Statements

* `Preference.isRepresentedBy_iff_eq_ofUtility` — a utility represents a preference if and only if
  utility induces that preference.
* `Preference.isRepresentedBy_iff_toPreorder_eq_lift` — the same characterization stated with the
  preorder lifted from the utility scale.
* `Preference.IsRepresentedBy.comap` — composing with a map of alternatives preserves
  representation.
* `Preference.IsRepresentedBy.forall_le_iff_isMaxOn` — under a representation, an alternative is at
  least as good as every alternative on a menu if and only if it maximizes utility on that menu.

## Tags

preference, utility, ordinal representation, multi-utility, maximization
-/

@[expose] public section

namespace MathEconLib

namespace Preferences

namespace Preference

variable {X Y U : Type*}

/-- Utility `u` represents `R` if larger utility is equivalent to weakly better alternatives. -/
def IsRepresentedBy (R : Preference X) [Preorder U] (u : X → U) : Prop :=
  ∀ x y, x ≼[R] y ↔ u x ≤ u y

/-- A utility representation identifies the preference order with the lifted utility order. -/
theorem isRepresentedBy_iff_toPreorder_eq_lift (R : Preference X) [Preorder U] (u : X → U) :
    R.IsRepresentedBy u ↔ R.toPreorder = Preorder.lift u := by
  constructor
  · exact fun h => Preorder.ext h
  · intro h x y
    exact congrArg (fun p : Preorder X => p.le x y) h ▸ Iff.rfl

/-- The preference obtained by comparing utility values. -/
def ofUtility [Preorder U] (u : X → U) : Preference X :=
  (ofPreorder inferInstance).comap u

@[simp]
theorem ofUtility_le_iff [Preorder U] (u : X → U) (x y : X) :
    x ≼[ofUtility u] y ↔ u x ≤ u y := Iff.rfl

@[simp]
theorem ofUtility_lt_iff [Preorder U] (u : X → U) (x y : X) :
    x ≺[ofUtility u] y ↔ u x < u y := lt_iff_le_not_ge.symm

/-- In a partial order, indifferent alternatives have equal utility. -/
@[simp]
theorem ofUtility_antisymmRel_iff [PartialOrder U] (u : X → U) (x y : X) :
    x ~[ofUtility u] y ↔ u x = u y := le_antisymm_iff.symm

/-- A utility represents its induced preference. -/
theorem isRepresentedBy_ofUtility [Preorder U] (u : X → U) :
    (ofUtility u).IsRepresentedBy u := fun _ _ => Iff.rfl

/-- Representation is equality with the preference induced by utility. -/
theorem isRepresentedBy_iff_eq_ofUtility (R : Preference X) [Preorder U] (u : X → U) :
    R.IsRepresentedBy u ↔ R = ofUtility u := by
  constructor
  · exact fun h => Preference.ext h
  · rintro rfl
    exact isRepresentedBy_ofUtility u

/-- Changing alternatives by `f` composes a representing utility with `f`. -/
theorem IsRepresentedBy.comap {R : Preference Y} [Preorder U] {u : Y → U}
    (hu : R.IsRepresentedBy u) (f : X → Y) :
    (R.comap f).IsRepresentedBy (u ∘ f) := fun x y => hu (f x) (f y)

/-- A greatest alternative on a menu has exactly the utility-maximization property. -/
theorem IsRepresentedBy.forall_le_iff_isMaxOn {R : Preference X} [Preorder U] {u : X → U}
    (hu : R.IsRepresentedBy u) {S : Set X} {a : X} :
    (∀ x ∈ S, x ≼[R] a) ↔ IsMaxOn u S a := by
  exact forall₂_congr fun x _ => hu x a

end Preference

namespace CompletePreference

variable {X U : Type*}

/-- Utility in a total preorder gives a complete preference, including when utility has ties. -/
def ofUtility [Preorder U] [Std.Total (α := U) (· ≤ ·)] (u : X → U) :
    CompletePreference X :=
  (ofPreorder inferInstance inferInstance).comap u

@[simp]
theorem toPreference_ofUtility [Preorder U] [Std.Total (α := U) (· ≤ ·)]
    (u : X → U) : (ofUtility u).toPreference = Preference.ofUtility u := rfl

end CompletePreference
end Preferences

end MathEconLib

end
