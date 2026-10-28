/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/

module

public import MathEconLib.Preferences.Basic

/-!
# Complete Preferences

This file defines complete preferences: preferences that compare every pair of alternatives. A
complete preference is a total preorder. When indifference implies equality, the preference is a
linear order on the alternatives.

## Main Definitions

* `CompletePreference` — a `Preference` whose weak comparison is total; it coerces to `Preference`.
* `CompletePreference.ofPreorder`, `CompletePreference.ofLinearOrder` — the complete preferences
  determined by a total preorder and by a linear order.
* `CompletePreference.comap` — the complete preference that compares alternatives by their images
  under a map.
* `CompletePreference.toLinearOrder` — the linear order determined by a complete preference with
  antisymmetric weak comparison.

## Main Statements

* `CompletePreference.total` — every pair of alternatives is weakly ranked in at least one
  direction.
* `CompletePreference.not_le` — failure of a weak comparison is strict preference in the reverse
  direction.
* `CompletePreference.lt_or_antisymmRel_or_gt` — any two alternatives are strictly ranked in one
  direction or indifferent.
* `CompletePreference.ofLinearOrder_toLinearOrder` — an antisymmetric complete preference is the
  preference of its linear order.

## Tags

preference, complete preference, total preorder, linear order, indifference
-/

@[expose] public section

namespace MathEconLib

namespace Preferences

/-- A preference that compares every pair of alternatives, while allowing indifference. -/
structure CompletePreference (X : Type*) extends Preference X where
  /-- Every pair admits a weak comparison in at least one direction. -/
  isTotal : Std.Total le

attribute [coe] CompletePreference.toPreference

instance {X : Type*} : CoeOut (CompletePreference X) (Preference X) :=
  ⟨CompletePreference.toPreference⟩

namespace CompletePreference

variable {X Y : Type*}

instance (R : CompletePreference X) : Std.Total R.le := R.isTotal

/-- Every pair of alternatives can be compared. -/
theorem total (R : CompletePreference X) (x y : X) : x ≼[R] y ∨ y ≼[R] x :=
  total_of R.le x y

/-- A total preorder determines a complete preference. -/
def ofPreorder (p : Preorder X) (h : Std.Total p.le) : CompletePreference X where
  toPreference := Preference.ofPreorder p
  isTotal := h

/-- A linear order determines a complete preference with no ties between distinct alternatives. -/
def ofLinearOrder (L : LinearOrder X) : CompletePreference X :=
  ofPreorder L.toPreorder ⟨@le_total X L⟩

@[simp]
theorem toPreorder_ofPreorder (p : Preorder X) (h : Std.Total p.le) :
    (ofPreorder p h).toPreference.toPreorder = p := Preference.toPreorder_ofPreorder p

@[simp]
theorem ofPreorder_toPreorder (R : CompletePreference X) :
    ofPreorder R.toPreference.toPreorder R.isTotal = R := rfl

@[simp]
theorem toPreorder_ofLinearOrder (L : LinearOrder X) :
    (ofLinearOrder L).toPreference.toPreorder = L.toPreorder :=
  Preference.toPreorder_ofPreorder L.toPreorder

/-- Compare alternatives by a map into a completely ranked space. -/
def comap (R : CompletePreference Y) (f : X → Y) : CompletePreference X where
  toPreference := R.toPreference.comap f
  isTotal := ⟨fun x y => R.total (f x) (f y)⟩

@[simp]
theorem toPreference_comap (R : CompletePreference Y) (f : X → Y) :
    (R.comap f).toPreference = R.toPreference.comap f := rfl

instance (L : LinearOrder X) : Std.Antisymm (ofLinearOrder L).le :=
  ⟨@le_antisymm X L.toPartialOrder⟩

instance (R : CompletePreference X) [Std.Antisymm R.le] : IsLinearOrder X R.le := {}

/-- A complete preference with antisymmetric weak comparison gives a linear order. -/
@[instance_reducible]
noncomputable def toLinearOrder (R : CompletePreference X)
    [Std.Antisymm R.le] :
    LinearOrder X where
  toPreorder := R.toPreference.toPreorder
  le_antisymm := fun _ _ => antisymm
  le_total := R.total
  toDecidableLE := Classical.decRel R.le

@[simp]
theorem ofLinearOrder_toLinearOrder (R : CompletePreference X)
    [Std.Antisymm R.le] :
    ofLinearOrder R.toLinearOrder = R := rfl

/-- Failure of a weak comparison is the reverse strict preference. -/
theorem not_le (R : CompletePreference X) {x y : X} : ¬x ≼[R] y ↔ y ≺[R] x :=
  ⟨fun h => ⟨(R.total x y).resolve_left h, h⟩, fun h => h.2⟩

/-- Alternatives are strictly ranked in one direction or indifferent. -/
theorem lt_or_antisymmRel_or_gt (R : CompletePreference X) (x y : X) :
    x ≺[R] y ∨ x ~[R] y ∨ y ≺[R] x := by
  by_cases hxy : x ≼[R] y
  · by_cases hyx : y ≼[R] x
    · exact Or.inr (Or.inl ⟨hxy, hyx⟩)
    · exact Or.inl ⟨hxy, hyx⟩
  · exact Or.inr (Or.inr (R.not_le.mp hxy))

end CompletePreference
end Preferences

end MathEconLib

end
