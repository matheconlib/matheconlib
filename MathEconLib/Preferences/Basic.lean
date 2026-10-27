/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/

module

public import Mathlib.Order.Antisymmetrization

/-!
# Preference Relations

This file defines preferences on an arbitrary type of alternatives. A preference is a reflexive,
transitive weak comparison. Completeness is not assumed, so two alternatives may be incomparable, as
when consumption bundles are compared coordinate by coordinate (for complete preferences, see
[Complete.lean](MathEconLib/Preferences/Complete.lean).

## Main Definitions

* `Preference` — a reflexive, transitive weak comparison, stored as an `IsPreorder` law.
* `Preference.lt` — strict preference: the weak comparison holds and its reverse fails.
* `Preference.toPreorder`, `Preference.ofPreorder` — the correspondence between preferences and
  preorders on the same alternatives.
* `Preference.comap` — the preference that compares alternatives by their images under a map.

## Main Statements

* `Preference.toPreorder_ofPreorder`, `Preference.ofPreorder_toPreorder` — preferences and preorders
  determine each other.
* `Preference.comap_id`, `Preference.comap_comp` — changes of alternatives respect identities and
  composition.
* `Preference.antisymm_comap` — injective changes of alternatives preserve antisymmetry.
* `Preference.lt_trans`, `Preference.lt_of_le_of_lt`, `Preference.lt_of_lt_of_le` — strict and weak
  preference compose transitively.

## Notation

The following notation is scoped to `MathEconLib.Preferences`.

* `x ≼[R] y` — `y` is weakly preferred to `x`, that is, `R.le x y`.
* `x ≺[R] y` — `y` is strictly preferred to `x`, that is, `R.lt x y`.
* `x ~[R] y` — `x` and `y` are indifferent, that is, `AntisymmRel R.le x y`.

## Implementation Notes

`Preference.toPreorder` is a definition rather than an instance, so a preference does not fix an
order on its type of alternatives. The strict-preference lemmas are stated with `≺[R]` and apply
without a local order instance.

## Tags

preference, preorder, strict preference, indifference, incomplete preference
-/

@[expose] public section

namespace MathEconLib

namespace Preferences

/-- A reflexive, transitive preference on alternatives `X`, with `le x y` meaning that `y` is at
least as good as `x`. Incomparable alternatives are allowed. -/
structure Preference (X : Type*) where
  /-- Weak comparison, oriented toward the better alternative. -/
  le : X → X → Prop
  /-- Weak comparison is reflexive and transitive. -/
  isPreorder : IsPreorder X le

scoped notation:50 x:50 " ≼[" R "] " y:50 => Preference.le R x y

namespace Preference

variable {X Y Z : Type*}

instance (R : Preference X) : IsPreorder X R.le := R.isPreorder

/-- Strict preference for `y` over `x`: the forward weak comparison holds and the reverse fails. -/
def lt (R : Preference X) (x y : X) : Prop := x ≼[R] y ∧ ¬y ≼[R] x

end Preference

scoped notation:50 x:50 " ≺[" R "] " y:50 => Preference.lt R x y
scoped notation:50 x:50 " ~[" R "] " y:50 => AntisymmRel (Preference.le R) x y

namespace Preference

variable {X Y Z : Type*}

/-- Preferences agree when every weak comparison agrees. -/
@[ext]
theorem ext {R S : Preference X} (h : ∀ x y, x ≼[R] y ↔ x ≼[S] y) : R = S := by
  cases R
  cases S
  congr
  exact funext₂ fun x y => propext (h x y)

/-- Every alternative is weakly as good as itself. -/
@[simp]
theorem le_refl (R : Preference X) (x : X) : x ≼[R] x := refl x

/-- Reflexivity with the alternative implicit. -/
theorem le_rfl (R : Preference X) {x : X} : x ≼[R] x := R.le_refl x

/-- Weak comparison is transitive. -/
theorem le_trans (R : Preference X) {x y z : X}
    (hxy : x ≼[R] y) (hyz : y ≼[R] z) : x ≼[R] z := _root_.trans hxy hyz

/-- The order on alternatives specified by a preference. -/
@[instance_reducible]
def toPreorder (R : Preference X) : Preorder X where
  le := R.le
  lt := R.lt
  le_refl := R.le_refl
  le_trans := fun _ _ _ => R.le_trans
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

@[simp]
theorem toPreorder_le (R : Preference X) (x y : X) :
    R.toPreorder.le x y ↔ x ≼[R] y := Iff.rfl

@[simp]
theorem toPreorder_lt (R : Preference X) (x y : X) :
    R.toPreorder.lt x y ↔ x ≺[R] y := Iff.rfl

/-- Regard an order as a preference, with larger alternatives preferred. -/
def ofPreorder (p : Preorder X) : Preference X where
  le := p.le
  isPreorder := by let := p; infer_instance

@[simp]
theorem toPreorder_ofPreorder (p : Preorder X) : (ofPreorder p).toPreorder = p :=
  Preorder.ext fun _ _ => Iff.rfl

@[simp]
theorem ofPreorder_toPreorder (R : Preference X) : ofPreorder R.toPreorder = R := rfl

/-- Compare alternatives by their images under `f`. -/
def comap (R : Preference Y) (f : X → Y) : Preference X where
  le x y := f x ≼[R] f y
  isPreorder := { refl := fun x => R.le_refl (f x), trans := fun _ _ _ => R.le_trans }

@[simp]
theorem comap_le (R : Preference Y) (f : X → Y) (x y : X) :
    x ≼[R.comap f] y ↔ f x ≼[R] f y := Iff.rfl

@[simp]
theorem comap_id (R : Preference X) : R.comap id = R := rfl

theorem comap_comp (R : Preference Z) (f : Y → Z) (g : X → Y) :
    (R.comap f).comap g = R.comap (f ∘ g) := rfl

theorem toPreorder_comap (R : Preference Y) (f : X → Y) :
    (R.comap f).toPreorder = @Preorder.lift X Y R.toPreorder f :=
  Preorder.ext fun _ _ => Iff.rfl

/-- Injective changes of alternatives preserve antisymmetry. -/
theorem antisymm_comap (R : Preference Y) {f : X → Y} (hf : Function.Injective f)
    [Std.Antisymm R.le] : Std.Antisymm (R.comap f).le :=
  ⟨fun _ _ hxy hyx => hf (antisymm hxy hyx)⟩

@[simp]
theorem lt_irrefl (R : Preference X) (x : X) : ¬x ≺[R] x := by
  let := R.toPreorder
  exact _root_.lt_irrefl x

theorem lt_asymm (R : Preference X) {x y : X} (hxy : x ≺[R] y) : ¬y ≺[R] x := by
  let := R.toPreorder
  exact @_root_.lt_asymm X R.toPreorder x y hxy

theorem lt_trans (R : Preference X) {x y z : X}
    (hxy : x ≺[R] y) (hyz : y ≺[R] z) : x ≺[R] z := by
  let := R.toPreorder
  exact @_root_.lt_trans X R.toPreorder x y z hxy hyz

theorem lt_of_le_of_lt (R : Preference X) {x y z : X}
    (hxy : x ≼[R] y) (hyz : y ≺[R] z) : x ≺[R] z := by
  let := R.toPreorder
  exact @_root_.lt_of_le_of_lt X R.toPreorder x y z hxy hyz

theorem lt_of_lt_of_le (R : Preference X) {x y z : X}
    (hxy : x ≺[R] y) (hyz : y ≼[R] z) : x ≺[R] z := by
  let := R.toPreorder
  exact @_root_.lt_of_lt_of_le X R.toPreorder x y z hxy hyz

theorem le_of_lt (R : Preference X) {x y : X} (hxy : x ≺[R] y) : x ≼[R] y := by
  let := R.toPreorder
  exact @_root_.le_of_lt X R.toPreorder x y hxy

end Preference
end Preferences

end MathEconLib

end
