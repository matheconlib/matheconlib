/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import Mathlib.Order.Antisymmetrization

/-!
# Preference relations: definitions

A preference relation on a type `X` of alternatives is a relation `R : X → X → Prop`, where `R x y`
reads "`x` is at least as good as `y`". Its properties are separate predicates, not fields, so every
theorem states the properties it uses.

## Main definitions

* `MathEconLib.Preference.IsComplete R`: any two alternatives are comparable.
* `MathEconLib.Preference.IsReflexive R`: every alternative is related to itself.
* `MathEconLib.Preference.IsTransitive R`: `R x y` and `R y z` give `R x z`.
* `MathEconLib.Preference.IsAntisymmetric R`: `R x y` and `R y x` give `x = y`.
* `MathEconLib.Preference.IsPreferenceRelation R`: complete and transitive.
* `MathEconLib.Preference.IsLinearPreference R`: an antisymmetric preference relation.
* `MathEconLib.Preference.StrictPart R`: the strict preference `x ≻ y`, `R x y ∧ ¬ R y x`.
* `MathEconLib.Preference.Indiff R`: indifference `x ∼ y`, `R x y ∧ R y x`.

## Implementation notes

* The four properties are Mathlib's `Std.Total`, `Std.Refl`, `IsTrans` and `Std.Antisymm` under
  economic names. They are `def`s, not `abbrev`s, so a hypothesis `h : IsComplete R` is not found by
  type-class search; `isComplete_iff_total` and its siblings pass to Mathlib's classes.
* `IsAntisymmetric` is Mathlib's form. Osborne and Rubinstein's Definition 1.4 (`x ≠ y` and `R x y`
  exclude `R y x`) is equivalent: `isAntisymmetric_iff_not_rel_of_ne`.
* `Indiff` is an `abbrev` of Mathlib's `AntisymmRel`, so that API applies. Mathlib has no named
  strict part of an arbitrary relation, hence `StrictPart`.

## References

Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, expanded second
edition, Open Book Publishers, Section 1.1 (Definitions 1.1–1.4).
[DOI: 10.11647/OBP.0361](https://doi.org/10.11647/OBP.0361).

## Tags

preference relation, complete, transitive, strict preference, indifference
-/

@[expose] public section

namespace MathEconLib.Preference

universe u

variable {X : Type u} {R : X → X → Prop} {x y z : X}

/-! ### Properties of a relation -/

/-- `R` is complete: for all `x` and `y`, `R x y` or `R y x` (Mathlib's `Std.Total R`). -/
def IsComplete (R : X → X → Prop) : Prop := Std.Total R

/-- `R` is reflexive: `R x x` for every `x` (`Std.Refl R`). -/
def IsReflexive (R : X → X → Prop) : Prop := Std.Refl R

/-- `R` is transitive: `R x y` and `R y z` imply `R x z` (Mathlib's `IsTrans X R`). -/
def IsTransitive (R : X → X → Prop) : Prop := IsTrans X R

/-- `R` is antisymmetric: `R x y` and `R y x` imply `x = y` (`Std.Antisymm R`): no two distinct
alternatives are indifferent. -/
def IsAntisymmetric (R : X → X → Prop) : Prop := Std.Antisymm R

/-- `R` is a preference relation: it is complete and transitive. -/
def IsPreferenceRelation (R : X → X → Prop) : Prop := IsComplete R ∧ IsTransitive R

/-- `R` is a linear preference: an antisymmetric preference relation (Mathlib's
`IsLinearOrder X R`, see `isLinearPreference_iff_isLinearOrder`). -/
def IsLinearPreference (R : X → X → Prop) : Prop := IsPreferenceRelation R ∧ IsAntisymmetric R

/-! ### Derived relations -/

/-- The strict part `≻` of `R`: `x ≻ y` if `R x y` and not `R y x`. -/
def StrictPart (R : X → X → Prop) (x y : X) : Prop := R x y ∧ ¬ R y x

/-- Indifference `∼` derived from `R`: `x ∼ y` if `R x y` and `R y x` (Mathlib's
`AntisymmRel R`). -/
abbrev Indiff (R : X → X → Prop) : X → X → Prop := AntisymmRel R

instance [DecidableRel R] : DecidableRel (StrictPart R) :=
  fun x y => inferInstanceAs (Decidable (R x y ∧ ¬ R y x))

/-! ### Unfolding lemmas and bridges to Mathlib's classes -/

theorem isComplete_iff : IsComplete R ↔ ∀ x y, R x y ∨ R y x :=
  ⟨fun h => h.total, fun h => ⟨h⟩⟩

theorem isReflexive_iff : IsReflexive R ↔ ∀ x, R x x :=
  ⟨fun h => h.refl, fun h => ⟨h⟩⟩

theorem isTransitive_iff : IsTransitive R ↔ ∀ x y z, R x y → R y z → R x z :=
  ⟨fun h => h.trans, fun h => ⟨h⟩⟩

theorem isAntisymmetric_iff : IsAntisymmetric R ↔ ∀ x y, R x y → R y x → x = y :=
  ⟨fun h => h.antisymm, fun h => ⟨h⟩⟩

theorem isPreferenceRelation_iff : IsPreferenceRelation R ↔ IsComplete R ∧ IsTransitive R :=
  Iff.rfl

theorem isLinearPreference_iff :
    IsLinearPreference R ↔ IsPreferenceRelation R ∧ IsAntisymmetric R :=
  Iff.rfl

theorem strictPart_iff : StrictPart R x y ↔ R x y ∧ ¬ R y x := Iff.rfl

theorem indiff_iff : Indiff R x y ↔ R x y ∧ R y x := Iff.rfl

theorem isComplete_iff_total : IsComplete R ↔ Std.Total R := Iff.rfl

theorem isReflexive_iff_refl : IsReflexive R ↔ Std.Refl R := Iff.rfl

theorem isTransitive_iff_isTrans : IsTransitive R ↔ IsTrans X R := Iff.rfl

theorem isAntisymmetric_iff_antisymm : IsAntisymmetric R ↔ Std.Antisymm R := Iff.rfl

/-- The strict part of `R` is the strict relation of `R` in Mathlib's sense. -/
instance : IsNonstrictStrictOrder X R (StrictPart R) := ⟨fun _ _ => Iff.rfl⟩

/-! ### Projections -/

theorem IsComplete.total (h : IsComplete R) (x y : X) : R x y ∨ R y x :=
  Std.Total.total (self := h) x y

theorem IsReflexive.refl (h : IsReflexive R) (x : X) : R x x := Std.Refl.refl (self := h) x

theorem IsTransitive.trans (h : IsTransitive R) (hxy : R x y) (hyz : R y z) : R x z :=
  IsTrans.trans (self := h) x y z hxy hyz

theorem IsAntisymmetric.antisymm (h : IsAntisymmetric R) (hxy : R x y) (hyx : R y x) : x = y :=
  Std.Antisymm.antisymm (self := h) x y hxy hyx

theorem IsComplete.toTotal (h : IsComplete R) : Std.Total R := h

theorem IsTransitive.toIsTrans (h : IsTransitive R) : IsTrans X R := h

theorem IsPreferenceRelation.isComplete (h : IsPreferenceRelation R) : IsComplete R := h.1

theorem IsPreferenceRelation.isTransitive (h : IsPreferenceRelation R) : IsTransitive R := h.2

theorem IsPreferenceRelation.total (h : IsPreferenceRelation R) (x y : X) : R x y ∨ R y x :=
  h.1.total x y

theorem IsPreferenceRelation.trans (h : IsPreferenceRelation R) (hxy : R x y) (hyz : R y z) :
    R x z :=
  h.2.trans hxy hyz

theorem IsLinearPreference.isPreferenceRelation (h : IsLinearPreference R) :
    IsPreferenceRelation R := h.1

theorem IsLinearPreference.isAntisymmetric (h : IsLinearPreference R) : IsAntisymmetric R := h.2

/-! ### Basic cases -/

/-- The strict part is irreflexive (Mathlib's `irrefl`, through `IsNonstrictStrictOrder`). -/
@[simp] theorem strictPart_irrefl (R : X → X → Prop) (x : X) : ¬ StrictPart R x x :=
  irrefl x

theorem isComplete_of_total [h : Std.Total R] : IsComplete R := h

theorem isTransitive_of_isTrans [h : IsTrans X R] : IsTransitive R := h

theorem isReflexive_of_refl [h : Std.Refl R] : IsReflexive R := h

theorem isAntisymmetric_of_antisymm [h : Std.Antisymm R] : IsAntisymmetric R := h

/-- `≥` on a linear order is a preference relation. -/
@[simp] theorem isPreferenceRelation_ge {α : Type*} [LinearOrder α] :
    IsPreferenceRelation (fun x y : α => y ≤ x) :=
  ⟨isComplete_iff.2 fun x y => le_total y x,
    isTransitive_iff.2 fun _ _ _ hxy hyz => le_trans hyz hxy⟩

theorem StrictPart.rel (h : StrictPart R x y) : R x y := h.1

theorem StrictPart.not_rel (h : StrictPart R x y) : ¬ R y x := h.2

end MathEconLib.Preference

/-! ### Worked examples -/

section Examples

open MathEconLib.Preference

/-- `≥` on the natural numbers is a preference relation ("more is better"). -/
example : IsPreferenceRelation (fun x y : ℕ => y ≤ x) :=
  ⟨isComplete_iff.2 fun x y => le_total y x,
    isTransitive_iff.2 fun _ _ _ hxy hyz => le_trans hyz hxy⟩

example (x y : ℕ) : StrictPart (fun x y : ℕ => y ≤ x) x y ↔ y < x :=
  (lt_iff_le_not_ge).symm

example (x y : ℕ) : Indiff (fun x y : ℕ => y ≤ x) x y ↔ x = y :=
  ⟨fun h => le_antisymm h.2 h.1, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩

/-- The empty relation is transitive but not complete. -/
example : IsTransitive (fun _ _ : ℕ => False) ∧ ¬ IsComplete (fun _ _ : ℕ => False) :=
  ⟨isTransitive_iff.2 fun _ _ _ h => h.elim, fun h => (h.total 0 0).elim id id⟩

/-- Universal indifference is a preference relation that is not antisymmetric. -/
example : IsPreferenceRelation (fun _ _ : Bool => True) ∧
    ¬ IsAntisymmetric (fun _ _ : Bool => True) :=
  ⟨⟨isComplete_iff.2 fun _ _ => Or.inl trivial, isTransitive_iff.2 fun _ _ _ _ _ => trivial⟩,
    fun h => Bool.noConfusion (h.antisymm (x := true) (y := false) trivial trivial)⟩

end Examples
