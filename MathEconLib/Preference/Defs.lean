/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import Mathlib.Order.Antisymmetrization

/-!
# Preference relations: definitions

A preference relation on `X` is a relation `R : X → X → Prop`; `R x y` reads "`x` is at least as
good as `y`". Its properties are `def`s for Mathlib's classes, not instances, so each theorem
states the ones it uses.

## Main definitions

* `IsComplete`, `IsReflexive`, `IsTransitive`, `IsAntisymmetric`: properties of a relation.
* `IsPreferenceRelation`: complete and transitive; `IsLinearPreference`: also antisymmetric.
* `StrictPart`, `Indiff`: strict preference `x ≻ y` and indifference `x ∼ y`.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Section 1.1
-/

@[expose] public section

namespace MathEconLib.Preference

universe u

variable {X : Type u} {R : X → X → Prop} {x y z : X}

/-- `R` is complete: for all `x` and `y`, `R x y` or `R y x` (Mathlib's `Std.Total R`). -/
def IsComplete (R : X → X → Prop) : Prop := Std.Total R

/-- `R` is reflexive: `R x x` for every `x` (`Std.Refl R`). -/
def IsReflexive (R : X → X → Prop) : Prop := Std.Refl R

/-- `R` is transitive: `R x y` and `R y z` imply `R x z` (Mathlib's `IsTrans X R`). -/
def IsTransitive (R : X → X → Prop) : Prop := IsTrans X R

/-- `R` is antisymmetric: `R x y` and `R y x` imply `x = y` (`Std.Antisymm R`). -/
def IsAntisymmetric (R : X → X → Prop) : Prop := Std.Antisymm R

/-- `R` is a preference relation: it is complete and transitive. -/
def IsPreferenceRelation (R : X → X → Prop) : Prop := IsComplete R ∧ IsTransitive R

/-- `R` is a linear preference: an antisymmetric preference relation. -/
def IsLinearPreference (R : X → X → Prop) : Prop := IsPreferenceRelation R ∧ IsAntisymmetric R

/-- The strict part `≻` of `R`: `x ≻ y` if `R x y` and not `R y x`. -/
def StrictPart (R : X → X → Prop) (x y : X) : Prop := R x y ∧ ¬ R y x

/-- Indifference `∼` derived from `R`: `x ∼ y` if `R x y` and `R y x` (`AntisymmRel R`). -/
abbrev Indiff (R : X → X → Prop) : X → X → Prop := AntisymmRel R

instance [DecidableRel R] : DecidableRel (StrictPart R) :=
  fun x y => inferInstanceAs (Decidable (R x y ∧ ¬ R y x))

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

instance : IsNonstrictStrictOrder X R (StrictPart R) := ⟨fun _ _ => Iff.rfl⟩

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

@[simp] theorem strictPart_irrefl (R : X → X → Prop) (x : X) : ¬ StrictPart R x x :=
  irrefl x

theorem isComplete_of_total [h : Std.Total R] : IsComplete R := h

theorem isTransitive_of_isTrans [h : IsTrans X R] : IsTransitive R := h

theorem isReflexive_of_refl [h : Std.Refl R] : IsReflexive R := h

theorem isAntisymmetric_of_antisymm [h : Std.Antisymm R] : IsAntisymmetric R := h

@[simp] theorem isPreferenceRelation_ge {α : Type*} [LinearOrder α] :
    IsPreferenceRelation (fun x y : α => y ≤ x) :=
  ⟨isComplete_iff.2 fun x y => le_total y x,
    isTransitive_iff.2 fun _ _ _ hxy hyz => le_trans hyz hxy⟩

theorem StrictPart.rel (h : StrictPart R x y) : R x y := h.1

theorem StrictPart.not_rel (h : StrictPart R x y) : ¬ R y x := h.2

end MathEconLib.Preference

section Examples

open MathEconLib.Preference

example : IsPreferenceRelation (fun x y : ℕ => y ≤ x) :=
  ⟨isComplete_iff.2 fun x y => le_total y x,
    isTransitive_iff.2 fun _ _ _ hxy hyz => le_trans hyz hxy⟩

example (x y : ℕ) : StrictPart (fun x y : ℕ => y ≤ x) x y ↔ y < x :=
  (lt_iff_le_not_ge).symm

example (x y : ℕ) : Indiff (fun x y : ℕ => y ≤ x) x y ↔ x = y :=
  ⟨fun h => le_antisymm h.2 h.1, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩

example : IsTransitive (fun _ _ : ℕ => False) ∧ ¬ IsComplete (fun _ _ : ℕ => False) :=
  ⟨isTransitive_iff.2 fun _ _ _ h => h.elim, fun h => (h.total 0 0).elim id id⟩

example : IsPreferenceRelation (fun _ _ : Bool => True) ∧
    ¬ IsAntisymmetric (fun _ _ : Bool => True) :=
  ⟨⟨isComplete_iff.2 fun _ _ => Or.inl trivial, isTransitive_iff.2 fun _ _ _ _ _ => trivial⟩,
    fun h => Bool.noConfusion (h.antisymm (x := true) (y := false) trivial trivial)⟩

end Examples
