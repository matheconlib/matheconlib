/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Preferences.Relation
public import MathEconLib.Preferences.Representation.Finite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Utility representations of preference relations

A function `u : X → α` *represents* a relation `R` read from the better alternative if
`R x y ↔ u y ≤ u x`. For `R = S.ge` this is `Preference.IsRepresentedBy`; results here are
either derived from that form or stated for it.

## Main statements

* `Preference.represents_ge_iff`: `u` represents `S.ge` iff `S.IsRepresentedBy u`.
* `Preference.IsRepresentedBy.comp_strictMono`, `IsRepresentedBy.affine`: strictly increasing
  transformations of a utility represent the same preference (Proposition 1.3).
* `exists_represents_of_finite`: on a finite type every preference relation has a utility in `ℝ`
  (Proposition 1.1), derived from `CompletePreference.exists_isRepresentedBy_nat`.

## References

* Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, Sections 1.2
  and 1.4.
-/

@[expose] public section

namespace MathEconLib.Preferences

variable {X α β : Type*} {R : X → X → Prop} {x y : X}

/-- The relation defined by `u`: `x ≿ y` if and only if `u y ≤ u x`. -/
def UtilityRel [LE α] (u : X → α) (x y : X) : Prop := u y ≤ u x

instance [LE α] [DecidableLE α] (u : X → α) : DecidableRel (UtilityRel u) :=
  fun x y => inferInstanceAs (Decidable (u y ≤ u x))

/-- `u` is a utility function for `R`: `R x y` if and only if `u y ≤ u x`. -/
def Represents [LE α] (u : X → α) (R : X → X → Prop) : Prop := ∀ x y, R x y ↔ u y ≤ u x

@[simp]
theorem utilityRel_iff [LE α] (u : X → α) : UtilityRel u x y ↔ u y ≤ u x := Iff.rfl

theorem utilityRel_eq_ge [Preorder α] (u : X → α) :
    UtilityRel u = (Preference.ofUtility u).ge := rfl

theorem represents_iff_eq [LE α] {u : X → α} : Represents u R ↔ R = UtilityRel u :=
  ⟨fun h => funext₂ fun x y => propext (h x y), fun h => h ▸ fun _ _ => Iff.rfl⟩

@[simp]
theorem represents_utilityRel [LE α] (u : X → α) : Represents u (UtilityRel u) :=
  fun _ _ => Iff.rfl

namespace Preference

/-- A utility represents the reversed comparison `S.ge` exactly when it represents `S`. -/
theorem represents_ge_iff [Preorder α] {S : Preference X} {u : X → α} :
    Represents u S.ge ↔ S.IsRepresentedBy u :=
  ⟨fun h x y => h y x, fun h x y => h y x⟩

/-- **Proposition 1.3**: a strictly increasing function of a utility for `S` is a utility for
`S`. -/
theorem IsRepresentedBy.comp_strictMono [LinearOrder α] [Preorder β] {S : Preference X}
    {u : X → α} {f : α → β} (hu : S.IsRepresentedBy u) (hf : StrictMono f) :
    S.IsRepresentedBy (f ∘ u) :=
  fun x y => (hu x y).trans hf.le_iff_le.symm

theorem IsRepresentedBy.affine {S : Preference X} {u : X → ℝ} (hu : S.IsRepresentedBy u) {a : ℝ}
    (ha : 0 < a) (b : ℝ) : S.IsRepresentedBy fun x => a * u x + b :=
  hu.comp_strictMono (f := fun t => a * t + b) fun s t hst => by simp only; nlinarith

end Preference

/-- **Proposition 1.3** for relations: a strictly increasing function of a utility for `R` is a
utility for `R`. -/
theorem Represents.comp_strictMono [LinearOrder α] [Preorder β] {u : X → α} {f : α → β}
    (hu : Represents u R) (hf : StrictMono f) : Represents (fun x => f (u x)) R :=
  fun x y => (hu x y).trans hf.le_iff_le.symm

theorem Represents.affine {u : X → ℝ} (hu : Represents u R) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Represents (fun x => a * u x + b) R :=
  hu.comp_strictMono (f := fun t => a * t + b) fun s t hst => by simp only; nlinarith

theorem Represents.strictPart_iff [Preorder α] {u : X → α} (h : Represents u R) :
    StrictPart R x y ↔ u y < u x := by
  rw [Preferences.strictPart_iff, h x y, h y x, lt_iff_le_not_ge]

theorem Represents.indiff_iff [PartialOrder α] {u : X → α} (h : Represents u R) :
    Indiff R x y ↔ u x = u y := by
  rw [Preferences.indiff_iff, h x y, h y x]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

@[simp]
theorem strictPart_utilityRel_iff [Preorder α] (u : X → α) :
    StrictPart (UtilityRel u) x y ↔ u y < u x :=
  Preference.ofUtility_lt_iff u y x

@[simp]
theorem indiff_utilityRel_iff [PartialOrder α] (u : X → α) :
    Indiff (UtilityRel u) x y ↔ u x = u y :=
  (Preference.indiff_ge _).trans (Preference.ofUtility_antisymmRel_iff u x y)

theorem isTransitive_utilityRel [Preorder α] (u : X → α) : IsTransitive (UtilityRel u) :=
  (Preference.ofUtility u).isTransitive_ge

/-- The relation defined by a function into a linear order is a preference relation. -/
theorem isPreferenceRelation_utilityRel [LinearOrder α] (u : X → α) :
    IsPreferenceRelation (UtilityRel u) :=
  (CompletePreference.ofUtility u).isPreferenceRelation_ge

theorem Represents.isTransitive [Preorder α] {u : X → α} (h : Represents u R) : IsTransitive R :=
  represents_iff_eq.1 h ▸ isTransitive_utilityRel u

/-- A relation represented by a function into a linear order is a preference relation. -/
theorem Represents.isPreferenceRelation [LinearOrder α] {u : X → α} (h : Represents u R) :
    IsPreferenceRelation R :=
  represents_iff_eq.1 h ▸ isPreferenceRelation_utilityRel u

theorem isAntisymmetric_utilityRel_iff [PartialOrder α] {u : X → α} :
    IsAntisymmetric (UtilityRel u) ↔ Function.Injective u :=
  ⟨fun h _ _ hab => h.antisymm hab.ge hab.le,
    fun hu => isAntisymmetric_iff.2 fun _ _ h₁ h₂ => hu (le_antisymm h₂ h₁)⟩

/-- Every complete preference on a finite type is represented by a real-valued utility. -/
theorem CompletePreference.exists_isRepresentedBy_real [Finite X] (S : CompletePreference X) :
    ∃ u : X → ℝ, S.IsRepresentedBy u :=
  let ⟨u, hu⟩ := S.exists_isRepresentedBy_nat
  ⟨Nat.cast ∘ u, hu.comp_strictMono Nat.strictMono_cast⟩

/-- Every preference relation on a finite type is represented by a function into `ℕ`. -/
theorem exists_nat_represents_of_finite [Finite X] (hR : IsPreferenceRelation R) :
    ∃ u : X → ℕ, Represents u R :=
  let ⟨u, hu⟩ := (CompletePreference.ofGE R hR).exists_isRepresentedBy_nat
  ⟨u, Preference.represents_ge_iff.2 hu⟩

/-- **Proposition 1.1**: a preference relation on a finite type has a utility `X → ℝ`. -/
theorem exists_represents_of_finite [Finite X] (hR : IsPreferenceRelation R) :
    ∃ u : X → ℝ, Represents u R :=
  let ⟨u, hu⟩ := (CompletePreference.ofGE R hR).exists_isRepresentedBy_real
  ⟨u, Preference.represents_ge_iff.2 hu⟩

end MathEconLib.Preferences

end
