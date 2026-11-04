/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Preference.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Linarith

/-!
# Utility representations

A function `u : X → α` *represents* a relation `R` on `X` if `x ≿ y` exactly when `u x ≥ u y`.

## Main statements

* `Represents.isPreferenceRelation`: a relation represented into a linear order is a preference.
* `Represents.comp_strictMono`, `Represents.affine`: representations survive increasing maps.
* `exists_represents_of_finite`: on a finite type every preference has a utility in `ℝ`.
* `isAntisymmetric_utilityRel_iff`: `UtilityRel u` is antisymmetric iff `u` is injective.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Sections 1.2 and 1.4
-/

@[expose] public section

namespace MathEconLib.Preference

universe u v w

variable {X : Type u} {α : Type v} {β : Type w} {R : X → X → Prop} {x y : X}

/-- The relation defined by `u`: `x ≿ y` if and only if `u x ≥ u y`. -/
def UtilityRel [LE α] (u : X → α) (x y : X) : Prop := u y ≤ u x

instance [LE α] [DecidableLE α] (u : X → α) : DecidableRel (UtilityRel u) :=
  fun x y => inferInstanceAs (Decidable (u y ≤ u x))

/-- `u` is a utility function for `R`: `x ≿ y` if and only if `u x ≥ u y`. -/
def Represents [LE α] (u : X → α) (R : X → X → Prop) : Prop := ∀ x y, R x y ↔ u y ≤ u x

@[simp]
theorem utilityRel_iff [LE α] (u : X → α) (x y : X) : UtilityRel u x y ↔ u y ≤ u x := Iff.rfl

theorem utilityRel_eq_preimage [LE α] (u : X → α) : UtilityRel u = u ⁻¹'o (· ≥ ·) := rfl

theorem represents_iff [LE α] {u : X → α} : Represents u R ↔ ∀ x y, R x y ↔ u y ≤ u x := Iff.rfl

theorem represents_iff_eq [LE α] {u : X → α} : Represents u R ↔ R = UtilityRel u :=
  ⟨fun h => funext₂ fun x y => propext (h x y), fun h => h ▸ fun _ _ => Iff.rfl⟩

@[simp]
theorem represents_utilityRel [LE α] (u : X → α) : Represents u (UtilityRel u) :=
  fun _ _ => Iff.rfl

theorem Represents.rel_iff [LE α] {u : X → α} (h : Represents u R) : R x y ↔ u y ≤ u x := h x y

theorem Represents.strictPart_iff [Preorder α] {u : X → α} (h : Represents u R) :
    StrictPart R x y ↔ u y < u x := by
  rw [MathEconLib.Preference.strictPart_iff, h x y, h y x, lt_iff_le_not_ge]

theorem Represents.indiff_iff [PartialOrder α] {u : X → α} (h : Represents u R) :
    Indiff R x y ↔ u x = u y := by
  rw [MathEconLib.Preference.indiff_iff, h x y, h y x]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

@[simp]
theorem strictPart_utilityRel_iff [Preorder α] (u : X → α) :
    StrictPart (UtilityRel u) x y ↔ u y < u x :=
  (represents_utilityRel u).strictPart_iff

@[simp]
theorem indiff_utilityRel_iff [PartialOrder α] (u : X → α) :
    Indiff (UtilityRel u) x y ↔ u x = u y :=
  (represents_utilityRel u).indiff_iff

theorem isTransitive_utilityRel [Preorder α] (u : X → α) : IsTransitive (UtilityRel u) :=
  isTransitive_iff.2 fun _ _ _ h₁ h₂ => le_trans h₂ h₁

theorem isComplete_utilityRel [LinearOrder α] (u : X → α) : IsComplete (UtilityRel u) :=
  isComplete_iff.2 fun _ _ => le_total _ _

/-- The relation defined by a value function into a linear order is a preference relation. -/
theorem isPreferenceRelation_utilityRel [LinearOrder α] (u : X → α) :
    IsPreferenceRelation (UtilityRel u) :=
  ⟨isComplete_utilityRel u, isTransitive_utilityRel u⟩

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

theorem isLinearPreference_utilityRel [LinearOrder α] {u : X → α} (hu : Function.Injective u) :
    IsLinearPreference (UtilityRel u) :=
  ⟨isPreferenceRelation_utilityRel u, isAntisymmetric_utilityRel_iff.2 hu⟩

/-- **Proposition 1.3**: if `u` represents `R` and `f` is strictly increasing, so does `f ∘ u`. -/
theorem Represents.comp_strictMono [LinearOrder α] [Preorder β] {u : X → α} {f : α → β}
    (hu : Represents u R) (hf : StrictMono f) : Represents (fun x => f (u x)) R :=
  fun x y => (hu x y).trans hf.le_iff_le.symm

theorem Represents.affine {u : X → ℝ} (hu : Represents u R) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Represents (fun x => a * u x + b) R :=
  hu.comp_strictMono (f := fun t => a * t + b) fun s t hst => by
    simp only; nlinarith

/-- Every preference relation on a finite type is represented by a function into `ℕ`. -/
theorem exists_nat_represents_of_finite [Finite X] (hR : IsPreferenceRelation R) :
    ∃ u : X → ℕ, Represents u R := by
  classical
  let := Fintype.ofFinite X
  refine ⟨fun x => (Finset.univ.filter fun z => R x z).card, fun x y => ?_⟩
  have hsub : ∀ {x y}, R x y →
      Finset.univ.filter (fun z => R y z) ⊆ Finset.univ.filter (fun z => R x z) := by
    intro x y hxy z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hR.trans hxy hz
  refine ⟨fun hxy => Finset.card_le_card (hsub hxy), fun hle => ?_⟩
  by_contra hxy
  have hyx : R y x := (hR.total x y).resolve_left hxy
  have hss : Finset.univ.filter (fun z => R x z) ⊂ Finset.univ.filter (fun z => R y z) :=
    (Finset.ssubset_iff_of_subset (hsub hyx)).2 ⟨y, by simp [hR.refl y], by simp [hxy]⟩
  exact absurd hle (not_le.2 (Finset.card_lt_card hss))

/-- **Proposition 1.1**: a preference relation on a finite type has a utility `X → ℝ`. -/
theorem exists_represents_of_finite [Finite X] (hR : IsPreferenceRelation R) :
    ∃ u : X → ℝ, Represents u R := by
  obtain ⟨u, hu⟩ := exists_nat_represents_of_finite hR
  exact ⟨fun x => (u x : ℝ), hu.comp_strictMono Nat.strictMono_cast⟩

end MathEconLib.Preference

section Examples

open MathEconLib.Preference

/-- Osborne and Rubinstein's Example 1.1: `a ≻ b ∼ c ≻ d`, with `u = (5, -1, -1, -17)`. -/
example : StrictPart (UtilityRel ![(5 : ℤ), -1, -1, -17]) 0 1 ∧
    Indiff (UtilityRel ![(5 : ℤ), -1, -1, -17]) 1 2 ∧
    StrictPart (UtilityRel ![(5 : ℤ), -1, -1, -17]) 2 3 := by
  decide

example {X : Type*} {R : X → X → Prop} {u : X → ℝ} (hu : Represents u R) :
    Represents (fun x => 3 * u x + (-7)) R :=
  hu.affine (by norm_num) (-7)

/-- A merely monotone transformation of a representation need not represent. -/
example : Represents (fun b : Bool => if b then (1 : ℕ) else 0)
      (UtilityRel fun b => if b then 1 else 0) ∧
    ¬ Represents (fun _ : Bool => (0 : ℕ)) (UtilityRel fun b : Bool => if b then (1 : ℕ) else 0) :=
  ⟨represents_utilityRel _, fun h => absurd ((h false true).2 le_rfl) (by decide)⟩

example : ∃ u : Fin 3 → ℝ, Represents u (fun x y => y ≤ x) :=
  exists_represents_of_finite isPreferenceRelation_ge

end Examples
