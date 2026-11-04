/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Preference.Defs
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Preference relations: basic API

How completeness, transitivity and antisymmetry interact with the strict part `StrictPart R` and
indifference `Indiff R`, and the bridges to Mathlib's order classes.

## Main statements

* `IsComplete.isReflexive`: a complete relation is reflexive.
* `IsTransitive.strictPart`, `IsTransitive.indiff`: the strict part and indifference of a
  transitive relation are transitive.
* `IsTransitive.strictPart_of_rel_of_strictPart`, `IsTransitive.strictPart_of_strictPart_of_rel`:
  `x ≿ y ≻ z` and `x ≻ y ≿ z` give `x ≻ z`.
* `equivalence_indiff`: indifference of a reflexive and transitive relation is an equivalence.
* `IsComplete.not_rel_iff`: for a complete relation, `¬ y ≿ x ↔ x ≻ y`.
* `IsComplete.rel_iff_eq_or_strictPart`: for a complete antisymmetric relation,
  `x ≿ y ↔ x = y ∨ x ≻ y`.
* `isPreferenceRelation_iff_isPreorder_and_total`, `isLinearPreference_iff_isLinearOrder`: the
  bridges to Mathlib's `IsPreorder`, `Std.Total` and `IsLinearOrder`.
* `exists_isLinearPreference_strictPart`: for distinct `x` and `y` there is a linear preference
  with `x ≻ y`.

## Implementation notes

Each lemma assumes only the properties its proof uses. Osborne and Rubinstein state these facts for
preference relations; most need transitivity alone.

## References

Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, expanded second
edition, Open Book Publishers, Section 1.1.
[DOI: 10.11647/OBP.0361](https://doi.org/10.11647/OBP.0361).

## Tags

preference relation, strict preference, indifference, total preorder
-/

@[expose] public section

namespace MathEconLib.Preference

universe u

variable {X : Type u} {R : X → X → Prop} {x y z : X}

/-! ### Completeness and reflexivity -/

/-- A complete relation is reflexive (Mathlib's `Std.Total.to_refl`). -/
theorem IsComplete.isReflexive (h : IsComplete R) : IsReflexive R :=
  have := h.toTotal
  isReflexive_of_refl

theorem IsComplete.rel_refl (h : IsComplete R) (x : X) : R x x := h.isReflexive.refl x

theorem IsPreferenceRelation.refl (h : IsPreferenceRelation R) (x : X) : R x x :=
  h.isComplete.rel_refl x

theorem IsPreferenceRelation.isReflexive (h : IsPreferenceRelation R) : IsReflexive R :=
  h.isComplete.isReflexive

/-! ### The strict part -/

theorem StrictPart.asymm (h : StrictPart R x y) : ¬ StrictPart R y x := fun h' => h.2 h'.1

theorem StrictPart.ne (h : StrictPart R x y) : x ≠ y := by
  rintro rfl
  exact strictPart_irrefl R x h

/-- The strict part of a relation is asymmetric (Mathlib's `Std.Asymm`). -/
instance : Std.Asymm (StrictPart R) := ⟨fun _ _ h => h.asymm⟩

/-- The strict part of `≤` is `<`. -/
@[simp] theorem strictPart_le {α : Type*} [Preorder α] : StrictPart (X := α) (· ≤ ·) = (· < ·) :=
  funext₂ fun _ _ => propext lt_iff_le_not_ge.symm

/-- The strict part of `≥` is `>`. -/
@[simp] theorem strictPart_ge {α : Type*} [Preorder α] :
    StrictPart (fun x y : α => y ≤ x) = (fun x y => y < x) :=
  funext₂ fun _ _ => propext lt_iff_le_not_ge.symm

/-! ### Transitivity -/

/-- The strict part of a transitive relation is transitive. -/
theorem IsTransitive.strictPart (h : IsTransitive R) : IsTransitive (StrictPart R) :=
  isTransitive_iff.2 fun _ _ _ hxy hyz =>
    ⟨h.trans hxy.1 hyz.1, fun hzx => hxy.2 (h.trans hyz.1 hzx)⟩

/-- Indifference derived from a transitive relation is transitive (Mathlib's
`AntisymmRel.trans`). -/
theorem IsTransitive.indiff (h : IsTransitive R) : IsTransitive (Indiff R) :=
  have := h.toIsTrans
  isTransitive_of_isTrans

/-- For a transitive relation, `x ≿ y` and `y ≻ z` give `x ≻ z`. -/
theorem IsTransitive.strictPart_of_rel_of_strictPart (h : IsTransitive R) (hxy : R x y)
    (hyz : StrictPart R y z) : StrictPart R x z :=
  ⟨h.trans hxy hyz.1, fun hzx => hyz.2 (h.trans hzx hxy)⟩

/-- For a transitive relation, `x ≻ y` and `y ≿ z` give `x ≻ z`. -/
theorem IsTransitive.strictPart_of_strictPart_of_rel (h : IsTransitive R)
    (hxy : StrictPart R x y) (hyz : R y z) : StrictPart R x z :=
  ⟨h.trans hxy.1 hyz, fun hzx => hxy.2 (h.trans hyz hzx)⟩

/-- Indifference derived from a reflexive and transitive relation is an equivalence relation
(Mathlib's `AntisymmRel.setoid`). -/
theorem equivalence_indiff (hr : IsReflexive R) (ht : IsTransitive R) :
    Equivalence (Indiff R) :=
  have : IsPreorder X R := { toRefl := hr, toIsTrans := ht }
  (AntisymmRel.setoid X R).iseqv

/-- Indifference derived from a preference relation is an equivalence relation. -/
theorem IsPreferenceRelation.equivalence_indiff (h : IsPreferenceRelation R) :
    Equivalence (Indiff R) :=
  MathEconLib.Preference.equivalence_indiff h.isReflexive h.isTransitive

/-! ### Completeness and the strict part -/

theorem IsComplete.not_rel_iff (h : IsComplete R) : ¬ R y x ↔ StrictPart R x y :=
  ⟨fun hn => ⟨(h.total x y).resolve_right hn, hn⟩, fun hs => hs.2⟩

theorem IsComplete.strictPart_or_rel (h : IsComplete R) (x y : X) : StrictPart R x y ∨ R y x := by
  by_cases hyx : R y x
  · exact Or.inr hyx
  · exact Or.inl (h.not_rel_iff.1 hyx)

theorem IsComplete.rel_iff_not_strictPart (h : IsComplete R) : R x y ↔ ¬ StrictPart R y x := by
  rw [← h.not_rel_iff, not_not]

/-- For a complete relation, at least one of `x ≻ y`, `x ∼ y`, `y ≻ x` holds. -/
theorem IsComplete.strictPart_or_indiff_or_strictPart (h : IsComplete R) (x y : X) :
    StrictPart R x y ∨ Indiff R x y ∨ StrictPart R y x := by
  by_cases hxy : R x y <;> by_cases hyx : R y x
  · exact Or.inr (Or.inl ⟨hxy, hyx⟩)
  · exact Or.inl ⟨hxy, hyx⟩
  · exact Or.inr (Or.inr ⟨hyx, hxy⟩)
  · exact ((h.total x y).elim hxy hyx).elim

/-! ### Antisymmetry -/

theorem IsAntisymmetric.eq_of_indiff (h : IsAntisymmetric R) (hxy : Indiff R x y) : x = y :=
  h.antisymm hxy.1 hxy.2

/-- For a reflexive antisymmetric relation, indifference is equality (Mathlib's
`antisymmRel_iff_eq`). -/
theorem IsAntisymmetric.indiff_iff_eq (h : IsAntisymmetric R) (hr : IsReflexive R) :
    Indiff R x y ↔ x = y :=
  have : Std.Antisymm R := h
  have : Std.Refl R := hr
  antisymmRel_iff_eq

/-- For a complete antisymmetric relation, distinct alternatives are strictly ranked. -/
theorem IsComplete.strictPart_or_strictPart (hC : IsComplete R) (hA : IsAntisymmetric R)
    (hxy : x ≠ y) : StrictPart R x y ∨ StrictPart R y x := by
  rcases hC.total x y with h | h
  · exact Or.inl ⟨h, fun h' => hxy (hA.antisymm h h')⟩
  · exact Or.inr ⟨h, fun h' => hxy (hA.antisymm h' h)⟩

/-- For a complete antisymmetric relation, `x ≿ y` if and only if `x = y` or `x ≻ y`. -/
theorem IsComplete.rel_iff_eq_or_strictPart (hC : IsComplete R) (hA : IsAntisymmetric R) :
    R x y ↔ x = y ∨ StrictPart R x y := by
  constructor
  · intro h
    by_cases h' : R y x
    · exact Or.inl (hA.antisymm h h')
    · exact Or.inr ⟨h, h'⟩
  · rintro (rfl | h)
    · exact hC.rel_refl x
    · exact h.1

/-- Osborne and Rubinstein's antisymmetry (Definition 1.4): `x ≠ y` and `x ≿ y` exclude
`y ≿ x`. -/
theorem isAntisymmetric_iff_not_rel_of_ne :
    IsAntisymmetric R ↔ ∀ x y, x ≠ y → R x y → ¬ R y x :=
  ⟨fun h x y hne hxy hyx => hne (h.antisymm hxy hyx),
    fun h => isAntisymmetric_iff.2 fun x y hxy hyx => by
      by_contra hne
      exact h x y hne hxy hyx⟩

/-! ### Bridges to Mathlib's order classes -/

theorem IsPreferenceRelation.isPreorder (h : IsPreferenceRelation R) : IsPreorder X R :=
  { toRefl := h.isReflexive, toIsTrans := h.isTransitive }

/-- A preference relation is a total preorder in Mathlib's unbundled sense. -/
theorem isPreferenceRelation_iff_isPreorder_and_total :
    IsPreferenceRelation R ↔ IsPreorder X R ∧ Std.Total R :=
  ⟨fun h => ⟨h.isPreorder, h.isComplete⟩, fun ⟨hp, ht⟩ => ⟨ht, hp.toIsTrans⟩⟩

theorem IsLinearPreference.isLinearOrder (h : IsLinearPreference R) : IsLinearOrder X R :=
  { toIsPreorder := h.isPreferenceRelation.isPreorder, toAntisymm := h.isAntisymmetric,
    toTotal := h.isPreferenceRelation.isComplete }

/-- A linear preference is a linear order in Mathlib's unbundled sense. -/
theorem isLinearPreference_iff_isLinearOrder : IsLinearPreference R ↔ IsLinearOrder X R :=
  ⟨IsLinearPreference.isLinearOrder, fun h => ⟨⟨h.toTotal, h.toIsTrans⟩, h.toAntisymm⟩⟩

/-- `≥` on a linear order is a linear preference. -/
@[simp] theorem isLinearPreference_ge {α : Type*} [LinearOrder α] :
    IsLinearPreference (fun x y : α => y ≤ x) :=
  ⟨isPreferenceRelation_ge, isAntisymmetric_iff.2 fun _ _ hxy hyx => le_antisymm hyx hxy⟩

/-! ### Existence of linear preferences -/

/-- For any two distinct alternatives `x` and `y` of any type there is a linear preference that
ranks `x` above `y`. -/
theorem exists_isLinearPreference_strictPart (hxy : x ≠ y) :
    ∃ R : X → X → Prop, IsLinearPreference R ∧ StrictPart R x y := by
  classical
  let : LinearOrder X := linearOrderOfSTO WellOrderingRel
  let u : X → Bool ×ₗ X := fun z => toLex (decide (z = x), z)
  have hu : Function.Injective u := fun a b h => congrArg Prod.snd (toLex.injective h)
  refine ⟨fun a b => u b ≤ u a, ⟨⟨isComplete_iff.2 fun a b => le_total _ _,
    isTransitive_iff.2 fun _ _ _ h₁ h₂ => le_trans h₂ h₁⟩,
    isAntisymmetric_iff.2 fun _ _ h₁ h₂ => hu (le_antisymm h₂ h₁)⟩, ?_⟩
  change u y ≤ u x ∧ ¬ u x ≤ u y
  rw [← lt_iff_le_not_ge]
  simp [u, Prod.Lex.toLex_lt_toLex, hxy.symm]

end MathEconLib.Preference

/-! ### Worked examples -/

section Examples

open MathEconLib.Preference

/-- The cyclic relation `0 ≿ 1 ≿ 2 ≿ 0` (each alternative also related to itself) on `Fin 3` is
complete but not transitive. -/
example : IsComplete (fun x y : Fin 3 => x = y ∨ y = x + 1) ∧
    ¬ IsTransitive (fun x y : Fin 3 => x = y ∨ y = x + 1) := by
  refine ⟨isComplete_iff.2 (by decide), fun h => ?_⟩
  have := h.trans (x := 0) (y := 1) (z := 2) (by decide) (by decide)
  revert this; decide

/-- `IsComplete.rel_iff_eq_or_strictPart` needs antisymmetry: universal indifference on `Bool`
has `true ≿ false` but neither `true = false` nor `true ≻ false`. -/
example : (fun _ _ : Bool => True) true false ∧
    ¬ (true = false ∨ StrictPart (fun _ _ : Bool => True) true false) := by
  simp [StrictPart]

example : ∃ R : ℕ → ℕ → Prop, IsLinearPreference R ∧ StrictPart R 3 0 :=
  exists_isLinearPreference_strictPart (by decide)

end Examples
