/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Card

/-!
# Choice functions

A choice function on a type `α` selects a subset of each available set of
alternatives. This definition does not require a matching market, preferences,
or any additional conditions on how choices change with the menu.

The current development is motivated by matching with contracts, but the
choice-function structure and its elementary operations apply to general
choice theory. Optional conditions such as consistency, substitutability,
and path independence are defined in
`MathEconLib.Choice.Conditions`.

## Main definitions

* `ChoiceFunction α` — a map `Set α → Set α` choosing a subset of its input.
* `ChoiceFunction.rejected` — available but unchosen alternatives.
* The pointwise order on choice functions — inclusion of choices at every menu.

## References

Hatfield–Kominers, *The theory of matching with contracts*, Chapter 5,
Handbook of the Economics of Matching 2 (2025), 409–487,
DOI 10.1016/bs.hesmat.2025.10.005, §2.1.1, p. 412. The chapter studies finite
contract sets; the definition here allows arbitrary types of alternatives.
-/

namespace MathEconLib.Choice

universe u

variable {α : Type u}

/-- A choice function on `α`: from any available set of alternatives it
selects a subset. -/
structure ChoiceFunction (α : Type u) where
  /-- The underlying selection map. -/
  toFun : Set α → Set α
  /-- Only available alternatives are chosen. -/
  choose_subset : ∀ Y, toFun Y ⊆ Y

namespace ChoiceFunction

instance : FunLike (ChoiceFunction α) (Set α) (Set α) where
  coe := toFun
  coe_injective := by
    rintro ⟨f, _⟩ ⟨g, _⟩ h
    simpa using h

@[ext]
lemma ext {C D : ChoiceFunction α} (h : ∀ Y, C Y = D Y) : C = D :=
  DFunLike.ext _ _ h

/-- Choice functions are ordered by pointwise inclusion of their choices.
Thus `C ≤ D` means that `D` enlarges `C` at every menu. -/
instance : PartialOrder (ChoiceFunction α) where
  le C D := ∀ Y, C Y ⊆ D Y
  le_refl C Y := Set.Subset.rfl
  le_trans C D E hCD hDE Y x hx := hDE Y (hCD Y hx)
  le_antisymm C D hCD hDC :=
    ext (fun Y => Set.Subset.antisymm (hCD Y) (hDC Y))

theorem le_def {C D : ChoiceFunction α} :
    C ≤ D ↔ ∀ Y, C Y ⊆ D Y :=
  Iff.rfl

variable (C : ChoiceFunction α)

/-- The rejection function: available but not chosen. -/
def rejected : Set α → Set α := fun Y => Y \ C Y

@[simp]
lemma mem_rejected {Y : Set α} {x : α} :
    x ∈ C.rejected Y ↔ x ∈ Y ∧ x ∉ C Y :=
  Iff.rfl

lemma choose_union_rejected (Y : Set α) : C Y ∪ C.rejected Y = Y :=
  Set.union_diff_cancel (C.choose_subset Y)

end ChoiceFunction

end MathEconLib.Choice
