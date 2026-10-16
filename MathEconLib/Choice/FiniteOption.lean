/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image

/-!
# Best choice from a finite menu with an outside option

`optionMenu A` adds `none` to the alternatives in `A`, and `bestOption pref A`
computes its maximum under the supplied preference order. Only the menu is
finite: the population of alternatives need not be finite or enumerable.

This is the common finite selector for the executable classical algorithms.
Its agreement with preference-induced set choice is stated in `Choice.Induced`.
-/

namespace MathEconLib.Choice

universe u

namespace ChoiceFunction

variable {α : Type u} [DecidableEq α]

/-- A finite menu of alternatives, together with the outside option. -/
def optionMenu (A : Finset α) : Finset (Option α) :=
  insert none (A.image some)

@[simp] theorem mem_optionMenu {A : Finset α} {o : Option α} :
    o ∈ optionMenu A ↔ o = none ∨ ∃ x ∈ A, some x = o := by
  simp [optionMenu]

@[simp] theorem none_mem_optionMenu (A : Finset α) :
    none ∈ optionMenu A := by
  simp [optionMenu]

@[simp] theorem some_mem_optionMenu {A : Finset α} {x : α} :
    some x ∈ optionMenu A ↔ x ∈ A := by
  simp [optionMenu]

theorem optionMenu_nonempty (A : Finset α) :
    (optionMenu A).Nonempty :=
  ⟨none, none_mem_optionMenu A⟩

theorem optionMenu_mono {A B : Finset α} (hAB : A ⊆ B) :
    optionMenu A ⊆ optionMenu B := by
  intro o ho
  rcases mem_optionMenu.mp ho with rfl | ⟨x, hx, rfl⟩
  · exact none_mem_optionMenu B
  · exact some_mem_optionMenu.mpr (hAB hx)

/-- The best available alternative or outside option, computed from the menu. -/
def bestOption (pref : LinearOrder (Option α)) (A : Finset α) : Option α := by
  letI := pref
  exact (optionMenu A).max' (optionMenu_nonempty A)

theorem bestOption_mem (pref : LinearOrder (Option α)) (A : Finset α) :
    bestOption pref A ∈ optionMenu A := by
  letI := pref
  exact Finset.max'_mem _ _

theorem le_bestOption (pref : LinearOrder (Option α)) (A : Finset α)
    {o : Option α} (ho : o ∈ optionMenu A) :
    pref.le o (bestOption pref A) := by
  letI := pref
  exact Finset.le_max' _ _ ho

theorem bestOption_eq_iff (pref : LinearOrder (Option α)) (A : Finset α)
    (o : Option α) :
    bestOption pref A = o ↔
      o ∈ optionMenu A ∧ ∀ p ∈ optionMenu A, pref.le p o := by
  letI := pref
  exact Finset.max'_eq_iff _ _ _

/-- The finite selector attains the greatest element under the supplied order. -/
theorem isGreatest_bestOption (pref : LinearOrder (Option α)) (A : Finset α) :
    letI := pref
    IsGreatest (↑(optionMenu A) : Set (Option α)) (bestOption pref A) := by
  letI := pref
  exact ⟨bestOption_mem pref A, fun _ ho => le_bestOption pref A ho⟩

theorem bestOption_mono (pref : LinearOrder (Option α))
    {A B : Finset α} (hAB : A ⊆ B) :
    pref.le (bestOption pref A) (bestOption pref B) :=
  le_bestOption pref B (optionMenu_mono hAB (bestOption_mem pref A))

/-- An alternative is selected precisely when it is acceptable and maximal. -/
theorem bestOption_eq_some_iff (pref : LinearOrder (Option α))
    (A : Finset α) {x : α} :
    bestOption pref A = some x ↔
      x ∈ A ∧ pref.le none (some x) ∧
        ∀ y ∈ A, pref.le (some y) (some x) := by
  rw [bestOption_eq_iff, some_mem_optionMenu]
  constructor
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, hmax none (none_mem_optionMenu A),
      fun y hy => hmax (some y) (some_mem_optionMenu.mpr hy)⟩
  · rintro ⟨hx, hnone, hmax⟩
    refine ⟨hx, ?_⟩
    intro o ho
    cases o with
    | none => exact hnone
    | some y => exact hmax y (some_mem_optionMenu.mp ho)

end ChoiceFunction

end MathEconLib.Choice
