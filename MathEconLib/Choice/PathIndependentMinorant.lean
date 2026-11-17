/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Choice.Conditions

/-!
# The greatest path-independent minorant

Take the pointwise union of all path-independent choice functions below a supplied
choice function. Substitutability and consistency are preserved by this union,
so it is the greatest path-independent minorant on arbitrary alternative types.
This is the standard greatest-minorant construction, not a new completion notion.
It requires no counterparty map or finite-domain assumption.
-/

@[expose] public section

namespace MathEconLib.Choice.ChoiceFunction

variable {X : Type*} {C D : ChoiceFunction X}

/-- The pointwise union of all path-independent rules below `C`. -/
def pathIndependentMinorant (C : ChoiceFunction X) : ChoiceFunction X where
  toFun Y := {x | ∃ D : ChoiceFunction X, D.PathIndependent ∧ D ≤ C ∧ x ∈ D Y}
  choose_subset := fun Y _ ⟨D, _, _, hx⟩ => D.choose_subset Y hx

@[simp] theorem mem_pathIndependentMinorant {Y : Set X} {x : X} :
    x ∈ C.pathIndependentMinorant Y ↔
      ∃ D : ChoiceFunction X, D.PathIndependent ∧ D ≤ C ∧ x ∈ D Y := Iff.rfl

/-- The union remains below its defining upper bound. -/
theorem pathIndependentMinorant_le (C : ChoiceFunction X) :
    C.pathIndependentMinorant ≤ C :=
  fun Y _ ⟨_, _, hDC, hx⟩ => hDC Y hx

/-- Every path-independent minorant is contained in the canonical one. -/
theorem le_pathIndependentMinorant (hD : D.PathIndependent) (hDC : D ≤ C) :
    D ≤ C.pathIndependentMinorant :=
  fun _ _ hx => ⟨D, hD, hDC, hx⟩

/-- Substitutability passes to the pointwise union. -/
theorem pathIndependentMinorant_substitutable (C : ChoiceFunction X) :
    C.pathIndependentMinorant.Substitutable := by
  apply substitutable_iff_chernoff.mpr
  intro V Y hV x hx
  obtain ⟨D, hD, hDC, hxD⟩ := hx.1
  exact ⟨D, hD, hDC, hD.substitutable.mem_of_subset hV hxD hx.2⟩

/-- Consistency passes to this union because retaining its choices retains
every constituent's choices. -/
theorem pathIndependentMinorant_consistent (C : ChoiceFunction X) :
    C.pathIndependentMinorant.Consistent := by
  intro Y V hCV hVY
  have heq : ∀ D : ChoiceFunction X, D.PathIndependent → D ≤ C → D V = D Y := by
    intro D hD hDC
    exact hD.consistent (fun _ hx => hCV ⟨D, hD, hDC, hx⟩) hVY
  ext x
  constructor
  · rintro ⟨D, hD, hDC, hx⟩
    exact ⟨D, hD, hDC, (heq D hD hDC) ▸ hx⟩
  · rintro ⟨D, hD, hDC, hx⟩
    exact ⟨D, hD, hDC, (heq D hD hDC).symm ▸ hx⟩

/-- The canonical minorant is path independent, without finiteness. -/
theorem pathIndependentMinorant_pathIndependent (C : ChoiceFunction X) :
    C.pathIndependentMinorant.PathIndependent :=
  (pathIndependentMinorant_substitutable C).pathIndependent
    (pathIndependentMinorant_consistent C)

/-- The construction is the greatest path-independent rule below `C`. -/
theorem isGreatest_pathIndependentMinorant (C : ChoiceFunction X) :
    IsGreatest {D : ChoiceFunction X | D.PathIndependent ∧ D ≤ C}
      C.pathIndependentMinorant :=
  ⟨⟨pathIndependentMinorant_pathIndependent C, pathIndependentMinorant_le C⟩,
    fun _ h => le_pathIndependentMinorant h.1 h.2⟩

/-- Path-independent rules are fixed points of the construction. -/
theorem PathIndependent.pathIndependentMinorant_eq (hC : C.PathIndependent) :
    C.pathIndependentMinorant = C :=
  le_antisymm (pathIndependentMinorant_le C) (le_pathIndependentMinorant hC le_rfl)

/-- Enlarging the upper bound enlarges the greatest minorant. -/
theorem pathIndependentMinorant_mono :
    Monotone (pathIndependentMinorant : ChoiceFunction X → ChoiceFunction X) := by
  intro C D hCD
  exact le_pathIndependentMinorant (pathIndependentMinorant_pathIndependent C)
    ((pathIndependentMinorant_le C).trans hCD)

/-- Applying the minorant construction twice has no further effect. -/
theorem pathIndependentMinorant_idempotent (C : ChoiceFunction X) :
    C.pathIndependentMinorant.pathIndependentMinorant = C.pathIndependentMinorant :=
  (pathIndependentMinorant_pathIndependent C).pathIndependentMinorant_eq

end MathEconLib.Choice.ChoiceFunction
