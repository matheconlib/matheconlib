/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Choice.PathIndependentMinorant
public import MathEconLib.Choice.Matching.SubstituteEnvelope

/-!
# The path-independent envelope

The greatest path-independent minorant of the substitute envelope is the
canonical candidate for a completion satisfying both substitutability and IRC.
For an IRC original rule it is a completion exactly when such a completion exists,
and is then the greatest one. The construction does not assert that bare
substitutable completability implies consistent substitutable completability.
All results apply to arbitrary contract types.
-/

@[expose] public section

namespace MathEconLib.Choice.ChoiceFunction

variable {X A : Type*} {counterparty : X → A} {C D : ChoiceFunction X}

/-- The greatest path-independent rule below the substitute envelope. -/
def pathIndependentEnvelope (counterparty : X → A) (C : ChoiceFunction X) :
    ChoiceFunction X := (substituteEnvelope counterparty C).pathIndependentMinorant

theorem pathIndependentEnvelope_pathIndependent (counterparty : X → A)
    (C : ChoiceFunction X) : (pathIndependentEnvelope counterparty C).PathIndependent :=
  pathIndependentMinorant_pathIndependent _

theorem pathIndependentEnvelope_le_substituteEnvelope (counterparty : X → A)
    (C : ChoiceFunction X) :
    pathIndependentEnvelope counterparty C ≤ substituteEnvelope counterparty C :=
  pathIndependentMinorant_le _

/-- Every substitutable IRC completion lies below the path-independent envelope. -/
theorem IsCompletionOf.le_pathIndependentEnvelope
    (hcomp : C.IsCompletionOf counterparty D)
    (hsub : D.Substitutable) (hIRC : D.Consistent) :
    D ≤ pathIndependentEnvelope counterparty C :=
  le_pathIndependentMinorant (hsub.pathIndependent hIRC)
    (hcomp.le_substituteEnvelope hsub)

/-- If a substitutable IRC completion exists, the path-independent envelope is one. -/
theorem pathIndependentEnvelope_isCompletionOf
    (hIRC : C.Consistent) (hC : C.HasConsistentSubstitutableCompletion counterparty) :
    C.IsCompletionOf counterparty (pathIndependentEnvelope counterparty C) := by
  classical
  obtain ⟨D, hcomp, hsub, hcons⟩ := hC
  have hDP := hcomp.le_pathIndependentEnvelope hsub hcons
  have hPU := pathIndependentEnvelope_le_substituteEnvelope counterparty C
  intro Y
  by_cases hfeas : Set.InjOn counterparty (pathIndependentEnvelope counterparty C Y)
  · left
    have hDfeas : Set.InjOn counterparty (D Y) :=
      fun _ hx _ hy heq => hfeas (hDP Y hx) (hDP Y hy) heq
    have hDC := hcomp.eq_of_injOn hDfeas
    have hCP : C Y ⊆ pathIndependentEnvelope counterparty C Y := by
      rw [← hDC]
      exact hDP Y
    have heq : C (pathIndependentEnvelope counterparty C Y) = C Y :=
      hIRC hCP ((pathIndependentEnvelope counterparty C).choose_subset Y)
    apply Set.Subset.antisymm _ hCP
    intro x hx
    have h := (hPU Y hx).2 (pathIndependentEnvelope counterparty C Y)
      ((pathIndependentEnvelope counterparty C).choose_subset Y) hfeas hx
    rwa [heq] at h
  · right
    simp only [Set.InjOn] at hfeas
    push Not at hfeas
    obtain ⟨x, hx, y, hy, heq, hne⟩ := hfeas
    exact ⟨x, hx, y, hy, hne, heq⟩

/-- The canonical candidate exactly tests consistent substitutable completability. -/
theorem hasConsistentSubstitutableCompletion_iff_pathIndependentEnvelope_isCompletionOf
    (hIRC : C.Consistent) :
    C.HasConsistentSubstitutableCompletion counterparty ↔
      C.IsCompletionOf counterparty (pathIndependentEnvelope counterparty C) := by
  constructor
  · exact pathIndependentEnvelope_isCompletionOf hIRC
  · intro hcomp
    have hpi := pathIndependentEnvelope_pathIndependent counterparty C
    exact ⟨_, hcomp, hpi.substitutable, hpi.consistent⟩

/-- When consistent substitutable completions exist, the envelope is their greatest member. -/
theorem isGreatest_pathIndependentEnvelope (hIRC : C.Consistent)
    (hC : C.HasConsistentSubstitutableCompletion counterparty) :
    IsGreatest {D : ChoiceFunction X |
      C.IsCompletionOf counterparty D ∧ D.Substitutable ∧ D.Consistent}
      (pathIndependentEnvelope counterparty C) := by
  have hpi := pathIndependentEnvelope_pathIndependent counterparty C
  exact ⟨⟨pathIndependentEnvelope_isCompletionOf hIRC hC, hpi.substitutable, hpi.consistent⟩,
    fun _ h => h.1.le_pathIndependentEnvelope h.2.1 h.2.2⟩

/-- The path-independent sandwich describes exactly the enlarging IRC completions.
Feasibility and finite-valuedness of the original rule are not needed. -/
theorem enlarging_pathIndependent_completion_iff_sandwich (hIRC : C.Consistent) :
    (C.IsCompletionOf counterparty D ∧ D.PathIndependent ∧ C ≤ D) ↔
      (D.PathIndependent ∧ C.substituteHull ≤ D ∧
        D ≤ pathIndependentEnvelope counterparty C) := by
  constructor
  · rintro ⟨hcomp, hpi, hCD⟩
    exact ⟨hpi, substituteHull_le hpi.substitutable hCD,
      hcomp.le_pathIndependentEnvelope hpi.substitutable hpi.consistent⟩
  · rintro ⟨hpi, hHD, hDP⟩
    have hCD := (le_substituteHull C).trans hHD
    exact ⟨isCompletionOf_of_le_of_le_substituteEnvelope hIRC hCD
      (hDP.trans (pathIndependentEnvelope_le_substituteEnvelope counterparty C)), hpi, hCD⟩

end MathEconLib.Choice.ChoiceFunction
