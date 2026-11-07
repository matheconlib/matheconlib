/-
Copyright (c) 2026 Scott Duke Kominers and Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers, Bo Cowgill
-/
module

public import MathEconLib.Choice.PathIndependentMinorant
public import MathEconLib.Choice.Matching.SubstituteEnvelope

/-!
# The path-independent envelope

The greatest path-independent minorant of the substitute envelope is the
canonical candidate for a completion satisfying both substitutability and IRC.
It is a completion exactly when such a completion exists, and is then the greatest such
completion under pointwise inclusion of chosen contracts. The original rule need not satisfy IRC.
The construction does not assert that bare substitutable completability implies consistent
substitutable completability.
All results apply to arbitrary contract types.

The completion-preservation results in this module were developed for an in-preparation writeup
on substitute completions and stable outcomes.
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

/-- If `K` lies below the substitute envelope and above a path-independent completion `D` of `C`,
its greatest path-independent minorant completes `C`. The IRC condition is satisfied by the
witnessing completion `D`. -/
theorem pathIndependentMinorant_isCompletionOf_of_le_substituteEnvelope {K : ChoiceFunction X}
    (hKU : K ≤ substituteEnvelope counterparty C) (hcomp : C.IsCompletionOf counterparty D)
    (hD : D.PathIndependent) (hDK : D ≤ K) :
    C.IsCompletionOf counterparty K.pathIndependentMinorant := by
  classical
  let P := K.pathIndependentMinorant
  have hDP : D ≤ P := le_pathIndependentMinorant hD hDK
  have hPU : P ≤ substituteEnvelope counterparty C :=
    (pathIndependentMinorant_le K).trans hKU
  intro Y
  by_cases hfeas : Set.InjOn counterparty (P Y)
  · left
    have hDY : D Y = C Y := hcomp.eq_of_injOn (hfeas.mono (hDP Y))
    have hDF : D (P Y) = D Y := hD.consistent (hDP Y) (P.choose_subset Y)
    have hCF : C (P Y) = C Y := (hcomp.eq_of_injOn_menu hfeas).symm.trans (hDF.trans hDY)
    apply Set.Subset.antisymm _ (hDY ▸ hDP Y)
    intro x hx
    have hxC := (hPU Y hx).2 (P Y) (P.choose_subset Y) hfeas hx
    rwa [hCF] at hxC
  · right
    simp only [Set.InjOn] at hfeas
    push Not at hfeas
    obtain ⟨x, hx, y, hy, heq, hne⟩ := hfeas
    exact ⟨x, hx, y, hy, hne, heq⟩

/-- If `C` admits a substitutable completion satisfying IRC, its path-independent envelope
is a completion of `C`. -/
theorem pathIndependentEnvelope_isCompletionOf_of_hasConsistentSubstitutableCompletion
    (hC : C.HasConsistentSubstitutableCompletion counterparty) :
    C.IsCompletionOf counterparty (pathIndependentEnvelope counterparty C) := by
  obtain ⟨D, hcomp, hsub, hcons⟩ := hC
  exact pathIndependentMinorant_isCompletionOf_of_le_substituteEnvelope le_rfl hcomp
    (hsub.pathIndependent hcons) (hcomp.le_substituteEnvelope hsub)

/-- The canonical candidate exactly tests consistent substitutable completability. -/
theorem hasConsistentSubstitutableCompletion_iff_pathIndependentEnvelope_isCompletionOf :
    C.HasConsistentSubstitutableCompletion counterparty ↔
      C.IsCompletionOf counterparty (pathIndependentEnvelope counterparty C) := by
  constructor
  · exact pathIndependentEnvelope_isCompletionOf_of_hasConsistentSubstitutableCompletion
  · intro hcomp
    have hpi := pathIndependentEnvelope_pathIndependent counterparty C
    exact ⟨_, hcomp, hpi.substitutable, hpi.consistent⟩

/-- When consistent substitutable completions exist, the envelope is their greatest member. -/
theorem isGreatest_pathIndependentEnvelope
    (hC : C.HasConsistentSubstitutableCompletion counterparty) :
    IsGreatest {D : ChoiceFunction X |
      C.IsCompletionOf counterparty D ∧ D.Substitutable ∧ D.Consistent}
      (pathIndependentEnvelope counterparty C) := by
  have hpi := pathIndependentEnvelope_pathIndependent counterparty C
  exact ⟨⟨pathIndependentEnvelope_isCompletionOf_of_hasConsistentSubstitutableCompletion hC,
    hpi.substitutable, hpi.consistent⟩,
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
