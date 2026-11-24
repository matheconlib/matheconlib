/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Choice.Matching.Relationships

/-!
# The substitute envelope

The envelope excludes contracts rejected on any feasible sub-menu. It is
substitutable and bounds every substitutable completion from above. For an
IRC original rule it is a completion if and only if a substitutable completion
exists; in that case it is the greatest one. No finiteness assumption is needed.

For feasible, finite-valued IRC choice, unilateral substitutability is equivalent
to the original rule lying below the envelope. The hull and envelope bound
exactly the enlarging substitutable completions, not all completions.

These results follow the completion conventions in `Matching.Completion`.
The envelope is not asserted to satisfy IRC or the law of aggregate demand.
See `docs/SubstitutableCompletionFollowup.md` for proofs, scope, and the
separate path-independent and aggregate-demand developments.
-/

@[expose] public section

namespace MathEconLib.Choice.ChoiceFunction

variable {X A : Type*} {counterparty : X → A} {C D : ChoiceFunction X}

/-- Retain a contract only if no feasible sub-menu rejects it. -/
def substituteEnvelope (counterparty : X → A) (C : ChoiceFunction X) :
    ChoiceFunction X where
  toFun Y := {x | x ∈ Y ∧ ∀ V, V ⊆ Y → Set.InjOn counterparty V →
    x ∈ V → x ∈ C V}
  choose_subset := fun _ _ hx => hx.1

@[simp] theorem mem_substituteEnvelope {Y : Set X} {x : X} :
    x ∈ substituteEnvelope counterparty C Y ↔
      x ∈ Y ∧ ∀ V, V ⊆ Y → Set.InjOn counterparty V → x ∈ V → x ∈ C V :=
  Iff.rfl

/-- Feasible-sub-menu rejection is monotone as the ambient menu grows. -/
theorem substituteEnvelope_substitutable (counterparty : X → A)
    (C : ChoiceFunction X) : (substituteEnvelope counterparty C).Substitutable := by
  apply substitutable_iff_chernoff.mpr
  intro Y Z hYZ x hx
  exact ⟨hx.2, fun V hV hfeas hxV => hx.1.2 V (hV.trans hYZ) hfeas hxV⟩

/-- Every substitutable completion lies below the envelope. -/
theorem IsCompletionOf.le_substituteEnvelope
    (hcomp : C.IsCompletionOf counterparty D) (hD : D.Substitutable) :
    D ≤ substituteEnvelope counterparty C := by
  intro Y x hx
  refine ⟨D.choose_subset Y hx, ?_⟩
  intro V hV hfeas hxV
  rw [← hcomp.eq_of_injOn_menu hfeas]
  exact hD.mem_of_subset hV hx hxV

/-- Any rule between the original rule and its envelope is a completion
when the original rule satisfies IRC. Substitutability of the middle rule
is not needed for this lemma. -/
theorem isCompletionOf_of_le_of_le_substituteEnvelope
    (hIRC : C.Consistent) (hCD : C ≤ D)
    (hDU : D ≤ substituteEnvelope counterparty C) :
    C.IsCompletionOf counterparty D := by
  classical
  intro Y
  by_cases hfeas : Set.InjOn counterparty (D Y)
  · left
    have heq : C (D Y) = C Y := hIRC (hCD Y) (D.choose_subset Y)
    apply Set.Subset.antisymm _ (hCD Y)
    intro x hx
    have h := (hDU Y hx).2 (D Y) (D.choose_subset Y) hfeas hx
    rwa [heq] at h
  · right
    simp only [Set.InjOn] at hfeas
    push Not at hfeas
    obtain ⟨x, hx, y, hy, heq, hne⟩ := hfeas
    exact ⟨x, hx, y, hy, hne, heq⟩

/-- Under IRC the envelope succeeds whenever any substitutable completion
does. This does not assert that the envelope is itself consistent. -/
theorem substituteEnvelope_isCompletionOf_of_substitutablyCompletable
    (hIRC : C.Consistent) (hC : C.SubstitutablyCompletable counterparty) :
    C.IsCompletionOf counterparty (substituteEnvelope counterparty C) := by
  classical
  obtain ⟨D, hcomp, hD⟩ := hC
  have hDU := hcomp.le_substituteEnvelope hD
  intro Y
  by_cases hfeas : Set.InjOn counterparty (substituteEnvelope counterparty C Y)
  · left
    have hDfeas : Set.InjOn counterparty (D Y) :=
      fun _ hx _ hy heq => hfeas (hDU Y hx) (hDU Y hy) heq
    have hDC := hcomp.eq_of_injOn hDfeas
    have hCU : C Y ⊆ substituteEnvelope counterparty C Y := by
      rw [← hDC]
      exact hDU Y
    have heq : C (substituteEnvelope counterparty C Y) = C Y :=
      hIRC hCU ((substituteEnvelope counterparty C).choose_subset Y)
    apply Set.Subset.antisymm _ hCU
    intro x hx
    have h : x ∈ C (substituteEnvelope counterparty C Y) :=
      hx.2 (substituteEnvelope counterparty C Y)
        ((substituteEnvelope counterparty C).choose_subset Y) hfeas hx
    rwa [heq] at h
  · right
    simp only [Set.InjOn] at hfeas
    push Not at hfeas
    obtain ⟨x, hx, y, hy, heq, hne⟩ := hfeas
    exact ⟨x, hx, y, hy, hne, heq⟩

/-- An explicit test for bare substitutable completability of an IRC rule. -/
theorem substitutablyCompletable_iff_substituteEnvelope_isCompletionOf
    (hIRC : C.Consistent) :
    C.SubstitutablyCompletable counterparty ↔
      C.IsCompletionOf counterparty (substituteEnvelope counterparty C) :=
  ⟨substituteEnvelope_isCompletionOf_of_substitutablyCompletable hIRC,
    fun h => ⟨_, h, substituteEnvelope_substitutable counterparty C⟩⟩

/-- If a substitutable completion exists, the envelope is the greatest one. -/
theorem isGreatest_substituteEnvelope (hIRC : C.Consistent)
    (hC : C.SubstitutablyCompletable counterparty) :
    IsGreatest {D : ChoiceFunction X |
      C.IsCompletionOf counterparty D ∧ D.Substitutable}
      (substituteEnvelope counterparty C) :=
  ⟨⟨substituteEnvelope_isCompletionOf_of_substitutablyCompletable hIRC hC,
      substituteEnvelope_substitutable counterparty C⟩,
    fun _ h => h.1.le_substituteEnvelope h.2⟩

/-- Pointwise enlargement is exactly substitutability restricted to feasible
smaller menus. The larger menu is unrestricted. -/
theorem le_substituteEnvelope_iff :
    C ≤ substituteEnvelope counterparty C ↔
      ∀ V Y, V ⊆ Y → Set.InjOn counterparty V → C Y ∩ V ⊆ C V := by
  constructor
  · intro h V Y hV hfeas x hx
    exact (h Y hx.1).2 V hV hfeas hx.2
  · intro h Y x hx
    exact ⟨C.choose_subset Y hx, fun V hV hfeas hxV => h V Y hV hfeas ⟨hx, hxV⟩⟩

/-- For feasible finite-valued IRC choice, unilateral substitutability
means that all original choices fit below the envelope. -/
theorem unilaterallySubstitutable_iff_le_substituteEnvelope
    (hIRC : C.Consistent) (hfeasible : ∀ Y, Set.InjOn counterparty (C Y))
    (hfinite : C.FiniteValued) :
    C.UnilaterallySubstitutable counterparty ↔ C ≤ substituteEnvelope counterparty C := by
  constructor
  · intro hUS
    exact (le_substituteHull C).trans
      ((hUS.substituteHull_isCompletionOf hIRC hfeasible hfinite).le_substituteEnvelope
        (substituteHull_substitutable C))
  · intro hCU
    have hcomp : C.IsCompletionOf counterparty (substituteEnvelope counterparty C) :=
      isCompletionOf_of_le_of_le_substituteEnvelope hIRC hCU le_rfl
    exact hcomp.unilaterallySubstitutable_of_le
      (substituteEnvelope_substitutable counterparty C) hCU hIRC hfeasible

/-- The sandwich describes enlarging completions only. It holds even
without feasibility or finite-valuedness of the original IRC rule. -/
theorem enlarging_substitutable_completion_iff_sandwich (hIRC : C.Consistent) :
    (C.IsCompletionOf counterparty D ∧ D.Substitutable ∧ C ≤ D) ↔
      (D.Substitutable ∧ C.substituteHull ≤ D ∧ D ≤ substituteEnvelope counterparty C) := by
  constructor
  · rintro ⟨hcomp, hD, hCD⟩
    exact ⟨hD, substituteHull_le hD hCD, hcomp.le_substituteEnvelope hD⟩
  · rintro ⟨hD, hHD, hDU⟩
    have hCD := (le_substituteHull C).trans hHD
    exact ⟨isCompletionOf_of_le_of_le_substituteEnvelope hIRC hCD hDU, hD, hCD⟩

end MathEconLib.Choice.ChoiceFunction
