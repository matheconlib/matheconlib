/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Choice.Matching.SubstituteEnvelope

/-!
# Rejection evidence for substitutable completability

A collection of contracts has rejection evidence at a menu if each contract is
rejected on some feasible sub-menu. If removing those contracts leaves a feasible
residual, a substitutable completion must agree with the original choice and so
cannot retain any of them. For an IRC rule this condition is also sufficient.

The formulation quantifies over sets of witnessed rejections rather than an
indexed family of sub-menus; taking all the witnesses recovers the union-of-
rejections formulation. Neither feasibility of the original choices nor
finiteness of contracts is needed. Finite bounds on obstruction certificates
are a separate result.
-/

@[expose] public section

namespace MathEconLib.Choice.ChoiceFunction

variable {X A : Type*} {counterparty : X → A} {C : ChoiceFunction X}

/-- Every rejection by the envelope has a feasible sub-menu witnessing it. -/
theorem mem_rejected_substituteEnvelope_iff {Y : Set X} {x : X} :
    x ∈ (substituteEnvelope counterparty C).rejected Y ↔
      ∃ V, V ⊆ Y ∧ Set.InjOn counterparty V ∧ x ∈ C.rejected V := by
  classical
  constructor
  · rintro ⟨hxY, hxU⟩
    by_contra hnone
    apply hxU
    refine ⟨hxY, ?_⟩
    intro V hV hfeas hxV
    by_contra hxC
    exact hnone ⟨V, hV, hfeas, hxV, hxC⟩
  · rintro ⟨V, hV, hfeas, hxV, hxC⟩
    exact ⟨hV hxV, fun hxU => hxC (hxU.2 V hV hfeas hxV)⟩

/-- Witnessed rejections cannot remove original choices when the residual menu
is feasible. A witness is a feasible sub-menu rejecting the contract in question. -/
def RejectionEvidence (counterparty : X → A) (C : ChoiceFunction X) : Prop :=
  ∀ Y R : Set X,
    (∀ x ∈ R, ∃ V, V ⊆ Y ∧ Set.InjOn counterparty V ∧ x ∈ C.rejected V) →
    Set.InjOn counterparty (Y \ R) → Disjoint (C Y) R

/-- Necessity uses only substitutability and completion, not IRC. -/
theorem SubstitutablyCompletable.rejectionEvidence
    (hC : C.SubstitutablyCompletable counterparty) : C.RejectionEvidence counterparty := by
  obtain ⟨D, hcomp, hsub⟩ := hC
  intro Y R hevidence hresidual
  have hDR : D Y ⊆ Y \ R := by
    intro x hx
    refine ⟨D.choose_subset Y hx, ?_⟩
    intro hxR
    obtain ⟨V, hV, hfeas, hxV, hxC⟩ := hevidence x hxR
    have hxD := hsub.mem_of_subset hV hx hxV
    rw [hcomp.eq_of_injOn_menu hfeas] at hxD
    exact hxC hxD
  have hfeas : Set.InjOn counterparty (D Y) :=
    fun _ hx _ hy heq => hresidual (hDR hx) (hDR hy) heq
  rw [← hcomp.eq_of_injOn hfeas]
  exact Set.disjoint_left.mpr (fun _ hx hxR => (hDR hx).2 hxR)

/-- Under IRC, rejection evidence is a necessary and sufficient condition for
bare substitutable completability, even without feasible-valuedness. -/
theorem substitutablyCompletable_iff_rejectionEvidence (hIRC : C.Consistent) :
    C.SubstitutablyCompletable counterparty ↔ C.RejectionEvidence counterparty := by
  classical
  refine ⟨fun h => h.rejectionEvidence, ?_⟩
  intro hevidence
  apply (substitutablyCompletable_iff_substituteEnvelope_isCompletionOf hIRC).2
  intro Y
  by_cases hfeas : Set.InjOn counterparty (substituteEnvelope counterparty C Y)
  · left
    let R := (substituteEnvelope counterparty C).rejected Y
    have hresidual : Y \ R = substituteEnvelope counterparty C Y := by
      ext x
      change (x ∈ Y ∧ ¬ (x ∈ Y ∧ x ∉ substituteEnvelope counterparty C Y)) ↔ _
      constructor
      · intro hx
        by_contra hnot
        exact hx.2 ⟨hx.1, hnot⟩
      · intro hx
        exact ⟨hx.1, fun h => h.2 hx⟩
    have hdisjoint : Disjoint (C Y) R := hevidence Y R
      (fun _ hx => mem_rejected_substituteEnvelope_iff.mp hx)
      (hresidual.symm ▸ hfeas)
    have hCU : C Y ⊆ substituteEnvelope counterparty C Y := by
      intro x hx
      by_contra hnot
      exact Set.disjoint_left.mp hdisjoint hx ⟨C.choose_subset Y hx, hnot⟩
    have heq := hIRC hCU ((substituteEnvelope counterparty C).choose_subset Y)
    apply Set.Subset.antisymm _ hCU
    intro x hx
    have h := hx.2 (substituteEnvelope counterparty C Y)
      ((substituteEnvelope counterparty C).choose_subset Y) hfeas hx
    rwa [heq] at h
  · right
    simp only [Set.InjOn] at hfeas
    push Not at hfeas
    obtain ⟨x, hx, y, hy, heq, hne⟩ := hfeas
    exact ⟨x, hx, y, hy, hne, heq⟩

/-- A witnessed rejection of an original choice, with feasible residual,
rules out every substitutable completion. -/
theorem not_substitutablyCompletable_of_rejectionEvidence
    {Y R : Set X}
    (hevidence : ∀ x ∈ R,
      ∃ V, V ⊆ Y ∧ Set.InjOn counterparty V ∧ x ∈ C.rejected V)
    (hresidual : Set.InjOn counterparty (Y \ R))
    {x : X} (hxC : x ∈ C Y) (hxR : x ∈ R) :
    ¬ C.SubstitutablyCompletable counterparty := by
  intro hC
  exact Set.disjoint_left.mp (hC.rejectionEvidence Y R hevidence hresidual) hxC hxR

end MathEconLib.Choice.ChoiceFunction
