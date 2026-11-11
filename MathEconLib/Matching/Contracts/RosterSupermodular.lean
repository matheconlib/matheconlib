/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Contracts.RosterStableSets

/-!
# Supermodular hospital payoffs

A hospital's unique maximizers on the improvement menus are closed under
the doctorwise worse term when its payoff is supermodular in doctors' terms.
In the roster model these fixed choices are the stable assignments.
-/

@[expose] public section

namespace MathEconLib.Matching

open MathEconLib.Choice

variable {S X P : Type*} (seller : X → S) {W : Set S} {C : ChoiceFunction X}
  [∀ i, LinearOrder {x : X // seller x = i}] [Finite X]
  [AddCommMonoid P] [LinearOrder P] [IsOrderedCancelAddMonoid P]

/-- If the hospital uniquely maximizes a supermodular payoff on improvement menus
at a given roster, the stable assignments on that roster are closed under meet. -/
theorem rosterMarket_infClosed_stable_of_supermodular
    (hFeas : ∀ Y, Set.InjOn seller (C Y)) (hCIRC : C.Consistent)
    (u : RosterAssignment seller W → P)
    (hSupermod : ∀ A B, u A + u B ≤ u (A ⊔ B) + u (A ⊓ B))
    (hMax : ∀ A, ∃ Q, A ≤ Q ∧ C A.improvementMenu = Q.terms ∧
      ∀ B, A ≤ B → B ≠ Q → u B < u Q) :
    InfClosed {A : RosterAssignment seller W | (rosterMarket seller C).Stable A.terms} := by
  intro A hA B hB
  let M := A ⊓ B
  obtain ⟨Z, hMZ, hCZ, hZmax⟩ := hMax M
  have hStableMax (P : RosterAssignment seller W) (hP : (rosterMarket seller C).Stable P.terms)
      (Q : RosterAssignment seller W) (hPQ : P ≤ Q) : u Q ≤ u P := by
    obtain ⟨H, _, hCH, hHmax⟩ := hMax P
    have hHP : H = P := RosterAssignment.terms_injective
      (hCH.symm.trans ((rosterMarket_stable_terms_iff seller hFeas hCIRC P).mp hP))
    subst H
    by_cases hQP : Q = P
    · rw [hQP]
    · exact (hHmax Q hPQ hQP).le
  have hZle (P : RosterAssignment seller W) (hMP : M ≤ P)
      (hP : (rosterMarket seller C).Stable P.terms) : Z ≤ P := by
    by_contra hn
    have hInfNe : Z ⊓ P ≠ Z := fun h ↦ hn (inf_eq_left.mp h)
    have hInf : u (Z ⊓ P) < u Z := hZmax _ (le_inf hMZ hMP) hInfNe
    have hSup : u (Z ⊔ P) ≤ u P := hStableMax P hP _ le_sup_right
    have hsum : u (Z ⊔ P) + u (Z ⊓ P) < u Z + u P :=
      (add_lt_add_of_le_of_lt hSup hInf).trans_eq (add_comm _ _)
    exact (not_lt_of_ge (hSupermod Z P)) hsum
  have hZM : Z = M := le_antisymm (le_inf (hZle A inf_le_left hA) (hZle B inf_le_right hB)) hMZ
  exact (rosterMarket_stable_terms_iff seller hFeas hCIRC M).mpr (by rw [hCZ, hZM])

/-- Supermodular term payoffs give a substitutable IRC completion that preserves
exactly the original stable set of a hospital with term-independent staffing. -/
theorem roster_exact_whole_stable_set_of_supermodular
    {R : ChoiceFunction S}
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y))
    (hFeas : ∀ Y, Set.InjOn seller (C Y))
    (hRSub : R.Substitutable) (hRIRC : R.Consistent) (hCIRC : C.Consistent)
    (u : RosterAssignment seller (R (Set.range seller)) → P)
    (hSupermod : ∀ A B, u A + u B ≤ u (A ⊔ B) + u (A ⊓ B))
    (hMax : ∀ A, ∃ Q, A ≤ Q ∧ C A.improvementMenu = Q.terms ∧
      ∀ B, A ≤ B → B ≠ Q → u B < u Q) :
    ∃ D : ChoiceFunction X, C.IsCompletionOf seller D ∧ D.Substitutable ∧ D.Consistent ∧
      {A | (rosterMarket seller D).Stable A} = {A | (rosterMarket seller C).Stable A} :=
  (roster_exact_whole_stable_set_iff hRoster hFeas hRSub hRIRC hCIRC).mpr
    (rosterMarket_infClosed_stable_of_supermodular seller hFeas hCIRC u hSupermod hMax)

end MathEconLib.Matching
