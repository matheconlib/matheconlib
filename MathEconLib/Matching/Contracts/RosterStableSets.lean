/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Contracts.RosterCompletion
public import MathEconLib.Matching.Contracts.RosterStability

/-!
# Stable sets attainable under a term-independent roster rule

A hospital chooses whom to hire from the represented workers, then chooses
one contract for each member of that roster. Its terms may depend on the
whole offer menu. If the roster choice satisfies substitutes and IRC and the
original contract choice satisfies IRC, every stable outcome employs the
roster selected from all workers.

A family of assignments on that roster is exactly the stable set of some
substitutable IRC completion iff its members are originally stable, it contains
the worker-favourite assignment, and it is closed under giving each worker the
worse of their terms in two assignments. In particular, one completion can
preserve the whole original stable set iff that set is closed under workerwise
meets. The proof uses choice-theoretic stability.
-/

@[expose] public section

namespace MathEconLib.Matching

open MathEconLib.Choice

variable {X S : Type*} {seller : X → S}
  [∀ i, LinearOrder {x : X // seller x = i}] [Finite X]
variable {R : ChoiceFunction S} {C D : ChoiceFunction X}

omit [Finite X] in
private theorem choose_improvementMenu_inf_of_stable
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y))
    (hRIRC : R.Consistent) (hComp : C.IsCompletionOf seller D)
    (hDSub : D.Substitutable)
    {A B : RosterAssignment seller (R (Set.range seller))}
    (hA : (rosterMarket seller D).Stable A.terms)
    (hB : (rosterMarket seller D).Stable B.terms) :
    D (A ⊓ B).improvementMenu = (A ⊓ B).terms := by
  let M := A ⊓ B
  change D M.improvementMenu = M.terms
  have hsub : D M.improvementMenu ⊆ M.terms := by
    intro x hx
    by_contra hxM
    have hxU : x ∈ M.improvementMenu := D.choose_subset _ hx
    have reject (P : RosterAssignment seller (R (Set.range seller)))
        (hP : (rosterMarket seller D).Stable P.terms) (hle : M ≤ P)
        (hxP : x ∈ P.improvementMenu) (hxNotP : x ∉ P.terms) : False := by
      have hmenu : insert x P.terms ⊆ M.improvementMenu :=
        Set.insert_subset_iff.mpr
          ⟨hxU, P.terms_subset_improvementMenu.trans
            (RosterAssignment.improvementMenu_antitone hle)⟩
      have hxD : x ∈ D (insert x P.terms) :=
        hDSub.mem_of_subset hmenu hx (Set.mem_insert _ _)
      have hxS : x ∈ (rosterMarket seller D).toBuyers P.terms := by
        rwa [rosterMarket_toBuyers_terms seller D P]
      exact hxNotP ((rosterMarket seller D).not_blocking_singleton hP hxD hxS)
    by_cases hs : seller x ∈ R (Set.range seller)
    · let i : R (Set.range seller) := ⟨seller x, hs⟩
      have reject_at_term (P : RosterAssignment seller (R (Set.range seller)))
          (hP : (rosterMarket seller D).Stable P.terms) (hle : M ≤ P)
          (heq : M i = P i) : False := by
        apply reject P hP hle
        · intro j hj
          have hij : j = i := Subtype.ext hj.symm
          subst j
          simpa only [← heq] using hxU i rfl
        · intro hxP
          apply hxM
          apply (RosterAssignment.mem_terms_iff (A := M) (x := x) i rfl).mpr
          rw [heq]
          exact (RosterAssignment.mem_terms_iff (A := P) (x := x) i rfl).mp hxP
      rcases (show M i = A i ∨ M i = B i from min_choice _ _) with hi | hi
      · exact reject_at_term A hA inf_le_left hi
      · exact reject_at_term B hB inf_le_right hi
    · apply reject A hA inf_le_left
      · intro i hi
        exact (hs (hi ▸ i.property)).elim
      · intro hxA
        have hmem : seller x ∈ seller '' A.terms := ⟨x, hxA, rfl⟩
        exact hs (A.image_terms ▸ hmem)
  have hEq := hComp.eq_of_injOn (M.injOn_terms.mono hsub)
  have hR := roster_eq_of_terms_subset hRIRC M.terms_subset_improvementMenu
  apply (M.injOn_terms.image_eq_image_iff hsub Set.Subset.rfl).mp
  rw [hEq, hRoster, hR, M.image_terms]

/-- The stable sets attainable under substitutable IRC completions are exactly
the meet-closed subfamilies of the original stable set containing the
worker-favourite assignment. The equality on the left covers the entire
stable set, including the claim that there are no other stable outcomes. -/
theorem roster_attainable_stable_sets_iff
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y))
    (hFeas : ∀ Y, Set.InjOn seller (C Y))
    (hRSub : R.Substitutable) (hRIRC : R.Consistent) (hCIRC : C.Consistent)
    (T : Set (RosterAssignment seller (R (Set.range seller)))) :
    (∃ D : ChoiceFunction X, C.IsCompletionOf seller D ∧ D.Substitutable ∧ D.Consistent ∧
      {A | (rosterMarket seller D).Stable A} = RosterAssignment.terms '' T) ↔
    (∀ A ∈ T, (rosterMarket seller C).Stable A.terms) ∧
      RosterAssignment.favourite (R.choose_subset (Set.range seller)) ∈ T ∧ InfClosed T := by
  constructor
  · rintro ⟨D, hComp, hDSub, hDIRC, hEq⟩
    have stable_of_mem {A : RosterAssignment seller (R (Set.range seller))}
        (hA : A ∈ T) : (rosterMarket seller D).Stable A.terms := by
      have hmem : A.terms ∈ RosterAssignment.terms '' T := ⟨A, hA, rfl⟩
      rwa [← hEq] at hmem
    have mem_of_stable {A : RosterAssignment seller (R (Set.range seller))}
        (hA : (rosterMarket seller D).Stable A.terms) : A ∈ T := by
      have hmem : A.terms ∈ {Y | (rosterMarket seller D).Stable Y} := hA
      rw [hEq] at hmem
      obtain ⟨B, hB, hBA⟩ := hmem
      exact RosterAssignment.terms_injective hBA ▸ hB
    refine ⟨?_, mem_of_stable
      (rosterMarket_favourite_stable seller hRoster hRIRC hComp hDSub), ?_⟩
    · intro A hA
      have hD := (rosterMarket_stable_terms_iff_of_substitutable seller hDSub hDIRC A).mp
        (stable_of_mem hA)
      apply (rosterMarket_stable_terms_iff seller hFeas hCIRC A).mpr
      have hChoice : Set.InjOn seller (D A.improvementMenu) := hD ▸ A.injOn_terms
      exact (hComp.eq_of_injOn hChoice).symm.trans hD
    · intro A hA B hB
      apply mem_of_stable
      apply (rosterMarket_stable_terms_iff_of_substitutable seller hDSub hDIRC _).mpr
      exact choose_improvementMenu_inf_of_stable hRoster hRIRC hComp hDSub
        (stable_of_mem hA) (stable_of_mem hB)
  · rintro ⟨hStable, hTop, hT⟩
    let D := rosterCompletion seller R T
    have hDSub : D.Substitutable := rosterCompletion_substitutable hRSub
    have hDIRC : D.Consistent := rosterCompletion_consistent hRIRC hT
    have hComp : C.IsCompletionOf seller D :=
      rosterCompletion_isCompletionOf hRIRC hCIRC hRoster hT
        (fun A hA ↦ (rosterMarket_stable_terms_iff seller hFeas hCIRC A).mp (hStable A hA))
    refine ⟨D, hComp, hDSub, hDIRC, Set.Subset.antisymm ?_ ?_⟩
    · intro Y hY
      obtain ⟨A, rfl⟩ :=
        exists_rosterAssignment_of_stable seller hRoster hRSub hRIRC hComp hY
      have hEq := (rosterMarket_stable_terms_iff_of_substitutable seller hDSub hDIRC A).mp hY
      have hTopMenu : (RosterAssignment.favourite
          (R.choose_subset (Set.range seller))).terms ⊆ A.improvementMenu :=
        RosterAssignment.terms_subset_improvementMenu_iff.mpr
          (RosterAssignment.le_favourite _ A)
      obtain ⟨K, hK, hKY, hbound⟩ :=
        exists_rosterCompletion_cutoff hT ⟨_, hTop, hTopMenu⟩
      have hKA : K.terms ⊆ A.terms := by
        rw [← hEq]
        exact rosterCompletion_terms_subset hRIRC hKY hbound
      have hKeq : K.terms = A.terms :=
        (A.injOn_terms.image_eq_image_iff hKA Set.Subset.rfl).mp
          (K.image_terms.trans A.image_terms.symm)
      exact ⟨K, hK, hKeq⟩
    · rintro Y ⟨A, hA, rfl⟩
      apply (rosterMarket_stable_terms_iff_of_substitutable seller hDSub hDIRC A).mpr
      exact rosterCompletion_eq_terms_on_improvementMenu hRIRC hA

/-- The whole original stable set is realizable by one substitutable IRC
completion exactly when the original stable assignments are closed under
workerwise meets. -/
theorem roster_exact_whole_stable_set_iff
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y))
    (hFeas : ∀ Y, Set.InjOn seller (C Y))
    (hRSub : R.Substitutable) (hRIRC : R.Consistent) (hCIRC : C.Consistent) :
    (∃ D : ChoiceFunction X, C.IsCompletionOf seller D ∧ D.Substitutable ∧ D.Consistent ∧
      {A | (rosterMarket seller D).Stable A} = {A | (rosterMarket seller C).Stable A}) ↔
    InfClosed {A : RosterAssignment seller (R (Set.range seller)) |
      (rosterMarket seller C).Stable A.terms} := by
  let T := {A : RosterAssignment seller (R (Set.range seller)) |
    (rosterMarket seller C).Stable A.terms}
  have hOriginal : {A | (rosterMarket seller C).Stable A} =
      RosterAssignment.terms '' T := by
    apply Set.Subset.antisymm
    · intro A hA
      obtain ⟨B, hBA⟩ :=
        exists_rosterAssignment_of_stable seller hRoster hRSub hRIRC
          (ChoiceFunction.isCompletionOf_refl seller C) hA
      have hB : B ∈ T := by
        change (rosterMarket seller C).Stable B.terms
        rwa [hBA]
      exact ⟨B, hB, hBA⟩
    · rintro _ ⟨A, hA, rfl⟩
      exact hA
  rw [hOriginal, roster_attainable_stable_sets_iff hRoster hFeas hRSub hRIRC hCIRC T]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨fun _ hA ↦ hA,
    rosterMarket_favourite_stable_original seller hRoster hRIRC hFeas hCIRC, h⟩⟩

/-- One substitutable completion preserves every original stable outcome iff
the original stable set is closed under workerwise meets. When this holds,
one can take the completion to satisfy IRC and have exactly the original
stable set by the attainable-stable-sets theorem. -/
theorem roster_preserves_whole_stable_set_iff
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y))
    (hFeas : ∀ Y, Set.InjOn seller (C Y))
    (hRSub : R.Substitutable) (hRIRC : R.Consistent) (hCIRC : C.Consistent) :
    (∃ D : ChoiceFunction X, C.IsCompletionOf seller D ∧ D.Substitutable ∧
      ∀ A, (rosterMarket seller C).Stable A → (rosterMarket seller D).Stable A) ↔
    InfClosed {A : RosterAssignment seller (R (Set.range seller)) |
      (rosterMarket seller C).Stable A.terms} := by
  constructor
  · rintro ⟨D, hComp, hDSub, hPres⟩ A hA B hB
    have hD := choose_improvementMenu_inf_of_stable hRoster hRIRC hComp hDSub
      (hPres A.terms hA) (hPres B.terms hB)
    have hChoice : Set.InjOn seller (D (A ⊓ B).improvementMenu) := hD ▸ (A ⊓ B).injOn_terms
    exact (rosterMarket_stable_terms_iff seller hFeas hCIRC _).mpr
      ((hComp.eq_of_injOn hChoice).symm.trans hD)
  · intro hClosed
    obtain ⟨D, hComp, hDSub, _, hEq⟩ :=
      (roster_exact_whole_stable_set_iff hRoster hFeas hRSub hRIRC hCIRC).mpr hClosed
    refine ⟨D, hComp, hDSub, fun A hA ↦ ?_⟩
    have hMem : A ∈ {Y | (rosterMarket seller C).Stable Y} := hA
    rwa [← hEq] at hMem

end MathEconLib.Matching
