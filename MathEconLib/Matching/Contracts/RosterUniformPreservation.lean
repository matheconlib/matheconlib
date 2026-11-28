/-
Copyright (c) 2026 MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MathEconLib contributors
-/
module

public import MathEconLib.Matching.Contracts.RosterStableSets

/-!
# Uniform preservation under term-independent staffing

This module constructs a completion that works for every doctor profile in the
one-hospital roster model, provided the hospital's choice contracts consistently
on menus that represent the final roster. The completion uses no doctor orders.
-/

@[expose] public section

namespace MathEconLib.Matching

open MathEconLib.Choice

variable {X S : Type*} {seller : X → S} {R : ChoiceFunction S} {C : ChoiceFunction X}

/-- A menu represents the final roster if it offers a contract of each doctor
selected when every doctor is represented. -/
def RepresentsFinalRoster (seller : X → S) (R : ChoiceFunction S) (Y : Set X) : Prop :=
  R (Set.range seller) ⊆ seller '' Y

/-- The Chernoff contraction condition on menus representing the final roster. -/
def FullRosterContraction (seller : X → S) (R : ChoiceFunction S)
    (C : ChoiceFunction X) : Prop :=
  ∀ ⦃U V : Set X⦄, U ⊆ V → RepresentsFinalRoster seller R U → C V ∩ U ⊆ C U

theorem RepresentsFinalRoster.mono {U V : Set X} (h : RepresentsFinalRoster seller R U)
    (hUV : U ⊆ V) : RepresentsFinalRoster seller R V :=
  h.trans (Set.image_mono hUV)

theorem RepresentsFinalRoster.roster_eq {Y : Set X}
    (hY : RepresentsFinalRoster seller R Y) (hRIRC : R.Consistent) :
    R (seller '' Y) = R (Set.range seller) :=
  hRIRC hY (Set.image_subset_range seller Y)

/-- On menus representing the final roster, a selected doctor's chosen term
depends only on the terms offered by that doctor. -/
def OwnTermsDetermineChoice (seller : X → S) (R : ChoiceFunction S)
    (C : ChoiceFunction X) : Prop :=
  ∀ ⦃U V : Set X⦄, RepresentsFinalRoster seller R U → RepresentsFinalRoster seller R V →
    ∀ ⦃x y : X⦄, x ∈ C U → y ∈ C V → seller x = seller y →
      {z ∈ U | seller z = seller x} = {z ∈ V | seller z = seller x} → x = y

theorem fullRosterContraction_iff_ownTermsDetermineChoice
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y))
    (hFeas : ∀ Y, Set.InjOn seller (C Y))
    (hRIRC : R.Consistent) (hCIRC : C.Consistent) :
    FullRosterContraction seller R C ↔ OwnTermsDetermineChoice seller R C := by
  classical
  have hImage {Y : Set X} (hY : RepresentsFinalRoster seller R Y) :
      seller '' C Y = R (Set.range seller) := (hRoster Y).trans (hY.roster_eq hRIRC)
  constructor
  · intro h U V hU hV x y hx hy hxy hOwn
    have hUnion := hU.mono (Set.subset_union_left (s := U) (t := V))
    have hxW : seller x ∈ R (Set.range seller) :=
      hImage hU ▸ Set.mem_image_of_mem seller hx
    have hxUnion : seller x ∈ seller '' C (U ∪ V) := (hImage hUnion).symm ▸ hxW
    obtain ⟨z, hz, hzx⟩ := hxUnion
    have hzMem := C.choose_subset _ hz
    have hzBoth : z ∈ U ∩ V := by
      rcases hzMem with hzU | hzV
      · have hzu : z ∈ {z ∈ U | seller z = seller x} := ⟨hzU, hzx⟩
        have hzv : z ∈ {z ∈ V | seller z = seller x} := hOwn ▸ hzu
        exact ⟨hzU, hzv.1⟩
      · have hzv : z ∈ {z ∈ V | seller z = seller x} := ⟨hzV, hzx⟩
        have hzu : z ∈ {z ∈ U | seller z = seller x} := hOwn.symm ▸ hzv
        exact ⟨hzu.1, hzV⟩
    have hzU := h Set.subset_union_left hU ⟨hz, hzBoth.1⟩
    have hzV := h Set.subset_union_right hV ⟨hz, hzBoth.2⟩
    exact (hFeas U hzU hx hzx).symm.trans (hFeas V hzV hy (hzx.trans hxy))
  · intro h U V hUV hU x hx
    have hV := hU.mono hUV
    have hxW : seller x ∈ R (Set.range seller) :=
      hImage hV ▸ Set.mem_image_of_mem seller hx.1
    have hxU : seller x ∈ seller '' C U := (hImage hU).symm ▸ hxW
    obtain ⟨y, hy, hyx⟩ := hxU
    let U' := insert x (C U)
    let V' := insert y (C V)
    have hU' : RepresentsFinalRoster seller R U' := by
      change R (Set.range seller) ⊆ seller '' U'
      rw [← hImage hU]
      exact Set.image_mono (Set.subset_insert x (C U))
    have hV' : RepresentsFinalRoster seller R V' := by
      change R (Set.range seller) ⊆ seller '' V'
      rw [← hImage hV]
      exact Set.image_mono (Set.subset_insert y (C V))
    have hCU' : C U' = C U :=
      hCIRC (Set.subset_insert x (C U)) (Set.insert_subset_iff.mpr ⟨hx.2, C.choose_subset _⟩)
    have hCV' : C V' = C V :=
      hCIRC (Set.subset_insert y (C V))
        (Set.insert_subset_iff.mpr ⟨hUV (C.choose_subset _ hy), C.choose_subset _⟩)
    have hOwn : {z ∈ U' | seller z = seller y} = {z ∈ V' | seller z = seller y} := by
      ext z
      constructor
      · intro hz
        refine ⟨?_, hz.2⟩
        rcases Set.mem_insert_iff.mp hz.1 with rfl | hzU
        · exact Set.mem_insert_of_mem _ hx.1
        · rw [hFeas U hzU hy hz.2]
          exact Set.mem_insert _ _
      · intro hz
        refine ⟨?_, hz.2⟩
        rcases Set.mem_insert_iff.mp hz.1 with rfl | hzV
        · exact Set.mem_insert_of_mem _ hy
        · rw [hFeas V hzV hx.1 (hz.2.trans hyx)]
          exact Set.mem_insert _ _
    have hy' : y ∈ C U' := hCU'.symm ▸ hy
    have hx' : x ∈ C V' := hCV'.symm ▸ hx.1
    exact h hU' hV' hy' hx' hyx hOwn ▸ hy

/-- On a full menu keep the original choice; otherwise keep all offered terms
of each doctor whom the roster rule selects. -/
noncomputable def uniformRosterCompletion (seller : X → S) (R : ChoiceFunction S)
    (C : ChoiceFunction X) : ChoiceFunction X := by
  classical
  refine ⟨fun Y ↦ if RepresentsFinalRoster seller R Y then C Y
    else {x ∈ Y | seller x ∈ R (seller '' Y)}, ?_⟩
  intro Y
  split
  · exact C.choose_subset _
  · exact fun _ hx ↦ hx.1

theorem uniformRosterCompletion_eq_of_full {Y : Set X}
    (hY : RepresentsFinalRoster seller R Y) : uniformRosterCompletion seller R C Y = C Y := by
  classical
  exact ite_eq_left hY

private theorem uniformRosterCompletion_eq_of_partial {Y : Set X}
    (hY : ¬RepresentsFinalRoster seller R Y) :
    uniformRosterCompletion seller R C Y = {x ∈ Y | seller x ∈ R (seller '' Y)} := by
  classical
  exact ite_eq_right hY

theorem image_uniformRosterCompletion
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y)) (Y : Set X) :
    seller '' uniformRosterCompletion seller R C Y = R (seller '' Y) := by
  classical
  by_cases hY : RepresentsFinalRoster seller R Y
  · rw [uniformRosterCompletion_eq_of_full hY, hRoster]
  · rw [uniformRosterCompletion_eq_of_partial hY]
    ext i
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hi
      obtain ⟨x, hx, rfl⟩ := R.choose_subset _ hi
      exact ⟨x, ⟨hx, hi⟩, rfl⟩

theorem uniformRosterCompletion_isCompletionOf
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y)) :
    C.IsCompletionOf seller (uniformRosterCompletion seller R C) := by
  apply ChoiceFunction.isCompletionOf_of_le_of_image_subset
  · intro Y
    classical
    by_cases hY : RepresentsFinalRoster seller R Y
    · rw [uniformRosterCompletion_eq_of_full hY]
    · rw [uniformRosterCompletion_eq_of_partial hY]
      intro x hx
      refine ⟨C.choose_subset _ hx, ?_⟩
      rw [← hRoster]
      exact ⟨x, hx, rfl⟩
  · intro Y
    rw [image_uniformRosterCompletion hRoster, hRoster]

theorem uniformRosterCompletion_substitutable
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y)) (hRSub : R.Substitutable)
    (hFull : FullRosterContraction seller R C) :
    (uniformRosterCompletion seller R C).Substitutable := by
  apply ChoiceFunction.substitutable_iff_chernoff.mpr
  intro U V hUV x hx
  classical
  by_cases hU : RepresentsFinalRoster seller R U
  · have hV := hU.mono hUV
    rw [uniformRosterCompletion_eq_of_full hU]
    apply hFull hUV hU
    rwa [uniformRosterCompletion_eq_of_full hV] at hx
  · rw [uniformRosterCompletion_eq_of_partial hU]
    refine ⟨hx.2, hRSub.mem_of_subset (Set.image_mono hUV) ?_ ⟨x, hx.2, rfl⟩⟩
    rw [← image_uniformRosterCompletion hRoster V]
    exact ⟨x, hx.1, rfl⟩

theorem uniformRosterCompletion_consistent
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y)) (hRIRC : R.Consistent)
    (hCIRC : C.Consistent) : (uniformRosterCompletion seller R C).Consistent := by
  intro V U hDU hUV
  classical
  have hImg := Set.image_mono (f := seller) hDU
  rw [image_uniformRosterCompletion hRoster] at hImg
  by_cases hV : RepresentsFinalRoster seller R V
  · have hR : R (seller '' V) = R (Set.range seller) :=
      hRIRC hV (Set.image_subset_range seller V)
    have hU : RepresentsFinalRoster seller R U := by
      change R (Set.range seller) ⊆ seller '' U
      exact hR ▸ hImg
    rw [uniformRosterCompletion_eq_of_full hU, uniformRosterCompletion_eq_of_full hV]
    rw [uniformRosterCompletion_eq_of_full hV] at hDU
    exact hCIRC hDU hUV
  · have hU : ¬RepresentsFinalRoster seller R U := fun h ↦ hV (h.mono hUV)
    have hR := hRIRC hImg (Set.image_mono hUV)
    rw [uniformRosterCompletion_eq_of_partial hU, uniformRosterCompletion_eq_of_partial hV]
    rw [uniformRosterCompletion_eq_of_partial hV] at hDU
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hUV hx.1, hR ▸ hx.2⟩
    · intro x hx
      exact ⟨hDU hx, hR.symm ▸ hx.2⟩

/-- Full-roster contraction suffices for exact stability preservation, for any
strict doctor orders. The choice `uniformRosterCompletion` is profile-independent. -/
theorem rosterMarket_stable_uniformRosterCompletion_iff
    [Finite X] [∀ i, LinearOrder {x : X // seller x = i}]
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y))
    (hFeas : ∀ Y, Set.InjOn seller (C Y))
    (hRSub : R.Substitutable) (hRIRC : R.Consistent) (hCIRC : C.Consistent)
    (hFull : FullRosterContraction seller R C) {Y : Set X} :
    (rosterMarket seller (uniformRosterCompletion seller R C)).Stable Y ↔
      (rosterMarket seller C).Stable Y := by
  have hComp := uniformRosterCompletion_isCompletionOf hRoster
  have hSub := uniformRosterCompletion_substitutable hRoster hRSub hFull
  have hIRC := uniformRosterCompletion_consistent hRoster hRIRC hCIRC
  have hiff (A : RosterAssignment seller (R (Set.range seller))) :
      (rosterMarket seller (uniformRosterCompletion seller R C)).Stable A.terms ↔
        (rosterMarket seller C).Stable A.terms := by
    have hMenu : RepresentsFinalRoster seller R A.improvementMenu := by
      change R (Set.range seller) ⊆ seller '' A.improvementMenu
      rw (occs := .pos [1]) [← A.image_terms]
      exact Set.image_mono A.terms_subset_improvementMenu
    rw [rosterMarket_stable_terms_iff_of_substitutable seller hSub hIRC,
      rosterMarket_stable_terms_iff seller hFeas hCIRC, uniformRosterCompletion_eq_of_full hMenu]
  constructor
  · intro h
    obtain ⟨A, rfl⟩ := exists_rosterAssignment_of_stable seller hRoster hRSub hRIRC hComp h
    exact (hiff A).mp h
  · intro h
    obtain ⟨A, rfl⟩ := exists_rosterAssignment_of_stable seller hRoster hRSub hRIRC
      (ChoiceFunction.isCompletionOf_refl seller C) h
    exact (hiff A).mpr h

/-- A full-roster-agreeing substitutable choice forces the full-menu contraction
condition. No order on doctors' terms enters this implication. -/
theorem fullRosterContraction_of_agreeing_substitutable {D : ChoiceFunction X}
    (hD : D.Substitutable)
    (hAgree : ∀ Y, RepresentsFinalRoster seller R Y → D Y = C Y) :
    FullRosterContraction seller R C := by
  intro U V hUV hU
  rw [← hAgree U hU, ← hAgree V (hU.mono hUV)]
  exact (ChoiceFunction.substitutable_iff_chernoff.mp hD) hUV

/-- Under full-roster contraction, one substitutable IRC completion preserves
exactly the original stable set for all strict all-acceptable doctor orders. -/
theorem exists_uniform_completion_of_fullRosterContraction [Finite X]
    (hRoster : ∀ Y, seller '' C Y = R (seller '' Y))
    (hFeas : ∀ Y, Set.InjOn seller (C Y))
    (hRSub : R.Substitutable) (hRIRC : R.Consistent) (hCIRC : C.Consistent)
    (hFull : FullRosterContraction seller R C) :
    ∃ D : ChoiceFunction X, C.IsCompletionOf seller D ∧ D.Substitutable ∧ D.Consistent ∧
      ∀ p : ∀ i, LinearOrder {x : X // seller x = i}, letI := p
        ∀ Y : Set X, (rosterMarket seller C).Stable Y ↔ (rosterMarket seller D).Stable Y := by
  refine ⟨uniformRosterCompletion seller R C, uniformRosterCompletion_isCompletionOf hRoster,
    uniformRosterCompletion_substitutable hRoster hRSub hFull,
    uniformRosterCompletion_consistent hRoster hRIRC hCIRC, ?_⟩
  intro p
  let _ := p
  intro Y
  exact (rosterMarket_stable_uniformRosterCompletion_iff
    hRoster hFeas hRSub hRIRC hCIRC hFull (Y := Y)).symm

end MathEconLib.Matching
