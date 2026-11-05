/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Contracts.RosterAssignments
public import MathEconLib.Matching.Contracts.Completion

/-!
# Stability with term-independent hiring

An IRC hospital may choose the terms jointly while using a substitutable IRC
roster rule to decide whom to hire. Every stable outcome has the roster selected
when every worker is represented. The same conclusion holds under completion.
On this roster, stability can be tested on the menu of incumbent and preferred
terms, including all offers from workers who remain unmatched.
-/

@[expose] public section

namespace MathEconLib.Matching

open MathEconLib.Choice

variable {S X : Type*} (seller : X → S)
variable [∀ i, LinearOrder {x : X // seller x = i}]

private theorem rosterMarket_buyerSide (C : ChoiceFunction X) (b : Unit) (Y : Set X) :
    (rosterMarket seller C).buyerSide b Y = Y := by
  cases b
  ext x
  change x ∈ Y ∧ (() : Unit) = () ↔ x ∈ Y
  simp

private theorem rosterMarket_choiceS_eq_of_feasible (C : ChoiceFunction X) {Y : Set X}
    (hY : Set.InjOn seller Y) (i : S) :
    (rosterMarket seller C).choiceS i Y = (rosterMarket seller C).sellerSide i Y := by
  apply Set.Subset.antisymm ((rosterMarket seller C).choiceS_subset_sellerSide i Y)
  intro x hx
  obtain ⟨hxY, hxI⟩ := (rosterMarket seller C).mem_sellerSide.mp hx
  refine (mem_rosterMarket_choiceS_iff seller C).mpr ⟨hxY, hxI, ?_⟩
  intro y hyY hyI
  have hyx := hY hyY hxY (hyI.trans hxI.symm)
  subst y
  exact le_rfl

private theorem rosterMarket_indRational_iff_of_feasible (C : ChoiceFunction X) {Y : Set X}
    (hY : Set.InjOn seller Y) :
    (rosterMarket seller C).IndRational Y ↔ C Y = Y := by
  constructor
  · intro hIR
    have hB := hIR.1 ()
    rw [rosterMarket_buyerSide] at hB
    exact hB
  · intro hC
    refine ⟨?_, rosterMarket_choiceS_eq_of_feasible seller C hY⟩
    intro b
    rw [rosterMarket_buyerSide]
    exact hC

/-- Stable outcomes under a completion have the roster selected when all workers are represented. -/
theorem exists_rosterAssignment_of_stable {R : ChoiceFunction S} {C D : ChoiceFunction X}
    (hRoster : ∀ Y, seller '' (C Y) = R (seller '' Y))
    (hRSub : R.Substitutable) (hRIRC : R.Consistent)
    (hComp : C.IsCompletionOf seller D) {A : Set X}
    (hA : (rosterMarket seller D).Stable A) :
    ∃ a : RosterAssignment seller (R (Set.range seller)), a.terms = A := by
  have hFeas : Set.InjOn seller A :=
    hA.manyToOneFeasible _ (rosterMarket_sellersUnitDemand seller D)
  have hDA := (rosterMarket_indRational_iff_of_feasible seller D hFeas).mp hA.1
  have hCA : C A = A := (hComp.eq_of_injOn_menu hFeas).symm.trans hDA
  have hChooseA : R (seller '' A) = seller '' A := by
    rw [← hRoster, hCA]
  have hW : R (Set.range seller) ⊆ seller '' A := by
    intro i hi
    by_contra hiA
    obtain ⟨x, rfl⟩ := R.choose_subset _ hi
    have hxA : x ∉ A := fun hx ↦ hiA ⟨x, hx, rfl⟩
    have hFeasInsert := (Set.injOn_insert hxA).mpr ⟨hFeas, hiA⟩
    have hiC : seller x ∈ seller '' C (insert x A) := by
      rw [hRoster]
      exact hRSub.mem_of_subset (Set.image_subset_range seller _) hi
        ⟨x, Set.mem_insert _ _, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hiC
    have hyIns := C.choose_subset _ hy
    have hxy : y = x := hFeasInsert hyIns (Set.mem_insert _ _) hyx
    subst y
    have hxD : x ∈ D (insert x A) := by
      rw [hComp.eq_of_injOn_menu hFeasInsert]
      exact hy
    have hxS : x ∈ (rosterMarket seller D).choiceS (seller x) (insert x A) := by
      rw [rosterMarket_choiceS_eq_of_feasible seller D hFeasInsert]
      exact ⟨Set.mem_insert _ _, rfl⟩
    exact hxA ((rosterMarket seller D).not_blocking_singleton hA hxD hxS)
  exact RosterAssignment.exists_terms_eq hFeas
    (hChooseA.symm.trans (hRIRC hW (Set.image_subset_range seller A)))

variable [Finite X] {W : Set S}

private theorem rosterMarket_stable_terms_of_eq {C : ChoiceFunction X} (hIRC : C.Consistent)
    (A : RosterAssignment seller W) (hEq : C A.improvementMenu = A.terms) :
    (rosterMarket seller C).Stable A.terms := by
  let M := rosterMarket seller C
  have hAC : C A.improvementMenu ⊆ A.terms := hEq.le
  have hIR : M.IndRational A.terms :=
    (rosterMarket_indRational_iff_of_feasible seller C A.injOn_terms).mpr
      ((hIRC hAC A.terms_subset_improvementMenu).trans hEq)
  refine ⟨hIR, ?_⟩
  intro Z hZ
  have hZU : Z ⊆ A.improvementMenu := by
    intro x hx
    rw [← rosterMarket_toBuyers_terms seller C A]
    have hxS := hZ.2.2.2 (seller x) (show x ∈ M.sellerSide (seller x) Z from ⟨hx, rfl⟩)
    have hS := (rosterMarket_sellersUnitDemand seller C (seller x)).substitutable
      (rosterMarket_consistent_choiceS seller C (seller x))
    exact hS.mem_of_subset (Set.insert_subset_iff.mpr ⟨Or.inr hx, Set.subset_union_left⟩)
      hxS (Set.mem_insert _ _)
  have hChosen : C (A.terms ∪ Z) = A.terms :=
    (hIRC (hAC.trans Set.subset_union_left)
      (Set.union_subset A.terms_subset_improvementMenu hZU)).trans hEq
  obtain ⟨x, hx⟩ := hZ.1
  have hxB : x ∈ C (A.terms ∪ Z) := hZ.2.2.1 ()
    (show x ∈ M.buyerSide () Z from ⟨hx, rfl⟩)
  rw [hChosen] at hxB
  exact Set.disjoint_left.mp hZ.2.1 hx hxB

/-- A feasible-valued IRC hospital's stable assignments are its fixed choices from the
incumbent terms and all offers their workers would accept. -/
theorem rosterMarket_stable_terms_iff {C : ChoiceFunction X}
    (hFeas : ∀ Y, Set.InjOn seller (C Y)) (hIRC : C.Consistent)
    (A : RosterAssignment seller W) :
    (rosterMarket seller C).Stable A.terms ↔ C A.improvementMenu = A.terms := by
  refine ⟨?_, rosterMarket_stable_terms_of_eq seller hIRC A⟩
  intro hA
  let M := rosterMarket seller C
  let Z := C A.improvementMenu \ A.terms
  have hChoice : C (A.terms ∪ Z) = C A.improvementMenu := by
    apply hIRC
    · intro x hx
      by_cases hxA : x ∈ A.terms
      · exact Or.inl hxA
      · exact Or.inr ⟨hx, hxA⟩
    · exact Set.union_subset A.terms_subset_improvementMenu
        ((Set.sdiff_subset).trans (C.choose_subset _))
  have hSubset : C A.improvementMenu ⊆ A.terms := by
    intro x hx
    by_contra hxA
    have hxZ : x ∈ Z := ⟨hx, hxA⟩
    apply hA.2 Z
    refine ⟨⟨x, hxZ⟩, Set.disjoint_sdiff_left, ?_, ?_⟩
    · intro b y hy
      change y ∈ C (A.terms ∪ Z)
      rw [hChoice]
      exact hy.1.1
    · intro i y hy
      obtain ⟨hyZ, hyS⟩ := M.mem_sellerSide.mp hy
      have hyU : y ∈ A.improvementMenu := C.choose_subset _ hyZ.1
      rw [← rosterMarket_toBuyers_terms seller C A] at hyU
      have hySmall : y ∈ M.choiceS i (insert y A.terms) := by
        rw [← hyS]
        exact hyU
      have hSChoice := rosterMarket_consistent_choiceS seller C i
        (Y := A.terms ∪ Z) (Z := insert y A.terms)
        (by
          intro z hz
          have hzI := M.seller_eq_of_mem hz
          rcases (M.choiceS i).choose_subset _ hz with hzA | hzZ
          · exact Set.mem_insert_of_mem _ hzA
          · exact Set.mem_insert_iff.mpr (Or.inl
              (hFeas _ hzZ.1 hyZ.1 (hzI.trans hyS.symm))))
        (Set.insert_subset_iff.mpr ⟨Or.inr hyZ, Set.subset_union_left⟩)
      rwa [hSChoice] at hySmall
  have hCA := (rosterMarket_indRational_iff_of_feasible seller C A.injOn_terms).mp hA.1
  exact (hIRC hSubset A.terms_subset_improvementMenu).symm.trans hCA

/-- Under a substitutable IRC hospital rule, this stability test also applies
when hospital choices can contain several contracts of a worker. -/
theorem rosterMarket_stable_terms_iff_of_substitutable {D : ChoiceFunction X}
    (hSub : D.Substitutable) (hIRC : D.Consistent) (A : RosterAssignment seller W) :
    (rosterMarket seller D).Stable A.terms ↔ D A.improvementMenu = A.terms := by
  refine ⟨?_, rosterMarket_stable_terms_of_eq seller hIRC A⟩
  intro hA
  let M := rosterMarket seller D
  have hSellerIRC := rosterMarket_consistent_choiceS seller D
  have hMIRC : M.Consistent := ⟨fun _ ↦ hIRC, hSellerIRC⟩
  have hMSub : M.Substitutable :=
    ⟨fun _ ↦ hSub, (rosterMarket_sellersUnitDemand seller D).substitutable M hSellerIRC⟩
  have hEq : D A.improvementMenu = D A.terms := M.choiceB_eq_of_stable hMSub hMIRC hA ()
    Set.Subset.rfl A.terms_subset_improvementMenu (fun _ hy _ ↦
      (rosterMarket_toBuyers_terms seller D A).symm ▸ hy)
  exact hEq.trans
    ((rosterMarket_indRational_iff_of_feasible seller D A.injOn_terms).mp hA.1)

private theorem favourite_mem_terms_of_mem_improvementMenu {R : ChoiceFunction S} {x : X}
    (hxW : seller x ∈ R (Set.range seller))
    (hx : x ∈ (RosterAssignment.favourite
      (R.choose_subset (Set.range seller))).improvementMenu) :
    x ∈ (RosterAssignment.favourite (R.choose_subset (Set.range seller))).terms := by
  let i : R (Set.range seller) := ⟨seller x, hxW⟩
  let A := RosterAssignment.favourite (R.choose_subset (Set.range seller))
  have hLe : A i ≤ (⟨x, rfl⟩ : {x : X // seller x = i.1}) := hx i rfl
  have hGe := RosterAssignment.le_favourite_apply
    (R.choose_subset (Set.range seller)) i ⟨x, rfl⟩
  exact ⟨i, congrArg Subtype.val (le_antisymm hLe hGe)⟩

/-- Giving each selected worker their favourite term is stable under the original rule. -/
theorem rosterMarket_favourite_stable_original {R : ChoiceFunction S} {C : ChoiceFunction X}
    (hRoster : ∀ Y, seller '' (C Y) = R (seller '' Y)) (hRIRC : R.Consistent)
    (hFeas : ∀ Y, Set.InjOn seller (C Y)) (hCIRC : C.Consistent) :
    (rosterMarket seller C).Stable
      (RosterAssignment.favourite (R.choose_subset (Set.range seller))).terms := by
  let A := RosterAssignment.favourite (R.choose_subset (Set.range seller))
  apply (rosterMarket_stable_terms_iff seller hFeas hCIRC A).mpr
  have hW : R (Set.range seller) ⊆ seller '' A.improvementMenu :=
    A.image_terms.symm.le.trans (Set.image_mono A.terms_subset_improvementMenu)
  have hImage : seller '' C A.improvementMenu = R (Set.range seller) :=
    (hRoster _).trans (hRIRC hW (Set.image_subset_range seller _))
  have hSubset : C A.improvementMenu ⊆ A.terms := by
    intro x hx
    have hxW : seller x ∈ R (Set.range seller) := hImage ▸ ⟨x, hx, rfl⟩
    exact favourite_mem_terms_of_mem_improvementMenu seller hxW (C.choose_subset _ hx)
  exact (A.injOn_terms.image_eq_image_iff hSubset Set.Subset.rfl).mp
    (hImage.trans A.image_terms.symm)

/-- Giving each selected worker their favourite term is stable under every
substitutable completion. -/
theorem rosterMarket_favourite_stable {R : ChoiceFunction S} {C D : ChoiceFunction X}
    (hRoster : ∀ Y, seller '' (C Y) = R (seller '' Y)) (hRIRC : R.Consistent)
    (hComp : C.IsCompletionOf seller D) (hDSub : D.Substitutable) :
    (rosterMarket seller D).Stable
      (RosterAssignment.favourite (R.choose_subset (Set.range seller))).terms := by
  let A := RosterAssignment.favourite (R.choose_subset (Set.range seller))
  let M := rosterMarket seller D
  have hRosterA : seller '' C A.terms = R (Set.range seller) :=
    (hRoster _).trans ((congrArg R A.image_terms).trans
      (hRIRC.idempotent (Set.range seller)))
  have hCA : C A.terms = A.terms :=
    (A.injOn_terms.image_eq_image_iff (C.choose_subset _) Set.Subset.rfl).mp
      (hRosterA.trans A.image_terms.symm)
  have hDA : D A.terms = A.terms := (hComp.eq_of_injOn_menu A.injOn_terms).trans hCA
  have hSSub := (rosterMarket_sellersUnitDemand seller D).substitutable M
    (rosterMarket_consistent_choiceS seller D)
  apply Market.PairwiseStable.stable_of_substitutable M ⟨fun _ ↦ hDSub, hSSub⟩
  refine ⟨(rosterMarket_indRational_iff_of_feasible seller D A.injOn_terms).mpr hDA, ?_⟩
  intro x hx
  obtain ⟨hxA, hxB, hxS⟩ := M.blocks_singleton_iff.mp hx
  have hxU : x ∈ A.improvementMenu :=
    rosterMarket_toBuyers_terms seller D A ▸ hxS
  have hxW : seller x ∉ R (Set.range seller) := fun hi ↦
    hxA (favourite_mem_terms_of_mem_improvementMenu seller hi hxU)
  have hxImage : seller x ∉ seller '' A.terms := A.image_terms.symm ▸ hxW
  have hFeasInsert := (Set.injOn_insert hxA).mpr ⟨A.injOn_terms, hxImage⟩
  have hxC : x ∈ C (insert x A.terms) :=
    (hComp.eq_of_injOn_menu hFeasInsert) ▸ hxB
  have hW : R (Set.range seller) ⊆ seller '' insert x A.terms :=
    A.image_terms.symm.le.trans (Set.image_mono (Set.subset_insert _ _))
  have hImage : seller '' C (insert x A.terms) = R (Set.range seller) :=
    (hRoster _).trans (hRIRC hW (Set.image_subset_range seller _))
  exact hxW (hImage ▸ ⟨x, hxC, rfl⟩)

end MathEconLib.Matching
