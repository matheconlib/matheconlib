/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import MathEconLib.Matching.Classical.Marriage.Basic
import MathEconLib.Matching.Contracts.Basic

/-!
# Embedding marriage markets in the contracts model

The contracts are partner pairs: women are buyers and men are sellers.
The choice functions from `Marriage.Preferences` define the contracts market
without finiteness assumptions. Partial-matching graphs identify classical
individual rationality and stability with their contracts counterparts, and
individually rational outcomes recover partial matchings.

The choice/preference dictionary records exactly the needed side-specific
rationality hypothesis. Stable-matching existence via the contracts theorem
is proved separately in `Marriage.Existence`.
-/

namespace MathEconLib.Matching

open MathEconLib.Choice
open Function OrderDual

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}
variable (mkt : MarriageMarket M W)

/-! ## The induced contracts market -/

/-- The structural contracts market, without finiteness assumptions.
Women are buyers and men are sellers. -/
def toContractsMarket : Market W M (M × W) where
  buyer := Prod.snd
  seller := Prod.fst
  choiceB := mkt.inducedChoiceW
  choiceS := mkt.inducedChoiceM
  buyer_eq_of_mem := fun _ _ _ hp => mkt.snd_eq_of_mem_inducedChoiceW hp
  seller_eq_of_mem := fun _ _ _ hp => mkt.fst_eq_of_mem_inducedChoiceM hp

@[simp] theorem toContractsMarket_buyer (p : M × W) :
    mkt.toContractsMarket.buyer p = p.2 := rfl

@[simp] theorem toContractsMarket_seller (p : M × W) :
    mkt.toContractsMarket.seller p = p.1 := rfl

@[simp] theorem toContractsMarket_choiceB (w : W) :
    mkt.toContractsMarket.choiceB w = mkt.inducedChoiceW w := rfl

@[simp] theorem toContractsMarket_choiceS (m : M) :
    mkt.toContractsMarket.choiceS m = mkt.inducedChoiceM m := rfl

/-- Structural optional-partner choice is local on arbitrary partner types.
This uses the menu mapped along the partner embedding, without finiteness or an IRC hypothesis. -/
theorem local_toContractsMarket : mkt.toContractsMarket.Local := by
  constructor
  · intro w Y
    change (ChoiceFunction.ofOptionLinearOrder (mkt.prefW w)).map (partnerEmbeddingW w)
        (mkt.toContractsMarket.buyerSide w Y) =
      (ChoiceFunction.ofOptionLinearOrder (mkt.prefW w)).map (partnerEmbeddingW w) Y
    have hmenu : (partnerEmbeddingW w) ⁻¹' (mkt.toContractsMarket.buyerSide w Y) =
        (partnerEmbeddingW w) ⁻¹' Y := by
      ext m
      change ((m, w) ∈ Y ∧ w = w) ↔ (m, w) ∈ Y
      exact and_iff_left rfl
    exact congrArg (fun A : Set M =>
      (partnerEmbeddingW w) '' (ChoiceFunction.ofOptionLinearOrder (mkt.prefW w)) A) hmenu
  · intro m Y
    change (ChoiceFunction.ofOptionLinearOrder (mkt.prefM m)).map (partnerEmbeddingM m)
        (mkt.toContractsMarket.sellerSide m Y) =
      (ChoiceFunction.ofOptionLinearOrder (mkt.prefM m)).map (partnerEmbeddingM m) Y
    have hmenu : (partnerEmbeddingM m) ⁻¹' (mkt.toContractsMarket.sellerSide m Y) =
        (partnerEmbeddingM m) ⁻¹' Y := by
      ext w
      change ((m, w) ∈ Y ∧ m = m) ↔ (m, w) ∈ Y
      exact and_iff_left rfl
    exact congrArg (fun A : Set W =>
      (partnerEmbeddingM m) '' (ChoiceFunction.ofOptionLinearOrder (mkt.prefM m)) A) hmenu

theorem consistent_toContractsMarket [Finite M] [Finite W] : mkt.toContractsMarket.Consistent :=
  ⟨mkt.consistent_inducedChoiceW, mkt.consistent_inducedChoiceM⟩

theorem substitutable_toContractsMarket : mkt.toContractsMarket.Substitutable :=
  ⟨mkt.substitutable_inducedChoiceW, mkt.substitutable_inducedChoiceM⟩

theorem sizeMonotone_toContractsMarket : mkt.toContractsMarket.SizeMonotone :=
  ⟨mkt.sizeMonotone_inducedChoiceW, mkt.sizeMonotone_inducedChoiceM⟩

variable [Finite M] [Finite W]

/-! ## Individual rationality translation -/

omit [Finite M] in
/-- A man's individual rationality implies that he chooses his entire
side of the matching graph. -/
theorem choiceM_graphOf_eq_side
    {μ : M ≃. W} {m : M}
    (hIR : mkt.IndividuallyRationalForM μ m) :
    mkt.toContractsMarket.choiceS m (mkt.graphOf μ) =
      mkt.toContractsMarket.sellerSide m (mkt.graphOf μ) := by
  letI := Fintype.ofFinite W
  ext p
  rcases p with ⟨m', w⟩
  constructor
  · intro hp
    have hpY :=
      (mkt.toContractsMarket.choiceS m).choose_subset (mkt.graphOf μ) hp
    exact ⟨hpY, (mkt.mem_inducedChoiceM.mp hp).1⟩
  · rintro ⟨hpY, hm'⟩
    obtain rfl : m = m' := hm'.symm
    rw [mkt.toContractsMarket_choiceS, mkt.mem_inducedChoiceM_iff]
    have hμ : μ m = some w := mkt.mem_graphOf.mp hpY
    refine ⟨hpY, ?_, ?_⟩
    · have h : mkt.leM m none (μ m) := hIR
      rwa [hμ] at h
    · intro w' hw'
      letI := mkt.prefM m
      have hww' : w' = w := mkt.graphOf_rightUnique μ hw' hpY
      exact le_of_eq (congrArg Option.some hww')

omit [Finite W] in
/-- A woman's individual rationality implies that she chooses her entire
side of the matching graph. -/
theorem choiceW_graphOf_eq_side
    {μ : M ≃. W} {w : W}
    (hIR : mkt.IndividuallyRationalForW μ w) :
    mkt.toContractsMarket.choiceB w (mkt.graphOf μ) =
      mkt.toContractsMarket.buyerSide w (mkt.graphOf μ) := by
  letI := Fintype.ofFinite M
  ext p
  rcases p with ⟨m, w'⟩
  constructor
  · intro hp
    have hpY :=
      (mkt.toContractsMarket.choiceB w).choose_subset (mkt.graphOf μ) hp
    exact ⟨hpY, (mkt.mem_inducedChoiceW.mp hp).1⟩
  · rintro ⟨hpY, hw'⟩
    obtain rfl : w = w' := hw'.symm
    rw [mkt.toContractsMarket_choiceB, mkt.mem_inducedChoiceW_iff]
    have hμ : μ.symm w = some m := mkt.mem_graphOf_symm.mp hpY
    refine ⟨hpY, ?_, ?_⟩
    · have h : mkt.leW w none (μ.symm w) := hIR
      rwa [hμ] at h
    · intro m' hm'
      letI := mkt.prefW w
      have hmm' : m' = m := mkt.graphOf_leftUnique μ hm' hpY
      exact le_of_eq (congrArg Option.some hmm')

theorem individuallyRational_graphOf
    {μ : M ≃. W} (hIR : mkt.IndividuallyRational μ) :
    mkt.toContractsMarket.IndRational (mkt.graphOf μ) :=
  ⟨fun w => mkt.choiceW_graphOf_eq_side (hIR.2 w),
    fun m => mkt.choiceM_graphOf_eq_side (hIR.1 m)⟩

omit [Finite M] [Finite W] in
theorem individuallyRational_of_graphOf
    {μ : M ≃. W}
    (hIR : mkt.toContractsMarket.IndRational (mkt.graphOf μ)) :
    mkt.IndividuallyRational μ := by
  constructor
  · intro m
    change mkt.leM m none (μ m)
    letI := mkt.prefM m
    cases hμ : μ m with
    | none =>
        exact le_rfl
    | some w =>
        have hw : (m, w) ∈ mkt.graphOf μ :=
          mkt.mem_graphOf.mpr hμ
        have hwSide :
            (m, w) ∈ mkt.toContractsMarket.sellerSide m (mkt.graphOf μ) :=
          ⟨hw, rfl⟩
        have hwChoice :
            (m, w) ∈ mkt.toContractsMarket.choiceS m (mkt.graphOf μ) := by
          rw [hIR.2 m]
          exact hwSide
        exact (mkt.mem_inducedChoiceM_iff.mp hwChoice).2.1
  · intro w
    change mkt.leW w none (μ.symm w)
    letI := mkt.prefW w
    cases hμ : μ.symm w with
    | none =>
        exact le_rfl
    | some m =>
        have hw : (m, w) ∈ mkt.graphOf μ :=
          mkt.mem_graphOf_symm.mpr hμ
        have hwSide :
            (m, w) ∈ mkt.toContractsMarket.buyerSide w (mkt.graphOf μ) :=
          ⟨hw, rfl⟩
        have hwChoice :
            (m, w) ∈ mkt.toContractsMarket.choiceB w (mkt.graphOf μ) := by
          rw [hIR.1 w]
          exact hwSide
        exact (mkt.mem_inducedChoiceW_iff.mp hwChoice).2.1

theorem individuallyRational_iff_indRational_graphOf (μ : M ≃. W) :
    mkt.IndividuallyRational μ ↔
      mkt.toContractsMarket.IndRational (mkt.graphOf μ) :=
  ⟨mkt.individuallyRational_graphOf,
    mkt.individuallyRational_of_graphOf⟩

/-! ## Singleton acceptance and blocking pairs -/

omit [Finite M] [Finite W] in
/-- An individually rational man accepts a new contract precisely when
his side of the blocking condition holds. -/
theorem mem_choiceM_insert_graphOf_iff
    {μ : M ≃. W} {m : M} {w : W}
    (hIR : mkt.IndividuallyRationalForM μ m)
    (hnew : μ m ≠ some w) :
    (m, w) ∈ mkt.toContractsMarket.choiceS m
        (insert (m, w) (mkt.graphOf μ)) ↔
      mkt.BlocksM μ m w := by
  classical
  letI := mkt.prefM m
  unfold BlocksM
  rw [mkt.toContractsMarket_choiceS, mkt.mem_inducedChoiceM_iff]
  constructor
  · rintro ⟨-, hnone, hmax⟩
    have hle : μ m ≤ some w := by
      cases hμ : μ m with
      | none => exact hnone
      | some w' =>
          exact hmax w' (Set.mem_insert_iff.mpr
            (Or.inr (mkt.mem_graphOf.mpr hμ)))
    exact lt_of_le_of_ne hle hnew
  · intro hlt
    refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · exact le_trans hIR (le_of_lt hlt)
    · intro w' hw'
      rcases Set.mem_insert_iff.mp hw' with hw' | hw'
      · exact le_of_eq (congrArg Option.some (congrArg Prod.snd hw'))
      · have hμ : μ m = some w' := mkt.mem_graphOf.mp hw'
        have h := le_of_lt hlt
        rw [hμ] at h
        exact h

omit [Finite M] [Finite W] in
/-- An individually rational woman accepts a new contract precisely when
her side of the blocking condition holds. -/
theorem mem_choiceW_insert_graphOf_iff
    {μ : M ≃. W} {m : M} {w : W}
    (hIR : mkt.IndividuallyRationalForW μ w)
    (hnew : μ.symm w ≠ some m) :
    (m, w) ∈ mkt.toContractsMarket.choiceB w
        (insert (m, w) (mkt.graphOf μ)) ↔
      mkt.BlocksW μ w m := by
  classical
  letI := mkt.prefW w
  unfold BlocksW
  rw [mkt.toContractsMarket_choiceB, mkt.mem_inducedChoiceW_iff]
  constructor
  · rintro ⟨-, hnone, hmax⟩
    have hle : μ.symm w ≤ some m := by
      cases hμ : μ.symm w with
      | none => exact hnone
      | some m' =>
          exact hmax m' (Set.mem_insert_iff.mpr
            (Or.inr (mkt.mem_graphOf_symm.mpr hμ)))
    exact lt_of_le_of_ne hle hnew
  · intro hlt
    refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · exact le_trans hIR (le_of_lt hlt)
    · intro m' hm'
      rcases Set.mem_insert_iff.mp hm' with hm' | hm'
      · exact le_of_eq (congrArg Option.some (congrArg Prod.fst hm'))
      · have hμ : μ.symm w = some m' := mkt.mem_graphOf_symm.mp hm'
        have h := le_of_lt hlt
        rw [hμ] at h
        exact h

omit [Finite M] [Finite W] in
theorem blocks_singleton_graphOf_iff
    {μ : M ≃. W} (hIR : mkt.IndividuallyRational μ)
    {m : M} {w : W} :
    mkt.toContractsMarket.Blocks (mkt.graphOf μ) {(m, w)} ↔
      mkt.IsBlockingPair μ m w := by
  rw [mkt.toContractsMarket.blocks_singleton_iff]
  constructor
  · rintro ⟨hnew, hw, hm⟩
    have hnewM : μ m ≠ some w := fun h =>
      hnew (mkt.mem_graphOf.mpr h)
    have hnewW : μ.symm w ≠ some m := fun h =>
      hnew (mkt.mem_graphOf_symm.mpr h)
    exact ⟨
      (mkt.mem_choiceM_insert_graphOf_iff (hIR.1 m) hnewM).mp hm,
      (mkt.mem_choiceW_insert_graphOf_iff (hIR.2 w) hnewW).mp hw⟩
  · rintro ⟨hm, hw⟩
    have hnewM : μ m ≠ some w := by
      letI := mkt.prefM m
      exact ne_of_lt hm
    have hnewW : μ.symm w ≠ some m := by
      letI := mkt.prefW w
      exact ne_of_lt hw
    refine ⟨?_, ?_, ?_⟩
    · intro hmem
      exact hnewM (mkt.mem_graphOf.mp hmem)
    · exact
        (mkt.mem_choiceW_insert_graphOf_iff (hIR.2 w) hnewW).mpr hw
    · exact
        (mkt.mem_choiceM_insert_graphOf_iff (hIR.1 m) hnewM).mpr hm

/-- Classical stability is exactly stability of the matching graph in the
induced contracts market. -/
theorem isStableMatching_iff_stable_graphOf (μ : M ≃. W) :
    mkt.IsStableMatching μ ↔
      mkt.toContractsMarket.Stable (mkt.graphOf μ) := by
  let hsub := mkt.substitutable_toContractsMarket
  let hcons := mkt.consistent_toContractsMarket
  rw [← mkt.toContractsMarket.pairwiseStable_iff_stable hsub hcons]
  constructor
  · rintro ⟨hIR, hno⟩
    refine ⟨mkt.individuallyRational_graphOf hIR, ?_⟩
    rintro ⟨m, w⟩
    rw [mkt.blocks_singleton_graphOf_iff hIR]
    exact hno.1 m w
  · rintro ⟨hIRg, hno⟩
    have hIR : mkt.IndividuallyRational μ :=
      mkt.individuallyRational_of_graphOf hIRg
    refine ⟨hIR, ?_⟩
    apply (mkt.unblocked_iff_no_blockingPair μ).mpr
    intro m w
    rw [← mkt.blocks_singleton_graphOf_iff hIR]
    exact hno (m, w)

/-! ## Recovering a partial matching from a stable outcome -/

omit [Finite M] [Finite W] in
theorem seller_fiber_subsingleton {A : Set (M × W)}
    (hA : mkt.toContractsMarket.IndRational A) (m : M) :
    {w | (m, w) ∈ A}.Subsingleton := by
  intro w hw w' hw'
  have h1 : (m, w) ∈ mkt.toContractsMarket.choiceS m A := by
    rw [hA.2 m]
    exact ⟨hw, rfl⟩
  have h2 : (m, w') ∈ mkt.toContractsMarket.choiceS m A := by
    rw [hA.2 m]
    exact ⟨hw', rfl⟩
  have hp :=
    mkt.unitDemand_inducedChoiceM m A h1 h2
  exact congrArg Prod.snd hp

omit [Finite M] [Finite W] in
theorem buyer_fiber_subsingleton {A : Set (M × W)}
    (hA : mkt.toContractsMarket.IndRational A) (w : W) :
    {m | (m, w) ∈ A}.Subsingleton := by
  intro m hm m' hm'
  have h1 : (m, w) ∈ mkt.toContractsMarket.choiceB w A := by
    rw [hA.1 w]
    exact ⟨hm, rfl⟩
  have h2 : (m', w) ∈ mkt.toContractsMarket.choiceB w A := by
    rw [hA.1 w]
    exact ⟨hm', rfl⟩
  have hp :=
    mkt.unitDemand_inducedChoiceW w A h1 h2
  exact congrArg Prod.fst hp

set_option linter.unusedVariables false in
/-- The partner of `m` in outcome `A`, if any. This specializes the generic
optional value of a relation. -/
noncomputable def partnerMOf
    (mkt : MarriageMarket M W) (A : Set (M × W)) (m : M) : Option W :=
  PEquiv.relationValue (fun m w => (m, w) ∈ A) m

set_option linter.unusedVariables false in
/-- The partner of `w` in outcome `A`, if any. -/
noncomputable def partnerWOf
    (mkt : MarriageMarket M W) (A : Set (M × W)) (w : W) : Option M :=
  PEquiv.relationValue (fun w m => (m, w) ∈ A) w

omit [Finite M] [Finite W] in
theorem partnerMOf_eq_some_iff {A : Set (M × W)}
    (hsub : ∀ m, {w | (m, w) ∈ A}.Subsingleton)
    {m : M} {w : W} :
    mkt.partnerMOf A m = some w ↔ (m, w) ∈ A :=
  PEquiv.relationValue_eq_some_iff (hsub m)

omit [Finite W] [Finite M] in
theorem partnerWOf_eq_some_iff {A : Set (M × W)}
    (hsub : ∀ w, {m | (m, w) ∈ A}.Subsingleton)
    {m : M} {w : W} :
    mkt.partnerWOf A w = some m ↔ (m, w) ∈ A :=
  PEquiv.relationValue_eq_some_iff (hsub w)

/-- An individually rational unit-demand outcome induces a partial matching.
The economic hypotheses supply functionality; the reconstruction is generic. -/
noncomputable def matchingOfIndRational {A : Set (M × W)}
    (hA : mkt.toContractsMarket.IndRational A) : M ≃. W :=
  PEquiv.ofRelation (fun m w => (m, w) ∈ A)
    (mkt.seller_fiber_subsingleton hA) (mkt.buyer_fiber_subsingleton hA)

/-- A stable contracts outcome induces a partial matching. -/
noncomputable def matchingOfStable {A : Set (M × W)}
    (hA : mkt.toContractsMarket.Stable A) : M ≃. W :=
  mkt.matchingOfIndRational hA.1

omit [Finite M] [Finite W] in
@[simp] theorem graphOf_matchingOfIndRational {A : Set (M × W)}
    (hA : mkt.toContractsMarket.IndRational A) :
    mkt.graphOf (mkt.matchingOfIndRational hA) = A :=
  PEquiv.graph_ofRelation _ _ _

omit [Finite M] [Finite W] in
@[simp] theorem graphOf_matchingOfStable {A : Set (M × W)}
    (hA : mkt.toContractsMarket.Stable A) :
    mkt.graphOf (mkt.matchingOfStable hA) = A :=
  mkt.graphOf_matchingOfIndRational hA.1

theorem stable_matchingOfStable {A : Set (M × W)}
    (hA : mkt.toContractsMarket.Stable A) :
    mkt.IsStableMatching (mkt.matchingOfStable hA) := by
  rw [mkt.isStableMatching_iff_stable_graphOf,
    mkt.graphOf_matchingOfStable hA]
  exact hA

@[simp] theorem matchingOfStable_graphOf {μ : M ≃. W}
    (hμ : mkt.IsStableMatching μ) :
    mkt.matchingOfStable ((mkt.isStableMatching_iff_stable_graphOf μ).mp hμ) = μ := by
  apply mkt.graphOf_injective
  exact mkt.graphOf_matchingOfStable _

/-! ## Choice and pointwise preferences

The exact dictionary includes only individual rationality on the choosing
side. The forward preference implication has no rationality hypothesis:
choosing the graph already certifies acceptance of its assignments. -/

omit [Finite M] [Finite W] in
/-- An assignment belongs to every menu containing its matching graph. -/
theorem assignment_mem_menuM [Fintype W] {μ : M ≃. W} {Y : Set (M × W)}
    (hY : mkt.graphOf μ ⊆ Y) (m : M) : μ m ∈ mkt.menuM m Y := by
  cases hμ : μ m with
  | none => exact mkt.none_mem_menuM m Y
  | some w => exact mkt.some_mem_menuM.mpr (hY (mkt.mem_graphOf.mpr hμ))

omit [Finite M] [Finite W] in
/-- The symmetric assignment-membership statement for women. -/
theorem assignment_mem_menuW [Fintype M] {μ : M ≃. W} {Y : Set (M × W)}
    (hY : mkt.graphOf μ ⊆ Y) (w : W) : μ.symm w ∈ mkt.menuW w Y := by
  cases hμ : μ.symm w with
  | none => exact mkt.none_mem_menuW w Y
  | some m => exact mkt.some_mem_menuW.mpr (hY (mkt.mem_graphOf_symm.mpr hμ))

omit [Finite M] [Finite W] in
/-- Choosing exactly a man's assignment identifies his best option, including
when his assignment is the outside option. -/
theorem bestM_eq_of_choiceM_eq_side [Fintype W] {μ : M ≃. W} {Y : Set (M × W)} {m : M}
    (hchoice : mkt.inducedChoiceM m Y = mkt.toContractsMarket.sellerSide m (mkt.graphOf μ)) :
    mkt.bestM m Y = μ m := by
  cases hbest : mkt.bestM m Y with
  | none =>
      cases hμ : μ m with
      | none => rfl
      | some w =>
          have hc : (m, w) ∈ mkt.inducedChoiceM m Y := by
            rw [hchoice]
            exact ⟨mkt.mem_graphOf.mpr hμ, rfl⟩
          have hsome := (mkt.mem_inducedChoiceM.mp hc).2
          rw [hbest] at hsome
          cases hsome
  | some w =>
      have hc : (m, w) ∈ mkt.inducedChoiceM m Y :=
        mkt.mem_inducedChoiceM.mpr ⟨rfl, hbest.symm⟩
      rw [hchoice] at hc
      exact (mkt.mem_graphOf.mp hc.1).symm

omit [Finite M] [Finite W] in
/-- The symmetric identification of a woman's best option. -/
theorem bestW_eq_of_choiceW_eq_side [Fintype M] {μ : M ≃. W} {Y : Set (M × W)} {w : W}
    (hchoice : mkt.inducedChoiceW w Y = mkt.toContractsMarket.buyerSide w (mkt.graphOf μ)) :
    mkt.bestW w Y = μ.symm w := by
  cases hbest : mkt.bestW w Y with
  | none =>
      cases hμ : μ.symm w with
      | none => rfl
      | some m =>
          have hc : (m, w) ∈ mkt.inducedChoiceW w Y := by
            rw [hchoice]
            exact ⟨mkt.mem_graphOf_symm.mpr hμ, rfl⟩
          have hsome := (mkt.mem_inducedChoiceW.mp hc).2
          rw [hbest] at hsome
          cases hsome
  | some m =>
      have hc : (m, w) ∈ mkt.inducedChoiceW w Y :=
        mkt.mem_inducedChoiceW.mpr ⟨rfl, hbest.symm⟩
      rw [hchoice] at hc
      exact (mkt.mem_graphOf_symm.mp hc.1).symm

omit [Finite M] in
/-- Seller unanimity implies unanimous men's preference, without an IR assumption. -/
theorem menWeaklyPrefer_of_sellerChosen_graphOf {μ ν : M ≃. W}
    (hchosen : mkt.toContractsMarket.SellerChosen (mkt.graphOf μ) (mkt.graphOf ν)) :
    mkt.MenWeaklyPrefer μ ν := by
  letI := Fintype.ofFinite W
  intro m
  have hbest := mkt.bestM_eq_of_choiceM_eq_side (hchosen m)
  simpa only [hbest] using mkt.le_bestM_of_mem
    (mkt.assignment_mem_menuM (μ := ν)
      (Y := mkt.graphOf μ ∪ mkt.graphOf ν)
      Set.subset_union_right m)

omit [Finite W] in
/-- Buyer unanimity implies unanimous women's preference, without an IR assumption. -/
theorem womenWeaklyPrefer_of_buyerChosen_graphOf {μ ν : M ≃. W}
    (hchosen : mkt.toContractsMarket.BuyerChosen (mkt.graphOf μ) (mkt.graphOf ν)) :
    mkt.WomenWeaklyPrefer μ ν := by
  letI := Fintype.ofFinite M
  intro w
  have hbest := mkt.bestW_eq_of_choiceW_eq_side (hchosen w)
  simpa only [hbest] using mkt.le_bestW_of_mem
    (mkt.assignment_mem_menuW (μ := ν)
      (Y := mkt.graphOf μ ∪ mkt.graphOf ν)
      Set.subset_union_right w)

omit [Finite M] [Finite W] in
/-- Seller unanimity certifies men's individual rationality
for the chosen matching. -/
theorem individuallyRationalM_of_sellerChosen_graphOf {μ ν : M ≃. W}
    (hchosen :
      mkt.toContractsMarket.SellerChosen (mkt.graphOf μ) (mkt.graphOf ν)) :
    mkt.IndividuallyRationalM μ := by
  intro m
  change mkt.leM m none (μ m)
  letI := mkt.prefM m
  cases hμ : μ m with
  | none =>
      exact le_rfl
  | some w =>
      have hwChoice :
          (m, w) ∈ mkt.toContractsMarket.choiceS m
            (mkt.graphOf μ ∪ mkt.graphOf ν) := by
        rw [hchosen m]
        exact ⟨mkt.mem_graphOf.mpr hμ, rfl⟩
      exact (mkt.mem_inducedChoiceM_iff.mp hwChoice).2.1

omit [Finite M] [Finite W] in
/-- Buyer unanimity certifies women's individual rationality
for the chosen matching. -/
theorem individuallyRationalW_of_buyerChosen_graphOf {μ ν : M ≃. W}
    (hchosen :
      mkt.toContractsMarket.BuyerChosen (mkt.graphOf μ) (mkt.graphOf ν)) :
    mkt.IndividuallyRationalW μ := by
  intro w
  change mkt.leW w none (μ.symm w)
  letI := mkt.prefW w
  cases hμ : μ.symm w with
  | none =>
      exact le_rfl
  | some m =>
      have hwChoice :
          (m, w) ∈ mkt.toContractsMarket.choiceB w
            (mkt.graphOf μ ∪ mkt.graphOf ν) := by
        rw [hchosen w]
        exact ⟨mkt.mem_graphOf_symm.mpr hμ, rfl⟩
      exact (mkt.mem_inducedChoiceW_iff.mp hwChoice).2.1

omit [Finite M] in
/-- Compatibility form of the hypothesis-free forward dictionary. -/
theorem leM_of_sellerChosen_graphOf {μ ν : M ≃. W}
    (_hμ : mkt.IndividuallyRational μ) (_hν : mkt.IndividuallyRational ν)
    (hchosen : mkt.toContractsMarket.SellerChosen (mkt.graphOf μ) (mkt.graphOf ν)) (m : M) :
    mkt.leM m (ν m) (μ m) :=
  mkt.menWeaklyPrefer_of_sellerChosen_graphOf hchosen m

omit [Finite W] in
/-- Compatibility form of the hypothesis-free symmetric dictionary. -/
theorem leW_of_buyerChosen_graphOf {μ ν : M ≃. W}
    (_hμ : mkt.IndividuallyRational μ) (_hν : mkt.IndividuallyRational ν)
    (hchosen : mkt.toContractsMarket.BuyerChosen (mkt.graphOf μ) (mkt.graphOf ν)) (w : W) :
    mkt.leW w (ν.symm w) (μ.symm w) :=
  mkt.womenWeaklyPrefer_of_buyerChosen_graphOf hchosen w

omit [Finite M] in
/-- Unanimous classical preferences recover the seller-choice relation. -/
theorem sellerChosen_graphOf_of_individuallyRationalM {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRationalM μ) (h : mkt.MenWeaklyPrefer μ ν) :
    mkt.toContractsMarket.SellerChosen (mkt.graphOf μ) (mkt.graphOf ν) := by
  letI := Fintype.ofFinite W
  intro m
  letI := mkt.prefM m
  ext p
  rcases p with ⟨m', w⟩
  constructor
  · intro hp
    have hown : m' = m := (mkt.mem_inducedChoiceM.mp hp).1
    subst m'
    obtain ⟨hmem, hnone, hmax⟩ := mkt.mem_inducedChoiceM_iff.mp hp
    have hle : mkt.leM m (some w) (μ m) := by
      rcases hmem with hmem | hmem
      · exact le_of_eq (mkt.mem_graphOf.mp hmem).symm
      · simpa only [mkt.mem_graphOf.mp hmem] using h m
    have hge : mkt.leM m (μ m) (some w) := by
      cases hμm : μ m with
      | none => exact hnone
      | some w' => exact hmax w' (Or.inl (mkt.mem_graphOf.mpr hμm))
    exact ⟨mkt.mem_graphOf.mpr (le_antisymm hge hle), rfl⟩
  · rintro ⟨hp, hown⟩
    obtain rfl : m = m' := hown.symm
    have hμm := mkt.mem_graphOf.mp hp
    rw [mkt.toContractsMarket_choiceS, mkt.mem_inducedChoiceM_iff]
    refine ⟨Or.inl hp, ?_, ?_⟩
    · simpa only [IndividuallyRationalForM, hμm] using hμ m
    · intro w' hw'
      rcases hw' with hw' | hw'
      · exact le_of_eq ((mkt.mem_graphOf.mp hw').symm.trans hμm)
      · simpa only [mkt.mem_graphOf.mp hw', hμm] using h m

omit [Finite W] in
/-- Unanimous classical preferences recover the buyer-choice relation. -/
theorem buyerChosen_graphOf_of_individuallyRationalW {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRationalW μ) (h : mkt.WomenWeaklyPrefer μ ν) :
    mkt.toContractsMarket.BuyerChosen (mkt.graphOf μ) (mkt.graphOf ν) := by
  letI := Fintype.ofFinite M
  intro w
  letI := mkt.prefW w
  ext p
  rcases p with ⟨m, w'⟩
  constructor
  · intro hp
    have hown : w' = w := (mkt.mem_inducedChoiceW.mp hp).1
    subst w'
    obtain ⟨hmem, hnone, hmax⟩ := mkt.mem_inducedChoiceW_iff.mp hp
    have hle : mkt.leW w (some m) (μ.symm w) := by
      rcases hmem with hmem | hmem
      · exact le_of_eq (mkt.mem_graphOf_symm.mp hmem).symm
      · simpa only [mkt.mem_graphOf_symm.mp hmem] using h w
    have hge : mkt.leW w (μ.symm w) (some m) := by
      cases hμw : μ.symm w with
      | none => exact hnone
      | some m' => exact hmax m' (Or.inl (mkt.mem_graphOf_symm.mpr hμw))
    exact ⟨mkt.mem_graphOf_symm.mpr (le_antisymm hge hle), rfl⟩
  · rintro ⟨hp, hown⟩
    obtain rfl : w = w' := hown.symm
    have hμw := mkt.mem_graphOf_symm.mp hp
    rw [mkt.toContractsMarket_choiceB, mkt.mem_inducedChoiceW_iff]
    refine ⟨Or.inl hp, ?_, ?_⟩
    · simpa only [IndividuallyRationalForW, hμw] using hμ w
    · intro m' hm'
      rcases hm' with hm' | hm'
      · exact le_of_eq ((mkt.mem_graphOf_symm.mp hm').symm.trans hμw)
      · simpa only [mkt.mem_graphOf_symm.mp hm', hμw] using h w

omit [Finite M] in
/-- Exact seller dictionary, with the necessary IR condition made explicit. -/
theorem sellerChosen_graphOf_iff_individuallyRationalM_and_menWeaklyPrefer {μ ν : M ≃. W} :
    mkt.toContractsMarket.SellerChosen (mkt.graphOf μ) (mkt.graphOf ν) ↔
      mkt.IndividuallyRationalM μ ∧ mkt.MenWeaklyPrefer μ ν :=
  ⟨fun h => ⟨mkt.individuallyRationalM_of_sellerChosen_graphOf h,
      mkt.menWeaklyPrefer_of_sellerChosen_graphOf h⟩,
    fun h => mkt.sellerChosen_graphOf_of_individuallyRationalM h.1 h.2⟩

omit [Finite W] in
/-- Exact buyer dictionary, with the necessary IR condition made explicit. -/
theorem buyerChosen_graphOf_iff_individuallyRationalW_and_womenWeaklyPrefer {μ ν : M ≃. W} :
    mkt.toContractsMarket.BuyerChosen (mkt.graphOf μ) (mkt.graphOf ν) ↔
      mkt.IndividuallyRationalW μ ∧ mkt.WomenWeaklyPrefer μ ν :=
  ⟨fun h => ⟨mkt.individuallyRationalW_of_buyerChosen_graphOf h,
      mkt.womenWeaklyPrefer_of_buyerChosen_graphOf h⟩,
    fun h => mkt.buyerChosen_graphOf_of_individuallyRationalW h.1 h.2⟩

omit [Finite M] in
/-- Only the chosen matching's men's IR is needed for this order dictionary. -/
theorem sellerChosen_graphOf_iff_menWeaklyPrefer_of_individuallyRationalM {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRationalM μ) :
    mkt.toContractsMarket.SellerChosen (mkt.graphOf μ) (mkt.graphOf ν) ↔
      mkt.MenWeaklyPrefer μ ν :=
  ⟨mkt.menWeaklyPrefer_of_sellerChosen_graphOf,
    mkt.sellerChosen_graphOf_of_individuallyRationalM hμ⟩

omit [Finite W] in
/-- Only the chosen matching's women's IR is needed for this order dictionary. -/
theorem buyerChosen_graphOf_iff_womenWeaklyPrefer_of_individuallyRationalW {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRationalW μ) :
    mkt.toContractsMarket.BuyerChosen (mkt.graphOf μ) (mkt.graphOf ν) ↔
      mkt.WomenWeaklyPrefer μ ν :=
  ⟨mkt.womenWeaklyPrefer_of_buyerChosen_graphOf,
    mkt.buyerChosen_graphOf_of_individuallyRationalW hμ⟩

omit [Finite M] in
/-- Convenient compatibility specialization using full individual rationality. -/
theorem sellerChosen_graphOf_of_menWeaklyPrefer {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRational μ) (h : mkt.MenWeaklyPrefer μ ν) :
    mkt.toContractsMarket.SellerChosen (mkt.graphOf μ) (mkt.graphOf ν) :=
  mkt.sellerChosen_graphOf_of_individuallyRationalM hμ.1 h

omit [Finite W] in
/-- Convenient compatibility specialization using full individual rationality. -/
theorem buyerChosen_graphOf_of_womenWeaklyPrefer {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRational μ) (h : mkt.WomenWeaklyPrefer μ ν) :
    mkt.toContractsMarket.BuyerChosen (mkt.graphOf μ) (mkt.graphOf ν) :=
  mkt.buyerChosen_graphOf_of_individuallyRationalW hμ.2 h

omit [Finite M] in
/-- Compatibility dictionary for individually rational matchings. -/
theorem sellerChosen_graphOf_iff_menWeaklyPrefer {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRational μ) (_hν : mkt.IndividuallyRational ν) :
    mkt.toContractsMarket.SellerChosen (mkt.graphOf μ) (mkt.graphOf ν) ↔
      mkt.MenWeaklyPrefer μ ν :=
  mkt.sellerChosen_graphOf_iff_menWeaklyPrefer_of_individuallyRationalM hμ.1

omit [Finite W] in
/-- Compatibility dictionary for individually rational matchings. -/
theorem buyerChosen_graphOf_iff_womenWeaklyPrefer {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRational μ) (_hν : mkt.IndividuallyRational ν) :
    mkt.toContractsMarket.BuyerChosen (mkt.graphOf μ) (mkt.graphOf ν) ↔
      mkt.WomenWeaklyPrefer μ ν :=
  mkt.buyerChosen_graphOf_iff_womenWeaklyPrefer_of_individuallyRationalW hμ.2

end MarriageMarket

end MathEconLib.Matching
