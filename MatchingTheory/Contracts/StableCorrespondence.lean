import MatchingTheory.Contracts.Basic
import Mathlib.Order.FixedPoints

/-!
# Stable outcomes as deferred-acceptance fixed points

The generalized operator acts on `Set X × (Set X)ᵒᵈ`. Its first coordinate
contains contracts available to sellers; its second contains contracts
available to buyers. Thus `⊤ = (univ, ∅)` is the seller-proposing initial
state. Under substitutability and IRC, the greatest fixed point yields the
seller-optimal stable outcome, and the least fixed point yields the
buyer-optimal stable outcome.

Under substitutability and set-form IRC, `stateOf` and `outcomeOf` identify
stable outcomes with fixed points. Knaster–Tarski then gives existence.
These results require neither finiteness nor unit demand nor the law of
aggregate demand. The order dictionary and lattice API are in `Order`;
counting and finite convergence are in `RuralHospitals` and `Iteration`.

This operator uses contract-wise acceptance from `insert x Y`; it is not
merely the complement of the rejection set. The distinction matters for the
bijection between fixed points and stable outcomes.
-/

open Function OrderDual

universe u v w

variable {B : Type u} {S : Type v} {X : Type w}

namespace Market

variable (M : Market B S X)

/-! ### The generalized deferred acceptance operator -/

def toSellers (Xb : Set X) : Set X :=
  {x | x ∈ M.choiceB (M.buyer x) (insert x Xb)}

def toBuyers (Xs : Set X) : Set X :=
  {x | x ∈ M.choiceS (M.seller x) (insert x Xs)}

@[simp] lemma mem_toSellers {Xb : Set X} {x : X} :
    x ∈ M.toSellers Xb ↔ x ∈ M.choiceB (M.buyer x) (insert x Xb) := Iff.rfl

@[simp] lemma mem_toBuyers {Xs : Set X} {x : X} :
    x ∈ M.toBuyers Xs ↔ x ∈ M.choiceS (M.seller x) (insert x Xs) := Iff.rfl

theorem antitone_toSellers (hsub : ∀ b, (M.choiceB b).Substitutable) :
    Antitone M.toSellers := by
  intro Y Z hYZ x hx
  exact (hsub (M.buyer x)).mem_insert_of_subset hYZ hx

theorem antitone_toBuyers (hsub : ∀ s, (M.choiceS s).Substitutable) :
    Antitone M.toBuyers := by
  intro Y Z hYZ x hx
  exact (hsub (M.seller x)).mem_insert_of_subset hYZ hx

def daFun : Set X × (Set X)ᵒᵈ → Set X × (Set X)ᵒᵈ :=
  fun p => (M.toSellers (ofDual p.2), toDual (M.toBuyers p.1))

/-- Substitutability of all agents makes the operator monotone: the two
antitone half-lemmas plus `OrderDual` bookkeeping (which is definitional). -/
theorem monotone_daFun (hsub : M.Substitutable) : Monotone M.daFun := by
  intro p q h
  exact ⟨M.antitone_toSellers hsub.1 h.2, M.antitone_toBuyers hsub.2 h.1⟩

def daHom (hsub : M.Substitutable) :
    Set X × (Set X)ᵒᵈ →o Set X × (Set X)ᵒᵈ :=
  ⟨M.daFun, M.monotone_daFun hsub⟩

def outcomeOf (_M : Market B S X) (p : Set X × (Set X)ᵒᵈ) : Set X :=
  p.1 ∩ ofDual p.2

/-- The state carried by an outcome.  On stable outcomes this is a two-sided
inverse to `outcomeOf` (Lemma 2.1), and it is the *only* bridge the order
dictionary needs between set-level and state-level statements. -/
def stateOf (A : Set X) : Set X × (Set X)ᵒᵈ := M.daFun (A, toDual A)

@[simp] lemma stateOf_fst (A : Set X) : (M.stateOf A).1 = M.toSellers A := rfl

@[simp] lemma stateOf_snd (A : Set X) :
    (ofDual (M.stateOf A).2 : Set X) = M.toBuyers A := rfl

/-! ### Elementary consequences of stability -/

/-- A contract that both of its agents would take on top of `A` is already in
`A` — the singleton-blocking test, in the form used everywhere below. -/
theorem not_blocking_singleton {A : Set X} (hA : M.Stable A) {y : X}
    (hyB : y ∈ M.choiceB (M.buyer y) (insert y A))
    (hyS : y ∈ M.choiceS (M.seller y) (insert y A)) : y ∈ A := by
  by_contra hy
  exact hA.2 {y} (M.blocks_singleton_iff.mpr ⟨hy, hyB, hyS⟩)

theorem subset_toSellers_of_indRational {A : Set X} (h : M.IndRational A) :
    A ⊆ M.toSellers A := by
  intro x hx
  show x ∈ M.choiceB (M.buyer x) (insert x A)
  rw [Set.insert_eq_of_mem hx, h.1 (M.buyer x)]
  exact ⟨hx, rfl⟩

theorem subset_toBuyers_of_indRational {A : Set X} (h : M.IndRational A) :
    A ⊆ M.toBuyers A := by
  intro x hx
  show x ∈ M.choiceS (M.seller x) (insert x A)
  rw [Set.insert_eq_of_mem hx, h.2 (M.seller x)]
  exact ⟨hx, rfl⟩

/-- The IRC step at a stable outcome, buyer side: enlarging the menu from `U`
to `V` by contracts that the *sellers* would accept on top of `A` does not
change any buyer's choice.  Chernoff pushes a chosen contract down to
`insert y A`, singleton-blocking puts it in `A ⊆ U`, and IRC concludes. -/
theorem choiceB_eq_of_stable (hsub : M.Substitutable) (hcons : M.Consistent)
    {A : Set X} (hA : M.Stable A) (b : B) {U V : Set X}
    (hAU : A ⊆ U) (hUV : U ⊆ V) (hV : ∀ y ∈ V, y ∉ U → y ∈ M.toBuyers A) :
    M.choiceB b V = M.choiceB b U := by
  have hch : (M.choiceB b).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.1 b)
  have key : M.choiceB b V ⊆ U := by
    intro y hy
    by_contra hyU
    have hyV : y ∈ V := (M.choiceB b).choose_subset _ hy
    have hyS : y ∈ M.choiceS (M.seller y) (insert y A) := hV y hyV hyU
    have hins : insert y A ⊆ V := Set.insert_subset_iff.mpr ⟨hyV, hAU.trans hUV⟩
    have hyB : y ∈ M.choiceB b (insert y A) := hch hins ⟨hy, Set.mem_insert _ _⟩
    have hby : M.buyer y = b := M.buyer_eq_of_mem hy
    have hyA : y ∈ A :=
      M.not_blocking_singleton hA (by rw [hby]; exact hyB) hyS
    exact hyU (hAU hyA)
  exact (hcons.1 b key hUV).symm

theorem choiceS_eq_of_stable (hsub : M.Substitutable) (hcons : M.Consistent)
    {A : Set X} (hA : M.Stable A) (s : S) {U V : Set X}
    (hAU : A ⊆ U) (hUV : U ⊆ V) (hV : ∀ y ∈ V, y ∉ U → y ∈ M.toSellers A) :
    M.choiceS s V = M.choiceS s U := by
  have hch : (M.choiceS s).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.2 s)
  have key : M.choiceS s V ⊆ U := by
    intro y hy
    by_contra hyU
    have hyV : y ∈ V := (M.choiceS s).choose_subset _ hy
    have hyB : y ∈ M.choiceB (M.buyer y) (insert y A) := hV y hyV hyU
    have hins : insert y A ⊆ V := Set.insert_subset_iff.mpr ⟨hyV, hAU.trans hUV⟩
    have hyS : y ∈ M.choiceS s (insert y A) := hch hins ⟨hy, Set.mem_insert _ _⟩
    have hsy : M.seller y = s := M.seller_eq_of_mem hy
    have hyA : y ∈ A :=
      M.not_blocking_singleton hA hyB (by rw [hsy]; exact hyS)
    exact hyU (hAU hyA)
  exact (hcons.2 s key hUV).symm

theorem toSellers_eq_of_stable (hsub : M.Substitutable) (hcons : M.Consistent)
    {A W : Set X} (hA : M.Stable A) (hAW : A ⊆ W) (hW : W ⊆ M.toBuyers A) :
    M.toSellers W = M.toSellers A := by
  ext x
  have heq : M.choiceB (M.buyer x) (insert x W)
      = M.choiceB (M.buyer x) (insert x A) := by
    refine M.choiceB_eq_of_stable hsub hcons hA (M.buyer x)
      (Set.subset_insert _ _) (Set.insert_subset_insert hAW) ?_
    intro y hy hy'
    rcases Set.mem_insert_iff.mp hy with rfl | hy2
    · exact absurd (Set.mem_insert _ _) hy'
    · exact hW hy2
  show x ∈ M.choiceB (M.buyer x) (insert x W) ↔
    x ∈ M.choiceB (M.buyer x) (insert x A)
  rw [heq]

theorem toBuyers_eq_of_stable (hsub : M.Substitutable) (hcons : M.Consistent)
    {A W : Set X} (hA : M.Stable A) (hAW : A ⊆ W) (hW : W ⊆ M.toSellers A) :
    M.toBuyers W = M.toBuyers A := by
  ext x
  have heq : M.choiceS (M.seller x) (insert x W)
      = M.choiceS (M.seller x) (insert x A) := by
    refine M.choiceS_eq_of_stable hsub hcons hA (M.seller x)
      (Set.subset_insert _ _) (Set.insert_subset_insert hAW) ?_
    intro y hy hy'
    rcases Set.mem_insert_iff.mp hy with rfl | hy2
    · exact absurd (Set.mem_insert _ _) hy'
    · exact hW hy2
  show x ∈ M.choiceS (M.seller x) (insert x W) ↔
    x ∈ M.choiceS (M.seller x) (insert x A)
  rw [heq]

/-! ### Elementary consequences of being a fixed point -/

theorem toSellers_eq_of_isFixedPt {p : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) : M.toSellers (ofDual p.2) = p.1 :=
  congrArg Prod.fst hp

theorem toBuyers_eq_of_isFixedPt {p : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) : M.toBuyers p.1 = ofDual p.2 :=
  congrArg (fun q => ofDual q.2) hp

/-- At a fixed point, what a buyer chooses from the buyer-available set is
already part of the outcome.  (No substitutability, no IRC.) -/
theorem choiceB_subset_outcomeOf {p : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (b : B) :
    M.choiceB b (ofDual p.2) ⊆ M.outcomeOf p := by
  intro y hy
  have hyXb : y ∈ (ofDual p.2 : Set X) := (M.choiceB b).choose_subset _ hy
  have hby : M.buyer y = b := M.buyer_eq_of_mem hy
  have hys : y ∈ M.toSellers (ofDual p.2 : Set X) := by
    show y ∈ M.choiceB (M.buyer y) (insert y (ofDual p.2 : Set X))
    rw [Set.insert_eq_of_mem hyXb, hby]
    exact hy
  refine ⟨?_, hyXb⟩
  rw [← M.toSellers_eq_of_isFixedPt hp]
  exact hys

theorem choiceS_subset_outcomeOf {p : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (s : S) :
    M.choiceS s p.1 ⊆ M.outcomeOf p := by
  intro y hy
  have hyXs : y ∈ p.1 := (M.choiceS s).choose_subset _ hy
  have hsy : M.seller y = s := M.seller_eq_of_mem hy
  have hyb : y ∈ M.toBuyers p.1 := by
    show y ∈ M.choiceS (M.seller y) (insert y p.1)
    rw [Set.insert_eq_of_mem hyXs, hsy]
    exact hy
  refine ⟨hyXs, ?_⟩
  rw [← M.toBuyers_eq_of_isFixedPt hp]
  exact hyb

/-- Pure-IRC sandwich: any menu between the outcome and the buyer-available
set induces the same buyer choice. -/
theorem choiceB_eq_of_isFixedPt_sandwich (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.daFun p) (b : B) {V : Set X}
    (h1 : M.outcomeOf p ⊆ V) (h2 : V ⊆ (ofDual p.2 : Set X)) :
    M.choiceB b V = M.choiceB b (ofDual p.2) :=
  hcons.1 b ((M.choiceB_subset_outcomeOf hp b).trans h1) h2

theorem choiceS_eq_of_isFixedPt_sandwich (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.daFun p) (s : S) {V : Set X}
    (h1 : M.outcomeOf p ⊆ V) (h2 : V ⊆ p.1) :
    M.choiceS s V = M.choiceS s p.1 :=
  hcons.2 s ((M.choiceS_subset_outcomeOf hp s).trans h1) h2

/-- Chernoff + IRC at a fixed point: menus differing only in contracts drawn
from the buyer-available set induce the same buyer choice. -/
theorem choiceB_eq_of_isFixedPt (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.daFun p) (b : B) {U V : Set X}
    (hAU : M.outcomeOf p ⊆ U) (hUV : U ⊆ V) (hXbV : (ofDual p.2 : Set X) ⊆ V)
    (hVU : ∀ y ∈ V, y ∉ U → y ∈ (ofDual p.2 : Set X)) :
    M.choiceB b V = M.choiceB b U := by
  have hch : (M.choiceB b).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.1 b)
  have key : M.choiceB b V ⊆ U := by
    intro y hy
    by_contra hyU
    have hyV : y ∈ V := (M.choiceB b).choose_subset _ hy
    have hyXb : y ∈ (ofDual p.2 : Set X) := hVU y hyV hyU
    have hyC : y ∈ M.choiceB b (ofDual p.2 : Set X) := hch hXbV ⟨hy, hyXb⟩
    exact hyU (hAU (M.choiceB_subset_outcomeOf hp b hyC))
  exact (hcons.1 b key hUV).symm

theorem choiceS_eq_of_isFixedPt (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.daFun p) (s : S) {U V : Set X}
    (hAU : M.outcomeOf p ⊆ U) (hUV : U ⊆ V) (hXsV : p.1 ⊆ V)
    (hVU : ∀ y ∈ V, y ∉ U → y ∈ p.1) :
    M.choiceS s V = M.choiceS s U := by
  have hch : (M.choiceS s).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.2 s)
  have key : M.choiceS s V ⊆ U := by
    intro y hy
    by_contra hyU
    have hyV : y ∈ V := (M.choiceS s).choose_subset _ hy
    have hyXs : y ∈ p.1 := hVU y hyV hyU
    have hyC : y ∈ M.choiceS s p.1 := hch hXsV ⟨hy, hyXs⟩
    exact hyU (hAU (M.choiceS_subset_outcomeOf hp s hyC))
  exact (hcons.2 s key hUV).symm

/-! ### Lemma 2.1: fixed points ↔ stable outcomes -/

/-- Lemma 2.1, first half: the outcome of a fixed point is stable. -/
theorem stable_outcomeOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.daFun p) :
    M.Stable (M.outcomeOf p) := by
  have hAs : M.outcomeOf p ⊆ p.1 := fun x hx => hx.1
  have hAb : M.outcomeOf p ⊆ (ofDual p.2 : Set X) := fun x hx => hx.2
  -- Individual rationality: pure IRC via the sandwich lemma.
  have hIR : M.IndRational (M.outcomeOf p) := by
    constructor
    · intro b
      refine Set.Subset.antisymm
        (fun x hx => ⟨(M.choiceB b).choose_subset _ hx, M.buyer_eq_of_mem hx⟩) ?_
      rintro x ⟨hxA, hxb⟩
      have hxXb : x ∈ (ofDual p.2 : Set X) := hAb hxA
      have h1 : x ∈ M.choiceB (M.buyer x) (insert x (ofDual p.2 : Set X)) := by
        have h2 : x ∈ M.toSellers (ofDual p.2 : Set X) := by
          rw [M.toSellers_eq_of_isFixedPt hp]; exact hAs hxA
        exact h2
      rw [Set.insert_eq_of_mem hxXb, hxb] at h1
      rw [M.choiceB_eq_of_isFixedPt_sandwich hcons hp b (subset_refl _) hAb]
      exact h1
    · intro s
      refine Set.Subset.antisymm
        (fun x hx => ⟨(M.choiceS s).choose_subset _ hx, M.seller_eq_of_mem hx⟩) ?_
      rintro x ⟨hxA, hxs⟩
      have hxXs : x ∈ p.1 := hAs hxA
      have h1 : x ∈ M.choiceS (M.seller x) (insert x p.1) := by
        have h2 : x ∈ M.toBuyers p.1 := by
          rw [M.toBuyers_eq_of_isFixedPt hp]; exact hAb hxA
        exact h2
      rw [Set.insert_eq_of_mem hxXs, hxs] at h1
      rw [M.choiceS_eq_of_isFixedPt_sandwich hcons hp s (subset_refl _) hAs]
      exact h1
  -- No single blocking contract: such a contract would lie in both
  -- coordinates of the fixed point, hence in the outcome.
  have hno : ∀ z : X, ¬ M.Blocks (M.outcomeOf p) {z} := by
    intro z hz
    have hzA : z ∉ M.outcomeOf p := by
      have hd := hz.2.1
      rwa [Set.disjoint_singleton_left] at hd
    have hzB : z ∈ M.choiceB (M.buyer z) (insert z (M.outcomeOf p)) := by
      have h := hz.2.2.1 (M.buyer z)
        (⟨rfl, rfl⟩ : z ∈ M.buyerSide (M.buyer z) {z})
      rwa [Set.union_singleton] at h
    have hzS : z ∈ M.choiceS (M.seller z) (insert z (M.outcomeOf p)) := by
      have h := hz.2.2.2 (M.seller z)
        (⟨rfl, rfl⟩ : z ∈ M.sellerSide (M.seller z) {z})
      rwa [Set.union_singleton] at h
    have e1 : M.choiceB (M.buyer z) (insert z (ofDual p.2 : Set X))
        = M.choiceB (M.buyer z) (insert z (M.outcomeOf p)) := by
      refine M.choiceB_eq_of_isFixedPt hsub hcons hp (M.buyer z)
        (Set.subset_insert _ _) (Set.insert_subset_insert hAb)
        (Set.subset_insert _ _) ?_
      intro y hy hy'
      rcases Set.mem_insert_iff.mp hy with rfl | hy2
      · exact absurd (Set.mem_insert _ _) hy'
      · exact hy2
    have e2 : M.choiceS (M.seller z) (insert z p.1)
        = M.choiceS (M.seller z) (insert z (M.outcomeOf p)) := by
      refine M.choiceS_eq_of_isFixedPt hsub hcons hp (M.seller z)
        (Set.subset_insert _ _) (Set.insert_subset_insert hAs)
        (Set.subset_insert _ _) ?_
      intro y hy hy'
      rcases Set.mem_insert_iff.mp hy with rfl | hy2
      · exact absurd (Set.mem_insert _ _) hy'
      · exact hy2
    have hzXs : z ∈ p.1 := by
      rw [← M.toSellers_eq_of_isFixedPt hp]
      show z ∈ M.choiceB (M.buyer z) (insert z (ofDual p.2 : Set X))
      rw [e1]; exact hzB
    have hzXb : z ∈ (ofDual p.2 : Set X) := by
      rw [← M.toBuyers_eq_of_isFixedPt hp]
      show z ∈ M.choiceS (M.seller z) (insert z p.1)
      rw [e2]; exact hzS
    exact hzA ⟨hzXs, hzXb⟩
  have hps : M.PairwiseStable (M.outcomeOf p) := ⟨hIR, hno⟩
  exact hps.stable M hsub hcons

/-- Lemma 2.1, second half (existence). -/
theorem isFixedPt_daFun_of_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    IsFixedPt M.daFun (M.daFun (A, toDual A)) := by
  have hAb : A ⊆ M.toBuyers A := M.subset_toBuyers_of_indRational hA.1
  have hAs : A ⊆ M.toSellers A := M.subset_toSellers_of_indRational hA.1
  have h1 : M.toSellers (M.toBuyers A) = M.toSellers A :=
    M.toSellers_eq_of_stable hsub hcons hA hAb (subset_refl _)
  have h2 : M.toBuyers (M.toSellers A) = M.toBuyers A :=
    M.toBuyers_eq_of_stable hsub hcons hA hAs (subset_refl _)
  show (M.toSellers (M.toBuyers A), toDual (M.toBuyers (M.toSellers A)))
      = (M.toSellers A, toDual (M.toBuyers A))
  rw [h1, h2]

/-- Recovering a stable outcome from its canonical state needs no choice
regularity: individual rationality gives one inclusion and absence of singleton
blocks gives the other. -/
theorem outcomeOf_stateOf_of_stable {A : Set X} (hA : M.Stable A) :
    M.outcomeOf (M.stateOf A) = A := by
  show M.toSellers A ∩ M.toBuyers A = A
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hx1, hx2⟩
    exact M.not_blocking_singleton hA hx1 hx2
  · intro x hx
    exact ⟨M.subset_toSellers_of_indRational hA.1 hx,
           M.subset_toBuyers_of_indRational hA.1 hx⟩

/-- Compatibility form of `outcomeOf_stateOf_of_stable`, written using the
raw operator. The regularity hypotheses are unnecessary for this direction. -/
theorem outcomeOf_daFun_of_stable (_hsub : M.Substitutable)
    (_hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.outcomeOf (M.daFun (A, toDual A)) = A :=
  M.outcomeOf_stateOf_of_stable hA

/-- Lemma 2.1, second half (uniqueness). -/
theorem eq_of_isFixedPt_of_outcomeOf_eq (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} {p : Set X × (Set X)ᵒᵈ}
    (_hA : M.Stable A) (hp : IsFixedPt M.daFun p)
    (hout : M.outcomeOf p = A) :
    p = M.daFun (A, toDual A) := by
  have hAXb : A ⊆ (ofDual p.2 : Set X) := by
    rw [← hout]; exact fun x hx => hx.2
  have hAXs : A ⊆ p.1 := by
    rw [← hout]; exact fun x hx => hx.1
  have h1 : M.toSellers (ofDual p.2 : Set X) = M.toSellers A := by
    ext x
    have heq : M.choiceB (M.buyer x) (insert x (ofDual p.2 : Set X))
        = M.choiceB (M.buyer x) (insert x A) := by
      refine M.choiceB_eq_of_isFixedPt hsub hcons hp (M.buyer x) ?_
        (Set.insert_subset_insert hAXb) (Set.subset_insert _ _) ?_
      · rw [hout]; exact Set.subset_insert _ _
      · intro y hy hy'
        rcases Set.mem_insert_iff.mp hy with rfl | hy2
        · exact absurd (Set.mem_insert _ _) hy'
        · exact hy2
    show x ∈ M.choiceB (M.buyer x) (insert x (ofDual p.2 : Set X)) ↔
      x ∈ M.choiceB (M.buyer x) (insert x A)
    rw [heq]
  have h2 : M.toBuyers p.1 = M.toBuyers A := by
    ext x
    have heq : M.choiceS (M.seller x) (insert x p.1)
        = M.choiceS (M.seller x) (insert x A) := by
      refine M.choiceS_eq_of_isFixedPt hsub hcons hp (M.seller x) ?_
        (Set.insert_subset_insert hAXs) (Set.subset_insert _ _) ?_
      · rw [hout]; exact Set.subset_insert _ _
      · intro y hy hy'
        rcases Set.mem_insert_iff.mp hy with rfl | hy2
        · exact absurd (Set.mem_insert _ _) hy'
        · exact hy2
    show x ∈ M.choiceS (M.seller x) (insert x p.1) ↔
      x ∈ M.choiceS (M.seller x) (insert x A)
    rw [heq]
  have hp1 : p.1 = M.toSellers A := by
    rw [← M.toSellers_eq_of_isFixedPt hp, h1]
  have hp2 : p.2 = toDual (M.toBuyers A) := by
    show (ofDual p.2 : Set X) = M.toBuyers A
    rw [← M.toBuyers_eq_of_isFixedPt hp, h2]
  show p = (M.toSellers A, toDual (M.toBuyers A))
  calc p = (p.1, p.2) := rfl
    _ = (M.toSellers A, toDual (M.toBuyers A)) := by rw [hp1, hp2]

/-! #### The Lemma 2.1 round trips, in `stateOf` form

These interfaces use `stateOf A` in place of `daFun (A, toDual A)`.
The stronger `outcomeOf_stateOf_of_stable` above omits the regularity
hypotheses in the outcome round trip; the original interface remains below
for compatibility. -/

theorem isFixedPt_stateOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {A : Set X} (hA : M.Stable A) : IsFixedPt M.daFun (M.stateOf A) :=
  M.isFixedPt_daFun_of_stable hsub hcons hA

/-- Compatibility form of `outcomeOf_stateOf_of_stable`. -/
theorem outcomeOf_stateOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {A : Set X} (hA : M.Stable A) : M.outcomeOf (M.stateOf A) = A :=
  M.outcomeOf_daFun_of_stable hsub hcons hA

theorem stateOf_outcomeOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.daFun p) :
    M.stateOf (M.outcomeOf p) = p :=
  (M.eq_of_isFixedPt_of_outcomeOf_eq hsub hcons
    (M.stable_outcomeOf hsub hcons hp) hp rfl).symm

/-- Coordinate form of `stateOf_outcomeOf`: at a fixed point the
seller-available set is recomputable from the outcome alone. -/
theorem toSellers_outcomeOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.daFun p) :
    M.toSellers (M.outcomeOf p) = p.1 :=
  congrArg Prod.fst (M.stateOf_outcomeOf hsub hcons hp)

theorem toBuyers_outcomeOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.daFun p) :
    M.toBuyers (M.outcomeOf p) = (ofDual p.2 : Set X) :=
  congrArg (fun r : Set X × (Set X)ᵒᵈ => (ofDual r.2 : Set X))
    (M.stateOf_outcomeOf hsub hcons hp)

/-! ### Theorem 2.2 / 3.2: existence and the two extremal states -/

noncomputable def sellerOptimal (hsub : M.Substitutable) : Set X :=
  M.outcomeOf (OrderHom.gfp (M.daHom hsub))

noncomputable def buyerOptimal (hsub : M.Substitutable) : Set X :=
  M.outcomeOf (OrderHom.lfp (M.daHom hsub))

theorem isFixedPt_gfp_daHom (hsub : M.Substitutable) :
    IsFixedPt M.daFun (OrderHom.gfp (M.daHom hsub)) :=
  (M.daHom hsub).isGreatest_gfp.1

theorem le_gfp_daHom (hsub : M.Substitutable) {q : Set X × (Set X)ᵒᵈ}
    (hq : IsFixedPt M.daFun q) : q ≤ OrderHom.gfp (M.daHom hsub) :=
  (M.daHom hsub).isGreatest_gfp.2 hq

theorem isFixedPt_lfp_daHom (hsub : M.Substitutable) :
    IsFixedPt M.daFun (OrderHom.lfp (M.daHom hsub)) :=
  (M.daHom hsub).isLeast_lfp.1

theorem lfp_le_daHom (hsub : M.Substitutable) {q : Set X × (Set X)ᵒᵈ}
    (hq : IsFixedPt M.daFun q) : OrderHom.lfp (M.daHom hsub) ≤ q :=
  (M.daHom hsub).isLeast_lfp.2 hq

theorem stable_sellerOptimal (hsub : M.Substitutable) (hcons : M.Consistent) :
    M.Stable (M.sellerOptimal hsub) :=
  M.stable_outcomeOf hsub hcons (M.isFixedPt_gfp_daHom hsub)

theorem stable_buyerOptimal (hsub : M.Substitutable) (hcons : M.Consistent) :
    M.Stable (M.buyerOptimal hsub) :=
  M.stable_outcomeOf hsub hcons (M.isFixedPt_lfp_daHom hsub)

/-- Existence of stable outcomes (Hatfield–Milgrom/Fleiner). -/
theorem exists_stable (hsub : M.Substitutable) (hcons : M.Consistent) :
    ∃ A : Set X, M.Stable A :=
  ⟨M.sellerOptimal hsub, M.stable_sellerOptimal hsub hcons⟩

/-- On finite contract types, aggregate demand supplies the IRC hypothesis. -/
theorem exists_stable_of_sizeMonotone [Finite X]
    (hsub : M.Substitutable) (hload : M.SizeMonotone) :
    ∃ A : Set X, M.Stable A :=
  M.exists_stable hsub (M.consistent_of_substitutable_sizeMonotone hsub hload)

end Market
