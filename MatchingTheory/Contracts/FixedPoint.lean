/-
Matching with contracts, Layer 2: the fixed-point development
and structure of the stable matching lattice.
-/

import MatchingTheory.Contracts.Basic

import Mathlib.Order.FixedPoints
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card

/-!
# The generalized deferred acceptance operator

The survey's seller-superiority order `⊵` on pairs `(Xˢ, Xᵇ)` — contracts
available to sellers, contracts available to buyers — is realized *literally*
as the product order on `Set X × (Set X)ᵒᵈ`. Its top element `(univ, ∅)` is
the classical starting state of seller-proposing deferred acceptance, and the
greatest fixed point of the operator is the seller-optimal state.

With that encoding, mathlib's Knaster–Tarski development
(`Mathlib.Order.FixedPoints`: `OrderHom.lfp`/`OrderHom.gfp`, and the
`CompleteLattice` instance on `Function.fixedPoints f`) supplies existence and
the lattice theorem; the mathematical content of this file is **Lemma 2.1**,
the bijection between fixed points and stable outcomes, and the **order
dictionary** of §"The order dictionary", which identifies the lattice order
with unanimous seller choice and its reverse with unanimous buyer choice.

Everything is stated at many-to-many generality and, apart from the counting
and iteration sections at the bottom, is finiteness-free.

## Vocabulary

This file says *seller*/*buyer* where Hatfield–Milgrom say *doctor*/*hospital*:
sellers are the proposing side, `gfp` is the seller-optimal state, and
`StableOutcomes.sellerOptimalOutcome = ⊤`.

## Orientation convention

`⊤` is **seller-optimal** and **buyer-pessimal**; `⊥` is the reverse.  This is
forced by which coordinate carries the `ᵒᵈ` (the *buyer*-available set does),
and getting it backwards produces a pile of proofs that almost work.  Every
downstream result should be phrased through `sellerOptimalOutcome` /
`buyerOptimalOutcome`, never through bare `⊤`/`⊥`.

## No law of aggregate demand

Nothing in the fixed-point development, the order dictionary or the lattice
section uses `SizeMonotone`; substitutability and IRC suffice throughout.  LAD
appears only in the rural-hospitals section at the bottom, which is scheduled
to migrate to `RuralHospitals.lean`.  Do not let it creep upward.

## Main definitions

* `Market.toSellers`, `Market.toBuyers` — the two half-steps (Azevedo–Hatfield
  form: contract-wise membership tests `x ∈ C (insert x ·)`).
* `Market.daFun`, `Market.daHom` — the operator, raw and bundled.
* `Market.outcomeOf` — the outcome carried by a state: `Xˢ ∩ Xᵇ`.
* `Market.stateOf` — the state carried by an outcome: `daFun (A, toDual A)`.
* `Market.StableOutcomes` — the Knaster–Tarski lattice, carried by the fixed
  points; `state`, `outcome`, `ofStable` are its API.
* `Market.sellerOptimal`, `Market.buyerOptimal` — outcomes of `gfp`/`lfp`.

## Main statements

* `Market.monotone_daFun` — substitutability ⇒ monotonicity.
* `Market.stable_outcomeOf`, `Market.isFixedPt_daFun_of_stable`,
  `Market.stableEquivFixedPoints` — Lemma 2.1/4.1.
* `Market.le_iff_sellerChosen_outcomeOf`,
  `Market.le_iff_buyerChosen_outcomeOf` — the order dictionary; the lattice
  order *is* unanimous seller choice, and the reverse of unanimous buyer
  choice (opposition of interests).
* `Market.exists_stable`, `Market.sellerChosen_sellerOptimal` — Thm 2.2/3.2,
  now corollaries of the dictionary at `q := gfp`.
* `Market.ncard_buyerSide_eq_of_stable` — Thm 2.3/3.3 (rural hospitals);
  to migrate to `RuralHospitals.lean`.
* `OrderHom.exists_iterate_top_eq_gfp` — finite-lattice iteration (survey
  Observation 1); **upstream mathlib candidate**, parked here for now.
-/

open Function OrderDual

universe u v w

variable {B : Type u} {S : Type v} {X : Type w}

/-! ### A self-contained squeeze lemma for `ℕ`-valued sums

Replaces `Finset.sum_eq_sum_iff_of_le`, whose name/location has moved
between Mathlib versions.  Only `Finset.sum_lt_sum` is used, which is stable. -/

private theorem sum_eq_of_le_of_sum_le {ι : Type*} {s : Finset ι} {f g : ι → ℕ}
    (hfg : ∀ i ∈ s, f i ≤ g i) (hsum : ∑ i ∈ s, g i ≤ ∑ i ∈ s, f i) :
    ∀ i ∈ s, f i = g i := by
  intro i hi
  by_contra hne
  have hlt : ∑ j ∈ s, f j < ∑ j ∈ s, g j :=
    Finset.sum_lt_sum hfg ⟨i, hi, lt_of_le_of_ne (hfg i hi) hne⟩
  exact absurd hsum (not_le.mpr hlt)

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

/-- NOTE: `hsub`/`hcons` are genuinely unused here — the statement only needs
individual rationality and the singleton-blocking test.  They are kept (with
leading underscores) so that the whole `Lemma 2.1` family has a uniform
signature; every call site passes them positionally. -/
theorem outcomeOf_daFun_of_stable (_hsub : M.Substitutable)
    (_hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.outcomeOf (M.daFun (A, toDual A)) = A := by
  show M.toSellers A ∩ M.toBuyers A = A
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hx1, hx2⟩
    exact M.not_blocking_singleton hA hx1 hx2
  · intro x hx
    exact ⟨M.subset_toSellers_of_indRational hA.1 hx,
           M.subset_toBuyers_of_indRational hA.1 hx⟩

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

These are the same three theorems with `M.daFun (A, toDual A)` folded into
`M.stateOf A`.  Everything below quotes *these*, so that `rw` has a syntactic
target to hit. -/

theorem isFixedPt_stateOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {A : Set X} (hA : M.Stable A) : IsFixedPt M.daFun (M.stateOf A) :=
  M.isFixedPt_daFun_of_stable hsub hcons hA

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

/-! ### The order dictionary

The three statements

* `p ≤ q` in the state lattice,
* `SellerChosen (outcomeOf q) (outcomeOf p)` — every seller chooses their part
  of the `q`-outcome out of the union,
* `BuyerChosen (outcomeOf p) (outcomeOf q)` — every buyer chooses their part
  of the `p`-outcome out of the union,

are equivalent.  This is *opposition of interests*, and it is phrased through
choice functions rather than preference relations: at many-to-many generality
there is no primitive preference over sets, and `Cˢ(A ∪ A') = A'` is the form
that survives (and the form that feeds comparative statics).  The many-to-one
"each seller weakly prefers their contract in `A'`" reading is a unit-demand
specialisation and belongs downstream, not here — that is the Blair trap.

None of this uses `SizeMonotone`. -/

section OrderDictionary

variable (hsub : M.Substitutable) (hcons : M.Consistent)

include hsub hcons

/-- `→`, seller side.  Two IRC sandwiches at `q` and individual rationality. -/
theorem sellerChosen_outcomeOf_of_le {p q : Set X × (Set X)ᵒᵈ}
    (hq : IsFixedPt M.daFun q) (h : p ≤ q) :
    M.SellerChosen (M.outcomeOf q) (M.outcomeOf p) := by
  intro s
  have h1 : p.1 ⊆ q.1 := h.1
  have hop : M.outcomeOf p ⊆ q.1 := fun x hx => h1 hx.1
  have hoq : M.outcomeOf q ⊆ q.1 := fun x hx => hx.1
  have e1 : M.choiceS s (M.outcomeOf q ∪ M.outcomeOf p) = M.choiceS s q.1 :=
    M.choiceS_eq_of_isFixedPt_sandwich hcons hq s (fun x hx => Or.inl hx)
      (Set.union_subset hoq hop)
  have e2 : M.choiceS s (M.outcomeOf q) = M.choiceS s q.1 :=
    M.choiceS_eq_of_isFixedPt_sandwich hcons hq s (subset_refl _) hoq
  have hstable : M.Stable (M.outcomeOf q) := M.stable_outcomeOf hsub hcons hq
  show M.choiceS s (M.outcomeOf q ∪ M.outcomeOf p)
      = M.sellerSide s (M.outcomeOf q)
  rw [e1, ← e2]
  exact hstable.1.2 s

/-- `→`, buyer side.  The dual coordinate of `h` says exactly that the
`q`-outcome sits inside the contracts still available to buyers at `p`. -/
theorem buyerChosen_outcomeOf_of_le {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (h : p ≤ q) :
    M.BuyerChosen (M.outcomeOf p) (M.outcomeOf q) := by
  intro b
  have hA : M.Stable (M.outcomeOf p) := M.stable_outcomeOf hsub hcons hp
  have h2 : (ofDual q.2 : Set X) ⊆ (ofDual p.2 : Set X) := h.2
  have hb : M.toBuyers (M.outcomeOf p) = (ofDual p.2 : Set X) :=
    M.toBuyers_outcomeOf hsub hcons hp
  have key : ∀ y ∈ M.outcomeOf p ∪ M.outcomeOf q, y ∉ M.outcomeOf p →
      y ∈ M.toBuyers (M.outcomeOf p) := by
    intro y hy hyA
    rcases hy with h' | h'
    · exact absurd h' hyA
    · rw [hb]; exact h2 h'.2
  have e : M.choiceB b (M.outcomeOf p ∪ M.outcomeOf q)
      = M.choiceB b (M.outcomeOf p) :=
    M.choiceB_eq_of_stable hsub hcons hA b (subset_refl _)
      (fun x hx => Or.inl hx) key
  show M.choiceB b (M.outcomeOf p ∪ M.outcomeOf q)
      = M.buyerSide b (M.outcomeOf p)
  rw [e, hA.1.1 b]

/-- Opposition of interests, seller ⇒ buyer.  If a buyer chose some
`y ∈ A' \ A` out of `A ∪ A'`, Chernoff on *both* sides drops the menu to
`insert y A` and `y` blocks `A`.  Only `A` need be stable. -/
theorem buyerChosen_of_sellerChosen {A A' : Set X} (hA : M.Stable A)
    (h : M.SellerChosen A' A) : M.BuyerChosen A A' := by
  intro b
  have hchB : (M.choiceB b).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.1 b)
  have key : M.choiceB b (A ∪ A') ⊆ A := by
    intro y hy
    by_contra hyA
    have hyU : y ∈ A ∪ A' := (M.choiceB b).choose_subset _ hy
    have hyA' : y ∈ A' := hyU.resolve_left hyA
    have hby : M.buyer y = b := M.buyer_eq_of_mem hy
    have hins : insert y A ⊆ A ∪ A' :=
      Set.insert_subset_iff.mpr ⟨Or.inr hyA', fun x hx => Or.inl hx⟩
    have hyB : y ∈ M.choiceB (M.buyer y) (insert y A) := by
      rw [hby]; exact hchB hins ⟨hy, Set.mem_insert _ _⟩
    have hchS : (M.choiceS (M.seller y)).Chernoff :=
      ChoiceFunction.substitutable_iff_chernoff.mp (hsub.2 (M.seller y))
    have hyS0 : y ∈ M.choiceS (M.seller y) (A' ∪ A) := by
      rw [h (M.seller y)]; exact ⟨hyA', rfl⟩
    have hins' : insert y A ⊆ A' ∪ A :=
      Set.insert_subset_iff.mpr ⟨Or.inl hyA', fun x hx => Or.inr hx⟩
    have hyS : y ∈ M.choiceS (M.seller y) (insert y A) :=
      hchS hins' ⟨hyS0, Set.mem_insert _ _⟩
    exact hyA (M.not_blocking_singleton hA hyB hyS)
  show M.choiceB b (A ∪ A') = M.buyerSide b A
  rw [← hcons.1 b key (fun x hx => Or.inl hx), hA.1.1 b]

/-- Opposition of interests, buyer ⇒ seller. -/
theorem sellerChosen_of_buyerChosen {A A' : Set X} (hA' : M.Stable A')
    (h : M.BuyerChosen A A') : M.SellerChosen A' A := by
  intro s
  have hchS : (M.choiceS s).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.2 s)
  have key : M.choiceS s (A' ∪ A) ⊆ A' := by
    intro y hy
    by_contra hyA'
    have hyU : y ∈ A' ∪ A := (M.choiceS s).choose_subset _ hy
    have hyA : y ∈ A := hyU.resolve_left hyA'
    have hsy : M.seller y = s := M.seller_eq_of_mem hy
    have hins : insert y A' ⊆ A' ∪ A :=
      Set.insert_subset_iff.mpr ⟨Or.inr hyA, fun x hx => Or.inl hx⟩
    have hyS : y ∈ M.choiceS (M.seller y) (insert y A') := by
      rw [hsy]; exact hchS hins ⟨hy, Set.mem_insert _ _⟩
    have hchB : (M.choiceB (M.buyer y)).Chernoff :=
      ChoiceFunction.substitutable_iff_chernoff.mp (hsub.1 (M.buyer y))
    have hyB0 : y ∈ M.choiceB (M.buyer y) (A ∪ A') := by
      rw [h (M.buyer y)]; exact ⟨hyA, rfl⟩
    have hins' : insert y A' ⊆ A ∪ A' :=
      Set.insert_subset_iff.mpr ⟨Or.inl hyA, fun x hx => Or.inr hx⟩
    have hyB : y ∈ M.choiceB (M.buyer y) (insert y A') :=
      hchB hins' ⟨hyB0, Set.mem_insert _ _⟩
    exact hyA' (M.not_blocking_singleton hA' hyB hyS)
  show M.choiceS s (A' ∪ A) = M.sellerSide s A'
  rw [← hcons.2 s key (fun x hx => Or.inl hx), hA'.1.2 s]

/-- `←`, buyer coordinate.  Substitutability rejects all of `A \ A'` from
`A ∪ A'` and hence from any larger menu; IRC then collapses
`Cˢ(x + (A' ∪ A))` to `Cˢ(x + A')`, and one Chernoff step lands in
`insert x A`.  No stability is used. -/
theorem toBuyers_subset_of_sellerChosen {A A' : Set X}
    (h : M.SellerChosen A' A) : M.toBuyers A' ⊆ M.toBuyers A := by
  intro x hx
  have hxA' : x ∈ M.choiceS (M.seller x) (insert x A') := hx
  have hch : (M.choiceS (M.seller x)).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.2 (M.seller x))
  have hkey : M.choiceS (M.seller x) (insert x (A' ∪ A)) ⊆ insert x A' := by
    intro y hy
    rcases eq_or_ne y x with rfl | hyx
    · exact Set.mem_insert _ _
    · have hyW : y ∈ insert x (A' ∪ A) :=
        (M.choiceS (M.seller x)).choose_subset _ hy
      have hyU : y ∈ A' ∪ A := (Set.mem_insert_iff.mp hyW).resolve_left hyx
      have hy' : y ∈ M.choiceS (M.seller x) (A' ∪ A) :=
        hch (Set.subset_insert _ _) ⟨hy, hyU⟩
      rw [h (M.seller x)] at hy'
      exact Set.mem_insert_of_mem _ hy'.1
  have e : M.choiceS (M.seller x) (insert x A')
      = M.choiceS (M.seller x) (insert x (A' ∪ A)) :=
    hcons.2 (M.seller x) hkey (Set.insert_subset_insert (fun y hy => Or.inl hy))
  have hxW : x ∈ M.choiceS (M.seller x) (insert x (A' ∪ A)) := by
    rw [← e]; exact hxA'
  show x ∈ M.choiceS (M.seller x) (insert x A)
  exact hch (Set.insert_subset_insert (fun y hy => Or.inr hy))
    ⟨hxW, Set.mem_insert _ _⟩

/-- `←`, seller coordinate: the mirror image. -/
theorem toSellers_subset_of_buyerChosen {A A' : Set X}
    (h : M.BuyerChosen A A') : M.toSellers A ⊆ M.toSellers A' := by
  intro x hx
  have hxA : x ∈ M.choiceB (M.buyer x) (insert x A) := hx
  have hch : (M.choiceB (M.buyer x)).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.1 (M.buyer x))
  have hkey : M.choiceB (M.buyer x) (insert x (A ∪ A')) ⊆ insert x A := by
    intro y hy
    rcases eq_or_ne y x with rfl | hyx
    · exact Set.mem_insert _ _
    · have hyW : y ∈ insert x (A ∪ A') :=
        (M.choiceB (M.buyer x)).choose_subset _ hy
      have hyU : y ∈ A ∪ A' := (Set.mem_insert_iff.mp hyW).resolve_left hyx
      have hy' : y ∈ M.choiceB (M.buyer x) (A ∪ A') :=
        hch (Set.subset_insert _ _) ⟨hy, hyU⟩
      rw [h (M.buyer x)] at hy'
      exact Set.mem_insert_of_mem _ hy'.1
  have e : M.choiceB (M.buyer x) (insert x A)
      = M.choiceB (M.buyer x) (insert x (A ∪ A')) :=
    hcons.1 (M.buyer x) hkey (Set.insert_subset_insert (fun y hy => Or.inl hy))
  have hxW : x ∈ M.choiceB (M.buyer x) (insert x (A ∪ A')) := by
    rw [← e]; exact hxA
  show x ∈ M.choiceB (M.buyer x) (insert x A')
  exact hch (Set.insert_subset_insert (fun y hy => Or.inr hy))
    ⟨hxW, Set.mem_insert _ _⟩

/-- `←`: unanimous seller choice implies the state inequality. -/
theorem le_of_sellerChosen_outcomeOf {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (hq : IsFixedPt M.daFun q)
    (h : M.SellerChosen (M.outcomeOf q) (M.outcomeOf p)) : p ≤ q := by
  have hA : M.Stable (M.outcomeOf p) := M.stable_outcomeOf hsub hcons hp
  have hbc : M.BuyerChosen (M.outcomeOf p) (M.outcomeOf q) :=
    M.buyerChosen_of_sellerChosen hsub hcons hA h
  have h1 : M.toSellers (M.outcomeOf p) ⊆ M.toSellers (M.outcomeOf q) :=
    M.toSellers_subset_of_buyerChosen hsub hcons hbc
  have h2 : M.toBuyers (M.outcomeOf q) ⊆ M.toBuyers (M.outcomeOf p) :=
    M.toBuyers_subset_of_sellerChosen hsub hcons h
  refine ⟨?_, ?_⟩
  · rw [← M.toSellers_outcomeOf hsub hcons hp,
      ← M.toSellers_outcomeOf hsub hcons hq]
    exact h1
  · show (ofDual q.2 : Set X) ⊆ (ofDual p.2 : Set X)
    rw [← M.toBuyers_outcomeOf hsub hcons hp,
      ← M.toBuyers_outcomeOf hsub hcons hq]
    exact h2

/-- **The order dictionary, seller form.**  The lattice order *is* unanimous
seller choice. -/
theorem le_iff_sellerChosen_outcomeOf {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (hq : IsFixedPt M.daFun q) :
    p ≤ q ↔ M.SellerChosen (M.outcomeOf q) (M.outcomeOf p) :=
  ⟨M.sellerChosen_outcomeOf_of_le hsub hcons hq,
   M.le_of_sellerChosen_outcomeOf hsub hcons hp hq⟩

/-- **The order dictionary, buyer form.**  The same order is the *reverse* of
unanimous buyer choice. -/
theorem le_iff_buyerChosen_outcomeOf {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (hq : IsFixedPt M.daFun q) :
    p ≤ q ↔ M.BuyerChosen (M.outcomeOf p) (M.outcomeOf q) :=
  ⟨M.buyerChosen_outcomeOf_of_le hsub hcons hp,
   fun h => M.le_of_sellerChosen_outcomeOf hsub hcons hp hq
     (M.sellerChosen_of_buyerChosen hsub hcons
       (M.stable_outcomeOf hsub hcons hq) h)⟩

/-- Opposition of interests, packaged: on stable outcomes the two unanimity
statements are the same statement. -/
theorem sellerChosen_iff_buyerChosen {A A' : Set X} (hA : M.Stable A)
    (hA' : M.Stable A') : M.SellerChosen A' A ↔ M.BuyerChosen A A' :=
  ⟨M.buyerChosen_of_sellerChosen hsub hcons hA,
   M.sellerChosen_of_buyerChosen hsub hcons hA'⟩

end OrderDictionary

/-! ### The extremal outcomes

Seller-optimality and buyer-pessimality of `gfp` (and the duals at `lfp`) are
now instances of the dictionary at `q := gfp`, not separate arguments. -/

theorem sellerChosen_sellerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.SellerChosen (M.sellerOptimal hsub) A := by
  have hp : IsFixedPt M.daFun (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.sellerChosen_outcomeOf_of_le hsub hcons
    (M.isFixedPt_gfp_daHom hsub) (M.le_gfp_daHom hsub hp)
  rw [M.outcomeOf_stateOf hsub hcons hA] at h
  exact h

/-- Buyer-pessimality of the seller-optimal outcome: every stable `A` is
buyer-chosen over it. -/
theorem buyerChosen_sellerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.BuyerChosen A (M.sellerOptimal hsub) := by
  have hp : IsFixedPt M.daFun (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.buyerChosen_outcomeOf_of_le hsub hcons hp
    (M.le_gfp_daHom hsub hp)
  rw [M.outcomeOf_stateOf hsub hcons hA] at h
  exact h

theorem buyerChosen_buyerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.BuyerChosen (M.buyerOptimal hsub) A := by
  have hq : IsFixedPt M.daFun (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.buyerChosen_outcomeOf_of_le hsub hcons
    (M.isFixedPt_lfp_daHom hsub) (M.lfp_le_daHom hsub hq)
  rw [M.outcomeOf_stateOf hsub hcons hA] at h
  exact h

theorem sellerChosen_buyerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.SellerChosen A (M.buyerOptimal hsub) := by
  have hq : IsFixedPt M.daFun (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.sellerChosen_outcomeOf_of_le hsub hcons hq
    (M.lfp_le_daHom hsub hq)
  rw [M.outcomeOf_stateOf hsub hcons hA] at h
  exact h

/-! ### The lattice of stable outcomes

The carrier is the fixed-point set itself, so that mathlib's Knaster–Tarski
`CompleteLattice` instance is inherited verbatim and `≤` is *definitionally*
the state order (`StableOutcomes.le_iff_state_le` is `Iff.rfl`).  The
alternative — carrying `{A : Set X // M.Stable A}` and transporting the
lattice along `stableEquivFixedPoints` — would require a hand-rolled
`Equiv.completeLattice` (mathlib has none) and would demote the order to a
propositional characterization.  Nothing is lost: `outcome` is injective by
Lemma 2.1, so this type *is* the type of stable outcomes.

The lattice operations are deliberately left opaque; every statement below
goes through `IsLUB`/`IsGLB`-style reasoning or through `le_antisymm`, never
through the definition of `⊔`.  See the section after this one for what is
and is not known about the concrete operations. -/

/-- The Knaster–Tarski lattice of stable outcomes, carried by the fixed points
of the deferred-acceptance operator.  Reducible, so that the `CompleteLattice`
instance on `fixedPoints` applies. -/
abbrev StableOutcomes (M : Market B S X) (hsub : M.Substitutable) : Type w :=
  fixedPoints (M.daHom hsub)

/-- Package a stable outcome as a lattice element. -/
def ofStable (hsub : M.Substitutable) (hcons : M.Consistent) {A : Set X}
    (hA : M.Stable A) : M.StableOutcomes hsub :=
  ⟨M.stateOf A, M.isFixedPt_stateOf hsub hcons hA⟩

section StableOutcomesAPI

variable {M}

namespace StableOutcomes

variable {hsub : M.Substitutable}

/-- The state of a lattice element. -/
def state (A : M.StableOutcomes hsub) : Set X × (Set X)ᵒᵈ := A.1

theorem isFixedPt (A : M.StableOutcomes hsub) : IsFixedPt M.daFun A.state := A.2

/-- The outcome of a lattice element. -/
def outcome (A : M.StableOutcomes hsub) : Set X := M.outcomeOf A.state

theorem stable (A : M.StableOutcomes hsub) (hcons : M.Consistent) :
    M.Stable A.outcome :=
  M.stable_outcomeOf hsub hcons A.isFixedPt

theorem state_eq_stateOf (A : M.StableOutcomes hsub) (hcons : M.Consistent) :
    A.state = M.stateOf A.outcome :=
  (M.stateOf_outcomeOf hsub hcons A.isFixedPt).symm

/-- The lattice order *is* the state order.

DEVNOTE: `Iff.rfl` assumes mathlib's `fixedPoints.completeLattice` carries the
`Subtype` partial order, which it does today.  If that ever changes, the fix
is `Subtype.coe_le_coe.symm` and nothing downstream moves. -/
@[simp] theorem le_iff_state_le {A A' : M.StableOutcomes hsub} :
    A ≤ A' ↔ A.state ≤ A'.state := Iff.rfl

theorem state_injective :
    Function.Injective (fun A : M.StableOutcomes hsub => A.state) :=
  fun _ _ h => Subtype.ext h

theorem outcome_injective (hcons : M.Consistent) :
    Function.Injective (fun A : M.StableOutcomes hsub => A.outcome) := by
  intro A A' hout
  apply state_injective
  calc
    A.state = M.stateOf A.outcome := A.state_eq_stateOf hcons
    _ = M.stateOf A'.outcome := congrArg M.stateOf hout
    _ = A'.state := (A'.state_eq_stateOf hcons).symm

/-- The order dictionary on the lattice: `≤` is unanimous seller choice. -/
theorem le_iff_sellerChosen (hcons : M.Consistent)
    {A A' : M.StableOutcomes hsub} :
    A ≤ A' ↔ M.SellerChosen A'.outcome A.outcome :=
  M.le_iff_sellerChosen_outcomeOf hsub hcons A.isFixedPt A'.isFixedPt

/-- …and the reverse of unanimous buyer choice. -/
theorem le_iff_buyerChosen (hcons : M.Consistent)
    {A A' : M.StableOutcomes hsub} :
    A ≤ A' ↔ M.BuyerChosen A.outcome A'.outcome :=
  M.le_iff_buyerChosen_outcomeOf hsub hcons A.isFixedPt A'.isFixedPt

end StableOutcomes

end StableOutcomesAPI

/-- Lemma 2.1, packaged as an equivalence with the lattice carrier. -/
noncomputable def stableEquivFixedPoints (hsub : M.Substitutable)
    (hcons : M.Consistent) :
    {A : Set X // M.Stable A} ≃ M.StableOutcomes hsub where
  toFun A := M.ofStable hsub hcons A.2
  invFun p := ⟨p.outcome, p.stable hcons⟩
  left_inv A := Subtype.ext (M.outcomeOf_stateOf hsub hcons A.2)
  right_inv p := Subtype.ext (M.stateOf_outcomeOf hsub hcons p.isFixedPt)

@[simp] theorem outcome_ofStable (hsub : M.Substitutable) (hcons : M.Consistent)
    {A : Set X} (hA : M.Stable A) :
    (M.ofStable hsub hcons hA).outcome = A :=
  M.outcomeOf_stateOf hsub hcons hA

/-! #### Orientation

`⊤` is seller-optimal and buyer-pessimal.  This is the one fact in the file
that is a coin flip fixed by which coordinate carries the `ᵒᵈ`; state it once,
here, and route every downstream result through the two abbreviations rather
than through bare `⊤`/`⊥`. -/

/-- The **seller-optimal** stable outcome: the top of the lattice. -/
abbrev sellerOptimalOutcome (M : Market B S X) (hsub : M.Substitutable) :
    M.StableOutcomes hsub := ⊤

/-- The **buyer-optimal** stable outcome: the bottom of the lattice. -/
abbrev buyerOptimalOutcome (M : Market B S X) (hsub : M.Substitutable) :
    M.StableOutcomes hsub := ⊥

/-- DEVNOTE: proved by antisymmetry rather than `rfl`, so that it survives any
change to how mathlib populates the `top` field of `fixedPoints`. -/
theorem state_sellerOptimalOutcome (hsub : M.Substitutable) :
    (M.sellerOptimalOutcome hsub).state = OrderHom.gfp (M.daHom hsub) := by
  refine le_antisymm ?_ ?_
  · exact (M.daHom hsub).isGreatest_gfp.2 (M.sellerOptimalOutcome hsub).isFixedPt
  · exact le_top (a := (⟨OrderHom.gfp (M.daHom hsub),
      M.isFixedPt_gfp_daHom hsub⟩ : M.StableOutcomes hsub))

theorem state_buyerOptimalOutcome (hsub : M.Substitutable) :
    (M.buyerOptimalOutcome hsub).state = OrderHom.lfp (M.daHom hsub) := by
  refine le_antisymm ?_ ?_
  · exact bot_le (a := (⟨OrderHom.lfp (M.daHom hsub),
      M.isFixedPt_lfp_daHom hsub⟩ : M.StableOutcomes hsub))
  · exact (M.daHom hsub).isLeast_lfp.2 (M.buyerOptimalOutcome hsub).isFixedPt

theorem outcome_sellerOptimalOutcome (hsub : M.Substitutable) :
    (M.sellerOptimalOutcome hsub).outcome = M.sellerOptimal hsub :=
  congrArg M.outcomeOf (M.state_sellerOptimalOutcome hsub)

theorem outcome_buyerOptimalOutcome (hsub : M.Substitutable) :
    (M.buyerOptimalOutcome hsub).outcome = M.buyerOptimal hsub :=
  congrArg M.outcomeOf (M.state_buyerOptimalOutcome hsub)

/-- Seller-optimality, lattice form. -/
theorem sellerChosen_sellerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub) :
    M.SellerChosen (M.sellerOptimalOutcome hsub).outcome A.outcome :=
  (StableOutcomes.le_iff_sellerChosen hcons).mp le_top

/-- Buyer-pessimality, lattice form. -/
theorem buyerChosen_sellerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub) :
    M.BuyerChosen A.outcome (M.sellerOptimalOutcome hsub).outcome :=
  (StableOutcomes.le_iff_buyerChosen hcons).mp le_top

theorem buyerChosen_buyerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub) :
    M.BuyerChosen (M.buyerOptimalOutcome hsub).outcome A.outcome :=
  (StableOutcomes.le_iff_buyerChosen hcons).mp bot_le

theorem sellerChosen_buyerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub) :
    M.SellerChosen A.outcome (M.buyerOptimalOutcome hsub).outcome :=
  (StableOutcomes.le_iff_sellerChosen hcons).mp bot_le

/-! ### Concrete lattice operations — status

What is proved: the componentwise join of two fixed points is a *post*-fixed
point and the componentwise meet a *pre*-fixed point (pure monotonicity), and
`state_sup_of_isFixedPt` upgrades that to an identification of the lattice
operation *given* closure.

What is **not** proved, and is probably **false** at many-to-many generality:

    theorem isFixedPt_sup (hsub) (hcons) {p q} (hp : IsFixedPt M.daFun p)
        (hq : IsFixedPt M.daFun q) : IsFixedPt M.daFun (p ⊔ q)

Reduction.  By `stateOf_outcomeOf` every fixed point is
`(toSellers A, toBuyers A)` for its outcome `A`, so closure is exactly

  (i)  `toSellers (Xᵇp ∩ Xᵇq) ⊆ toSellers Ap ∪ toSellers Aq`
  (ii) `Xᵇp ∩ Xᵇq ⊆ toBuyers (Xˢp ∪ Xˢq)`

(the reverse inclusions are `antitone_toSellers`/`antitone_toBuyers`).

Obstruction to (ii).  Let `s` be a seller with capacity two and responsive
preferences `u ≻ v ≻ x`, holding `{u}` at `Ap` and `{v}` at `Aq`.  Then
`x ∈ Cˢ(x + Ap)` and `x ∈ Cˢ(x + Aq)`, so `x ∈ Xᵇp ∩ Xᵇq`; but
`u, v ∈ Xˢp ∪ Xˢq` and `Cˢ({x,u,v}) = {u,v}`, so `x ∉ toBuyers (Xˢp ∪ Xˢq)`.
Substitutability is satisfied throughout — the rejection function is monotone.
This is the Blair phenomenon in state coordinates: the genuine join gives `s`
the set `Cˢ(Ap ∪ Aq) = {u,v}`, strictly better than either, so the join's
buyer-available set is strictly smaller than the componentwise intersection.
The configuration is impossible under seller-side unit demand, which is why
the classical statements (Conway, Hatfield–Milgrom Thm 5) are many-to-one.

Recommendation.  Do not state `isFixedPt_sup` at this generality.  Either
(a) leave `⊔`/`⊓` opaque — the order dictionary above is what downstream
comparative statics actually needs, and it is fully general; or (b) state
closure under an explicit unit-demand hypothesis on the relevant side, in
`ManyToOne.lean`, where the decomposition argument is available.  Nothing in
this file depends on either. -/

/-- The componentwise join of two fixed points is a post-fixed point. -/
theorem le_daFun_sup (hsub : M.Substitutable) {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (hq : IsFixedPt M.daFun q) :
    p ⊔ q ≤ M.daFun (p ⊔ q) := by
  refine sup_le ?_ ?_
  · calc p = M.daFun p := hp.symm
      _ ≤ M.daFun (p ⊔ q) := M.monotone_daFun hsub le_sup_left
  · calc q = M.daFun q := hq.symm
      _ ≤ M.daFun (p ⊔ q) := M.monotone_daFun hsub le_sup_right

/-- The componentwise meet of two fixed points is a pre-fixed point. -/
theorem daFun_inf_le (hsub : M.Substitutable) {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (hq : IsFixedPt M.daFun q) :
    M.daFun (p ⊓ q) ≤ p ⊓ q := by
  refine le_inf ?_ ?_
  · calc M.daFun (p ⊓ q) ≤ M.daFun p := M.monotone_daFun hsub inf_le_left
      _ = p := hp
  · calc M.daFun (p ⊓ q) ≤ M.daFun q := M.monotone_daFun hsub inf_le_right
      _ = q := hq

/-- *If* the componentwise join is a fixed point, it is the lattice join.
Stated with the closure as a hypothesis so that no result depends on the open
问题 above; discharge it in the specialised files. -/
theorem state_sup_of_isFixedPt {hsub : M.Substitutable}
    {A A' : M.StableOutcomes hsub}
    (h : IsFixedPt M.daFun (A.state ⊔ A'.state)) :
    (A ⊔ A').state = A.state ⊔ A'.state := by
  let C : M.StableOutcomes hsub := ⟨A.state ⊔ A'.state, h⟩

  have hAC : A ≤ C := by
    change A.state ≤ A.state ⊔ A'.state
    exact le_sup_left

  have hA'C : A' ≤ C := by
    change A'.state ≤ A.state ⊔ A'.state
    exact le_sup_right

  have hjoinC : A ⊔ A' ≤ C :=
    sup_le hAC hA'C

  have hCjoin : C ≤ A ⊔ A' := by
    change A.state ⊔ A'.state ≤ (A ⊔ A').state
    refine sup_le ?_ ?_
    · exact (le_sup_left : A ≤ A ⊔ A')
    · exact (le_sup_right : A' ≤ A ⊔ A')

  have heq : A ⊔ A' = C :=
    le_antisymm hjoinC hCjoin

  simpa [C] using congrArg StableOutcomes.state heq

/-- Dual of `state_sup_of_isFixedPt`. -/
theorem state_inf_of_isFixedPt {hsub : M.Substitutable}
    {A A' : M.StableOutcomes hsub}
    (h : IsFixedPt M.daFun (A.state ⊓ A'.state)) :
    (A ⊓ A').state = A.state ⊓ A'.state := by
  let C : M.StableOutcomes hsub := ⟨A.state ⊓ A'.state, h⟩

  have hCA : C ≤ A := by
    change A.state ⊓ A'.state ≤ A.state
    exact inf_le_left

  have hCA' : C ≤ A' := by
    change A.state ⊓ A'.state ≤ A'.state
    exact inf_le_right

  have hCinf : C ≤ A ⊓ A' :=
    le_inf hCA hCA'

  have hinfC : A ⊓ A' ≤ C := by
    change (A ⊓ A').state ≤ A.state ⊓ A'.state
    refine le_inf ?_ ?_
    · exact (inf_le_left : A ⊓ A' ≤ A)
    · exact (inf_le_right : A ⊓ A' ≤ A')

  have heq : A ⊓ A' = C :=
    le_antisymm hinfC hCinf

  simpa [C] using congrArg StableOutcomes.state heq

/-! ### Rural hospitals (Theorems 2.3 / 3.3)

DEVNOTE: the only user of `SizeMonotone` in the file, and the only user of
finiteness outside the iteration lemma.  Scheduled to move to
`RuralHospitals.lean`; nothing above depends on it. -/

section Counting

variable [Fintype X]

private lemma ncard_eq_sum_buyerSide (A : Set X) (T : Finset B)
    (hT : ∀ x ∈ A, M.buyer x ∈ T) :
    A.ncard = ∑ b ∈ T, (M.buyerSide b A).ncard := by
  classical
  have hAf : A.Finite := Set.toFinite A
  have h0 : A.ncard = hAf.toFinset.card := Set.ncard_eq_toFinset_card A hAf
  rw [h0, Finset.card_eq_sum_card_fiberwise
      (fun x hx => hT x (hAf.mem_toFinset.mp hx))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Set.ncard_eq_toFinset_card (M.buyerSide b A) (Set.toFinite _)]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    exact (Set.Finite.mem_toFinset _).mpr ⟨hAf.mem_toFinset.mp hx1, hx2⟩
  · intro hx
    obtain ⟨hx1, hx2⟩ := (Set.Finite.mem_toFinset _).mp hx
    exact Finset.mem_filter.mpr ⟨hAf.mem_toFinset.mpr hx1, hx2⟩

private lemma ncard_eq_sum_sellerSide (A : Set X) (T : Finset S)
    (hT : ∀ x ∈ A, M.seller x ∈ T) :
    A.ncard = ∑ s ∈ T, (M.sellerSide s A).ncard := by
  classical
  have hAf : A.Finite := Set.toFinite A
  have h0 : A.ncard = hAf.toFinset.card := Set.ncard_eq_toFinset_card A hAf
  rw [h0, Finset.card_eq_sum_card_fiberwise
      (fun x hx => hT x (hAf.mem_toFinset.mp hx))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Set.ncard_eq_toFinset_card (M.sellerSide s A) (Set.toFinite _)]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    exact (Set.Finite.mem_toFinset _).mpr ⟨hAf.mem_toFinset.mp hx1, hx2⟩
  · intro hx
    obtain ⟨hx1, hx2⟩ := (Set.Finite.mem_toFinset _).mp hx
    exact Finset.mem_filter.mpr ⟨hAf.mem_toFinset.mpr hx1, hx2⟩

/-- The counting core: `|A| = Σ_b |A_b| = Σ_s |A_s|` squeezes the two
one-sided law-of-aggregate-demand inequalities into equalities. -/
private theorem ncard_eq_aux (hload : M.SizeMonotone) {A A₀ : Set X}
    (hA : M.Stable A) (hA₀ : M.Stable A₀)
    (hbc : M.BuyerChosen A A₀) (hsc : M.SellerChosen A₀ A) :
    (∀ b, (M.buyerSide b A).ncard = (M.buyerSide b A₀).ncard) ∧
    (∀ s, (M.sellerSide s A).ncard = (M.sellerSide s A₀).ncard) := by
  classical
  have hb : ∀ b, (M.buyerSide b A₀).ncard ≤ (M.buyerSide b A).ncard := by
    intro b
    have hsub' : A₀ ⊆ A ∪ A₀ := fun x hx => Or.inr hx
    have h : (M.choiceB b A₀).ncard ≤ (M.choiceB b (A ∪ A₀)).ncard :=
      hload.1 b hsub'
    rwa [hA₀.1.1 b, hbc b] at h
  have hs : ∀ s, (M.sellerSide s A).ncard ≤ (M.sellerSide s A₀).ncard := by
    intro s
    have hsub' : A ⊆ A₀ ∪ A := fun x hx => Or.inr hx
    have h : (M.choiceS s A).ncard ≤ (M.choiceS s (A₀ ∪ A)).ncard :=
      hload.2 s hsub'
    rwa [hA.1.2 s, hsc s] at h
  have hfin : (A ∪ A₀).Finite := Set.toFinite _
  have hmemB : ∀ x ∈ A ∪ A₀, M.buyer x ∈ hfin.toFinset.image M.buyer :=
    fun x hx => Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hx)
  have hmemS : ∀ x ∈ A ∪ A₀, M.seller x ∈ hfin.toFinset.image M.seller :=
    fun x hx => Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hx)
  have eA1 := M.ncard_eq_sum_buyerSide A _ fun x hx => hmemB x (Or.inl hx)
  have eA2 := M.ncard_eq_sum_sellerSide A _ fun x hx => hmemS x (Or.inl hx)
  have eB1 := M.ncard_eq_sum_buyerSide A₀ _ fun x hx => hmemB x (Or.inr hx)
  have eB2 := M.ncard_eq_sum_sellerSide A₀ _ fun x hx => hmemS x (Or.inr hx)
  have hcard : A.ncard = A₀.ncard := by
    refine le_antisymm ?_ ?_
    · rw [eA2, eB2]; exact Finset.sum_le_sum fun s _ => hs s
    · rw [eB1, eA1]; exact Finset.sum_le_sum fun b _ => hb b
  have hsumB : ∑ b ∈ hfin.toFinset.image M.buyer, (M.buyerSide b A₀).ncard
      = ∑ b ∈ hfin.toFinset.image M.buyer, (M.buyerSide b A).ncard := by
    rw [← eB1, ← eA1, hcard]
  have hsumS : ∑ s ∈ hfin.toFinset.image M.seller, (M.sellerSide s A).ncard
      = ∑ s ∈ hfin.toFinset.image M.seller, (M.sellerSide s A₀).ncard := by
    rw [← eA2, ← eB2, hcard]
  refine ⟨fun b => ?_, fun s => ?_⟩
  · by_cases hbT : b ∈ hfin.toFinset.image M.buyer
    · exact (sum_eq_of_le_of_sum_le (fun b _ => hb b) hsumB.symm.le b hbT).symm
    · have e1 : M.buyerSide b A = ∅ := by
        ext x
        simp only [mem_buyerSide, Set.mem_empty_iff_false, iff_false, not_and]
        intro hx hxb
        exact hbT (hxb ▸ hmemB x (Or.inl hx))
      have e2 : M.buyerSide b A₀ = ∅ := by
        ext x
        simp only [mem_buyerSide, Set.mem_empty_iff_false, iff_false, not_and]
        intro hx hxb
        exact hbT (hxb ▸ hmemB x (Or.inr hx))
      rw [e1, e2]
  · by_cases hsT : s ∈ hfin.toFinset.image M.seller
    · exact sum_eq_of_le_of_sum_le (fun s _ => hs s) hsumS.ge s hsT
    · have e1 : M.sellerSide s A = ∅ := by
        ext x
        simp only [mem_sellerSide, Set.mem_empty_iff_false, iff_false, not_and]
        intro hx hxs
        exact hsT (hxs ▸ hmemS x (Or.inl hx))
      have e2 : M.sellerSide s A₀ = ∅ := by
        ext x
        simp only [mem_sellerSide, Set.mem_empty_iff_false, iff_false, not_and]
        intro hx hxs
        exact hsT (hxs ▸ hmemS x (Or.inr hx))
      rw [e1, e2]

theorem ncard_buyerSide_eq_of_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) (hload : M.SizeMonotone) {A A' : Set X}
    (hA : M.Stable A) (hA' : M.Stable A') (b : B) :
    (M.buyerSide b A).ncard = (M.buyerSide b A').ncard := by
  have h1 := (M.ncard_eq_aux hload hA (M.stable_sellerOptimal hsub hcons)
    (M.buyerChosen_sellerOptimal hsub hcons hA)
    (M.sellerChosen_sellerOptimal hsub hcons hA)).1 b
  have h2 := (M.ncard_eq_aux hload hA' (M.stable_sellerOptimal hsub hcons)
    (M.buyerChosen_sellerOptimal hsub hcons hA')
    (M.sellerChosen_sellerOptimal hsub hcons hA')).1 b
  rw [h1, h2]

theorem ncard_sellerSide_eq_of_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) (hload : M.SizeMonotone) {A A' : Set X}
    (hA : M.Stable A) (hA' : M.Stable A') (s : S) :
    (M.sellerSide s A).ncard = (M.sellerSide s A').ncard := by
  have h1 := (M.ncard_eq_aux hload hA (M.stable_sellerOptimal hsub hcons)
    (M.buyerChosen_sellerOptimal hsub hcons hA)
    (M.sellerChosen_sellerOptimal hsub hcons hA)).2 s
  have h2 := (M.ncard_eq_aux hload hA' (M.stable_sellerOptimal hsub hcons)
    (M.buyerChosen_sellerOptimal hsub hcons hA')
    (M.sellerChosen_sellerOptimal hsub hcons hA')).2 s
  rw [h1, h2]

end Counting

end Market

/-! ### The iteration lemma (survey Observation 1) -/

/-- A monotone self-map of a finite complete lattice reaches its greatest
fixed point by iterating from `⊤`.

DEVNOTE: This should probably be pulled up the chain to mathlib. -/
theorem OrderHom.exists_iterate_top_eq_gfp {L : Type*} [CompleteLattice L]
    [Finite L] (f : L →o L) :
    ∃ n, (f : L → L)^[n] ⊤ = OrderHom.gfp f := by
  classical
  -- the iterates are antitone
  have hstep : ∀ n : ℕ, (f : L → L)^[n + 1] ⊤ ≤ (f : L → L)^[n] ⊤ := by
    intro n
    induction n with
    | zero => exact le_top
    | succ k ih =>
        calc (f : L → L)^[k + 1 + 1] (⊤ : L)
            = f ((f : L → L)^[k + 1] ⊤) := Function.iterate_succ_apply' _ _ _
          _ ≤ f ((f : L → L)^[k] ⊤) := f.monotone ih
          _ = (f : L → L)^[k + 1] ⊤ := (Function.iterate_succ_apply' _ _ _).symm
  have hanti : Antitone (fun n : ℕ => (f : L → L)^[n] (⊤ : L)) :=
    antitone_nat_of_succ_le hstep
  -- a beta-reduced restatement, so later `Eq.trans_le`s unify syntactically
  have hmono : ∀ a b : ℕ, a ≤ b →
      (f : L → L)^[b] (⊤ : L) ≤ (f : L → L)^[a] ⊤ := fun _ _ h => hanti h
  have hge : ∀ k : ℕ, OrderHom.gfp f ≤ (f : L → L)^[k] ⊤ := by
    intro k
    induction k with
    | zero => exact le_top
    | succ j ih =>
        calc OrderHom.gfp f = f (OrderHom.gfp f) := f.isGreatest_gfp.1.symm
          _ ≤ f ((f : L → L)^[j] ⊤) := f.monotone ih
          _ = (f : L → L)^[j + 1] ⊤ := (Function.iterate_succ_apply' _ _ _).symm
  -- finiteness forces the chain to stabilize
  obtain ⟨m, n, hmn, hval⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (f : L → L)^[k] (⊤ : L))
  have hval' : (f : L → L)^[m] (⊤ : L) = (f : L → L)^[n] ⊤ := hval
  have key : ∃ k : ℕ, (f : L → L)^[k + 1] (⊤ : L) = (f : L → L)^[k] ⊤ := by
        rcases lt_trichotomy m n with hlt | heq | hlt
        · exact ⟨m, le_antisymm (hstep m)
            (hval'.trans_le (hmono (m + 1) n (Nat.succ_le_of_lt hlt)))⟩
        · exact absurd heq hmn
        · exact ⟨n, le_antisymm (hstep n)
            (hval'.symm.trans_le (hmono (n + 1) m (Nat.succ_le_of_lt hlt)))⟩
  obtain ⟨k, hk⟩ := key
  refine ⟨k, le_antisymm ?_ (hge k)⟩
  have hfix : IsFixedPt (f : L → L) ((f : L → L)^[k] ⊤) :=
    (Function.iterate_succ_apply' (f : L → L) k ⊤).symm.trans hk
  exact f.isGreatest_gfp.2 hfix

/-- Mirror of `OrderHom.exists_iterate_top_eq_gfp`: iterating from `⊥` reaches
the least fixed point.

DEVNOTE: morally `exists_iterate_top_eq_gfp` applied to `f.dual`, but the
`gfp`/`lfp` interchange lemma's name has moved around, and the buyer-side
results below should not be hostage to it.  Collapse the two if and when the
spelling is pinned down; the proof is a literal mirror (`le_top ↝ bot_le`,
`isGreatest_gfp ↝ isLeast_lfp`, `Antitone ↝ Monotone`). -/
theorem OrderHom.exists_iterate_bot_eq_lfp {L : Type*} [CompleteLattice L]
    [Finite L] (f : L →o L) :
    ∃ n, (f : L → L)^[n] ⊥ = OrderHom.lfp f := by
  classical
  have hstep : ∀ n : ℕ, (f : L → L)^[n] ⊥ ≤ (f : L → L)^[n + 1] ⊤ → True :=
    fun _ _ => trivial  -- placeholder-free: see `hstep'` below
  clear hstep
  have hstep : ∀ n : ℕ, (f : L → L)^[n] ⊥ ≤ (f : L → L)^[n + 1] ⊥ := by
    intro n
    induction n with
    | zero => exact bot_le
    | succ k ih =>
        calc (f : L → L)^[k + 1] (⊥ : L)
            = f ((f : L → L)^[k] ⊥) := Function.iterate_succ_apply' _ _ _
          _ ≤ f ((f : L → L)^[k + 1] ⊥) := f.monotone ih
          _ = (f : L → L)^[k + 1 + 1] ⊥ := (Function.iterate_succ_apply' _ _ _).symm
  have hmonoNat : Monotone (fun n : ℕ => (f : L → L)^[n] (⊥ : L)) :=
    monotone_nat_of_le_succ hstep
  have hmono : ∀ a b : ℕ, a ≤ b →
      (f : L → L)^[a] (⊥ : L) ≤ (f : L → L)^[b] ⊥ := fun _ _ h => hmonoNat h
  have hle : ∀ k : ℕ, (f : L → L)^[k] ⊥ ≤ OrderHom.lfp f := by
    intro k
    induction k with
    | zero => exact bot_le
    | succ j ih =>
        calc (f : L → L)^[j + 1] (⊥ : L)
            = f ((f : L → L)^[j] ⊥) := Function.iterate_succ_apply' _ _ _
          _ ≤ f (OrderHom.lfp f) := f.monotone ih
          _ = OrderHom.lfp f := f.isLeast_lfp.1
  obtain ⟨m, n, hmn, hval⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (f : L → L)^[k] (⊥ : L))
  have hval' : (f : L → L)^[m] (⊥ : L) = (f : L → L)^[n] ⊥ := hval
  have key : ∃ k : ℕ, (f : L → L)^[k + 1] (⊥ : L) = (f : L → L)^[k] ⊥ := by
    rcases lt_trichotomy m n with hlt | heq | hlt
    · exact ⟨m, le_antisymm
        ((hmono (m + 1) n (Nat.succ_le_of_lt hlt)).trans hval'.ge) (hstep m)⟩
    · exact absurd heq hmn
    · exact ⟨n, le_antisymm
        ((hmono (n + 1) m (Nat.succ_le_of_lt hlt)).trans hval'.le) (hstep n)⟩
  obtain ⟨k, hk⟩ := key
  refine ⟨k, le_antisymm (hle k) ?_⟩
  have hfix : IsFixedPt (f : L → L) ((f : L → L)^[k] ⊥) :=
    (Function.iterate_succ_apply' (f : L → L) k ⊥).symm.trans hk
  exact f.isLeast_lfp.2 hfix

namespace Market

variable (M : Market B S X)

/-! ### Finiteness instances

Only needed for the iteration section; the `Fintype X` hypothesis is local to
the theorems below and never propagates upward. -/

/-- `Finite (Set X)` for a `Fintype` carrier. -/
instance instFiniteSetOfFintype [Fintype X] : Finite (Set X) := by
  classical
  have hinj : Function.Injective
      (fun A : Set X => (Finset.univ.filter (fun x => x ∈ A) : Finset X)) := by
    intro A B hAB
    have h := Finset.ext_iff.mp hAB
    ext x
    simpa [Finset.mem_filter] using h x
  exact Finite.of_injective _ hinj

/-- `ofDual` is the identity function, so injectivity is `fun _ _ h => h`. -/
instance instFiniteSetDualOfFintype [Fintype X] : Finite ((Set X)ᵒᵈ) :=
  Finite.of_injective (fun A : (Set X)ᵒᵈ => (ofDual A : Set X)) fun _ _ h => h

/-! ### Deferred acceptance as iteration

`⊤ = (univ, toDual ∅)`: all contracts available to sellers, none to buyers.
That is the classical initial state of *seller*-proposing deferred acceptance,
and by the orientation convention above it converges to the seller-optimal
state.  Dually `⊥ = (∅, toDual univ)` runs the buyer-proposing algorithm.

Both statements are `rfl`-level unfoldings of the two lattice-theoretic
iteration lemmas; the content is entirely in `monotone_daFun`. -/

/-- Seller-proposing deferred acceptance: under substitutability, iterating
from `(univ, ∅) = ⊤` computes the seller-optimal state in finitely many
steps. -/
theorem exists_iterate_daFun_top (hsub : M.Substitutable) [Fintype X] :
    ∃ n, M.daFun^[n] (Set.univ, toDual (∅ : Set X)) =
      OrderHom.gfp (M.daHom hsub) := by
  classical
  -- `Finite (Set X × (Set X)ᵒᵈ)` from the two instances above plus the `Prod`
  -- instance, which `Mathlib.Order.FixedPoints` already brings in transitively.
  obtain ⟨n, hn⟩ := OrderHom.exists_iterate_top_eq_gfp (M.daHom hsub)
  refine ⟨n, ?_⟩
  -- `⊤ = (univ, toDual ∅)` and `⇑(M.daHom hsub) = M.daFun` are definitional.
  have htop : ((Set.univ, toDual (∅ : Set X)) : Set X × (Set X)ᵒᵈ) = ⊤ := rfl
  rw [htop]
  exact hn

/-- Buyer-proposing deferred acceptance. -/
theorem exists_iterate_daFun_bot (hsub : M.Substitutable) [Fintype X] :
    ∃ n, M.daFun^[n] (∅, toDual (Set.univ : Set X)) =
      OrderHom.lfp (M.daHom hsub) := by
  classical
  obtain ⟨n, hn⟩ := OrderHom.exists_iterate_bot_eq_lfp (M.daHom hsub)
  refine ⟨n, ?_⟩
  have hbot : ((∅, toDual (Set.univ : Set X)) : Set X × (Set X)ᵒᵈ) = ⊥ := rfl
  rw [hbot]
  exact hn

/-- The algorithmic form of Theorem 2.2, outcome level: seller-proposing
deferred acceptance terminates at the seller-optimal *outcome*. -/
theorem exists_iterate_outcomeOf_eq_sellerOptimal (hsub : M.Substitutable)
    [Fintype X] :
    ∃ n, M.outcomeOf (M.daFun^[n] (Set.univ, toDual (∅ : Set X)))
      = M.sellerOptimal hsub := by
  obtain ⟨n, hn⟩ := M.exists_iterate_daFun_top hsub
  exact ⟨n, congrArg M.outcomeOf hn⟩

theorem exists_iterate_outcomeOf_eq_buyerOptimal (hsub : M.Substitutable)
    [Fintype X] :
    ∃ n, M.outcomeOf (M.daFun^[n] (∅, toDual (Set.univ : Set X)))
      = M.buyerOptimal hsub := by
  obtain ⟨n, hn⟩ := M.exists_iterate_daFun_bot hsub
  exact ⟨n, congrArg M.outcomeOf hn⟩

/-- Lattice form: the iterates of `⊤` reach `state (sellerOptimalOutcome)`.
Stated through `sellerOptimalOutcome` rather than `⊤` per the orientation
convention, so that downstream files never spell `gfp` either. -/
theorem exists_iterate_daFun_top_eq_state (hsub : M.Substitutable)
    [Fintype X] :
    ∃ n, M.daFun^[n] (Set.univ, toDual (∅ : Set X)) =
      (M.sellerOptimalOutcome hsub).state := by
  obtain ⟨n, hn⟩ := M.exists_iterate_daFun_top hsub
  exact ⟨n, hn.trans (M.state_sellerOptimalOutcome hsub).symm⟩

theorem exists_iterate_daFun_bot_eq_state (hsub : M.Substitutable)
    [Fintype X] :
    ∃ n, M.daFun^[n] (∅, toDual (Set.univ : Set X)) =
      (M.buyerOptimalOutcome hsub).state := by
  obtain ⟨n, hn⟩ := M.exists_iterate_daFun_bot hsub
  exact ⟨n, hn.trans (M.state_buyerOptimalOutcome hsub).symm⟩

end Market
