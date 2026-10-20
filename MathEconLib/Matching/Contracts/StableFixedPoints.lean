/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import MathEconLib.Matching.Contracts.Basic
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
aggregate demand. The order dictionary and lattice API are in `StableOrder`;
counting and finite convergence are in `RuralHospitals` and `FixedPointConvergence`.

This operator uses contract-wise acceptance from `insert x Y`; it is not
merely the complement of the rejection set. The distinction matters for the
bijection between fixed points and stable outcomes.

## References

HKContractDesign2017: John William Hatfield and Scott Duke Kominers,
*Contract design and stability in many-to-many matching*, Games and Economic
Behavior **101** (2017), 78–97. The operator is displayed in §4 (p. 86);
Lemma 1 and Theorem 1 are on p. 87, with proofs in Appendix A (pp. 91–92).
https://doi.org/10.1016/j.geb.2016.01.002

The paper's doctors correspond to sellers and its hospitals to buyers, so
its offer-state coordinates and order agree with those used here. The article
uses preference-induced choices; IRC is explained in footnote 8 (p. 80) and
Definition 6 with footnote 49 (p. 91). Here correspondence and existence hold
for arbitrary agent and contract types under explicit substitutability and
set-form IRC. The choice-order lattice and its relation to the article's
preference-order formulation are documented in `Order`.
-/

namespace MathEconLib.Matching

open MathEconLib.Choice

open Function OrderDual

universe u v w

variable {B : Type u} {S : Type v} {X : Type w}

namespace Market

variable (M : Market B S X)

/-! ### The generalized deferred acceptance operator -/

/-- Contracts accepted by their buyers when offered alongside `Xb`,
made available to sellers. -/
def toSellers (Xb : Set X) : Set X :=
  {x | x ∈ M.choiceB (M.buyer x) (insert x Xb)}

/-- Contracts accepted by their sellers when offered alongside `Xs`,
made available to buyers. -/
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

def deferredAcceptanceOperator : Set X × (Set X)ᵒᵈ → Set X × (Set X)ᵒᵈ :=
  fun p => (M.toSellers (ofDual p.2), toDual (M.toBuyers p.1))

/-- Substitutability of all agents makes the operator monotone: the two
antitone half-lemmas plus `OrderDual` bookkeeping (which is definitional). -/
theorem monotone_deferredAcceptanceOperator (hsub : M.Substitutable) :
    Monotone M.deferredAcceptanceOperator := by
  intro p q h
  exact ⟨M.antitone_toSellers hsub.1 h.2, M.antitone_toBuyers hsub.2 h.1⟩

def deferredAcceptanceOrderHom (hsub : M.Substitutable) :
    Set X × (Set X)ᵒᵈ →o Set X × (Set X)ᵒᵈ :=
  ⟨M.deferredAcceptanceOperator, M.monotone_deferredAcceptanceOperator hsub⟩

def outcomeOf (_M : Market B S X) (p : Set X × (Set X)ᵒᵈ) : Set X :=
  p.1 ∩ ofDual p.2

/-- The canonical acceptance state of `A`.

For stable `A`, `M.outcomeOf (M.stateOf A) = A` without choice regularity.
Under substitutability and IRC, `stateOf` and `outcomeOf` are inverse maps
between stable outcomes and deferred-acceptance fixed points. -/
def stateOf (A : Set X) : Set X × (Set X)ᵒᵈ := M.deferredAcceptanceOperator (A, toDual A)

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
  change x ∈ M.choiceB (M.buyer x) (insert x A)
  rw [Set.insert_eq_of_mem hx, h.1 (M.buyer x)]
  exact ⟨hx, rfl⟩

theorem subset_toBuyers_of_indRational {A : Set X} (h : M.IndRational A) :
    A ⊆ M.toBuyers A := by
  intro x hx
  change x ∈ M.choiceS (M.seller x) (insert x A)
  rw [Set.insert_eq_of_mem hx, h.2 (M.seller x)]
  exact ⟨hx, rfl⟩

/-! ### Certifying a canonical state directly

An algorithm can supply individual rationality and the singleton-acceptance
test below without first proving a stability theorem. Substitutability and
IRC then make its canonical state fixed; `stable_outcomeOf` subsequently
supplies stability from the general correspondence.
-/

/-- Individual rationality and the singleton-acceptance test recover the
outcome from its canonical state. No choice regularity is needed. -/
theorem outcomeOf_stateOf_of_indRational_of_accepts {A : Set X}
    (hIR : M.IndRational A)
    (hno : ∀ y, y ∈ M.choiceB (M.buyer y) (insert y A) →
      y ∈ M.choiceS (M.seller y) (insert y A) → y ∈ A) :
    M.outcomeOf (M.stateOf A) = A := by
  change M.toSellers A ∩ M.toBuyers A = A
  apply Set.Subset.antisymm
  · rintro y ⟨hyB, hyS⟩
    exact hno y hyB hyS
  · intro y hy
    exact ⟨M.subset_toSellers_of_indRational hIR hy,
      M.subset_toBuyers_of_indRational hIR hy⟩

/-- Certify a deferred-acceptance fixed point directly from individual
rationality and the singleton-acceptance test. The proof uses only choice
contraction, IRC, and path independence, and does not invoke stability. -/
theorem isFixedPt_stateOf_of_indRational_of_accepts
    (hsub : M.Substitutable) (hcons : M.Consistent) {A : Set X}
    (hIR : M.IndRational A)
    (hno : ∀ y, y ∈ M.choiceB (M.buyer y) (insert y A) →
      y ∈ M.choiceS (M.seller y) (insert y A) → y ∈ A) :
    IsFixedPt M.deferredAcceptanceOperator (M.stateOf A) := by
  have hAs : A ⊆ M.toSellers A := M.subset_toSellers_of_indRational hIR
  have hAb : A ⊆ M.toBuyers A := M.subset_toBuyers_of_indRational hIR
  have hB : ∀ b, M.choiceB b (M.toBuyers A) = M.choiceB b A := by
    intro b
    apply Eq.symm
    refine hcons.1 b ?_ hAb
    intro y hy
    have hyS : y ∈ M.toBuyers A := (M.choiceB b).choose_subset _ hy
    have hyB : y ∈ M.choiceB b (insert y A) :=
      (hsub.1 b).mem_of_subset (Set.insert_subset_iff.mpr ⟨hyS, hAb⟩)
        hy (Set.mem_insert _ _)
    refine hno y ?_ hyS
    rw [M.buyer_eq_of_mem hy]
    exact hyB
  have hS : ∀ s, M.choiceS s (M.toSellers A) = M.choiceS s A := by
    intro s
    apply Eq.symm
    refine hcons.2 s ?_ hAs
    intro y hy
    have hyB : y ∈ M.toSellers A := (M.choiceS s).choose_subset _ hy
    have hyS : y ∈ M.choiceS s (insert y A) :=
      (hsub.2 s).mem_of_subset (Set.insert_subset_iff.mpr ⟨hyB, hAs⟩)
        hy (Set.mem_insert _ _)
    apply hno y hyB
    rw [M.seller_eq_of_mem hy]
    exact hyS
  have heqS : M.toSellers (M.toBuyers A) = M.toSellers A := by
    ext x
    have heq : M.choiceB (M.buyer x) (insert x (M.toBuyers A)) =
        M.choiceB (M.buyer x) (insert x A) := by
      have hpi := (hsub.1 (M.buyer x)).pathIndependent (hcons.1 (M.buyer x))
      simpa only [Set.union_singleton] using
        hpi.union_congr_left (hB (M.buyer x)) ({x} : Set X)
    change x ∈ M.choiceB (M.buyer x) (insert x (M.toBuyers A)) ↔
      x ∈ M.choiceB (M.buyer x) (insert x A)
    rw [heq]
  have heqB : M.toBuyers (M.toSellers A) = M.toBuyers A := by
    ext x
    have heq : M.choiceS (M.seller x) (insert x (M.toSellers A)) =
        M.choiceS (M.seller x) (insert x A) := by
      have hpi := (hsub.2 (M.seller x)).pathIndependent (hcons.2 (M.seller x))
      simpa only [Set.union_singleton] using
        hpi.union_congr_left (hS (M.seller x)) ({x} : Set X)
    change x ∈ M.choiceS (M.seller x) (insert x (M.toSellers A)) ↔
      x ∈ M.choiceS (M.seller x) (insert x A)
    rw [heq]
  change (M.toSellers (M.toBuyers A), toDual (M.toBuyers (M.toSellers A))) =
    (M.toSellers A, toDual (M.toBuyers A))
  rw [heqS, heqB]

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
  change x ∈ M.choiceB (M.buyer x) (insert x W) ↔
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
  change x ∈ M.choiceS (M.seller x) (insert x W) ↔
    x ∈ M.choiceS (M.seller x) (insert x A)
  rw [heq]

/-! ### Elementary consequences of being a fixed point -/

theorem toSellers_eq_of_isFixedPt {p : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.deferredAcceptanceOperator p) : M.toSellers (ofDual p.2) = p.1 :=
  congrArg Prod.fst hp

theorem toBuyers_eq_of_isFixedPt {p : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.deferredAcceptanceOperator p) : M.toBuyers p.1 = ofDual p.2 :=
  congrArg (fun q => ofDual q.2) hp

/-- At a fixed point, what a buyer chooses from the buyer-available set is
already part of the outcome.  (No substitutability, no IRC.) -/
theorem choiceB_subset_outcomeOf {p : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.deferredAcceptanceOperator p) (b : B) :
    M.choiceB b (ofDual p.2) ⊆ M.outcomeOf p := by
  intro y hy
  have hyXb : y ∈ (ofDual p.2 : Set X) := (M.choiceB b).choose_subset _ hy
  have hby : M.buyer y = b := M.buyer_eq_of_mem hy
  have hys : y ∈ M.toSellers (ofDual p.2 : Set X) := by
    change y ∈ M.choiceB (M.buyer y) (insert y (ofDual p.2 : Set X))
    rw [Set.insert_eq_of_mem hyXb, hby]
    exact hy
  refine ⟨?_, hyXb⟩
  rw [← M.toSellers_eq_of_isFixedPt hp]
  exact hys

theorem choiceS_subset_outcomeOf {p : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.deferredAcceptanceOperator p) (s : S) :
    M.choiceS s p.1 ⊆ M.outcomeOf p := by
  intro y hy
  have hyXs : y ∈ p.1 := (M.choiceS s).choose_subset _ hy
  have hsy : M.seller y = s := M.seller_eq_of_mem hy
  have hyb : y ∈ M.toBuyers p.1 := by
    change y ∈ M.choiceS (M.seller y) (insert y p.1)
    rw [Set.insert_eq_of_mem hyXs, hsy]
    exact hy
  refine ⟨hyXs, ?_⟩
  rw [← M.toBuyers_eq_of_isFixedPt hp]
  exact hyb

/-- Pure-IRC sandwich: any menu between the outcome and the buyer-available
set induces the same buyer choice. -/
theorem choiceB_eq_of_isFixedPt_sandwich (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.deferredAcceptanceOperator p) (b : B) {V : Set X}
    (h1 : M.outcomeOf p ⊆ V) (h2 : V ⊆ (ofDual p.2 : Set X)) :
    M.choiceB b V = M.choiceB b (ofDual p.2) :=
  hcons.1 b ((M.choiceB_subset_outcomeOf hp b).trans h1) h2

theorem choiceS_eq_of_isFixedPt_sandwich (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.deferredAcceptanceOperator p) (s : S) {V : Set X}
    (h1 : M.outcomeOf p ⊆ V) (h2 : V ⊆ p.1) :
    M.choiceS s V = M.choiceS s p.1 :=
  hcons.2 s ((M.choiceS_subset_outcomeOf hp s).trans h1) h2

/-- Path independence at a fixed point: menus differing only in contracts
from the buyer-available set induce the same buyer choice. -/
theorem choiceB_eq_of_isFixedPt (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.deferredAcceptanceOperator p) (b : B) {U V : Set X}
    (hAU : M.outcomeOf p ⊆ U) (hUV : U ⊆ V) (hXbV : (ofDual p.2 : Set X) ⊆ V)
    (hVU : ∀ y ∈ V, y ∉ U → y ∈ (ofDual p.2 : Set X)) :
    M.choiceB b V = M.choiceB b U := by
  have hV : V = U ∪ (ofDual p.2 : Set X) := by
    apply Set.Subset.antisymm
    · intro y hy
      by_cases hyU : y ∈ U
      · exact Or.inl hyU
      · exact Or.inr (hVU y hy hyU)
    · exact Set.union_subset hUV hXbV
  rw [hV]
  exact ((hsub.1 b).pathIndependent (hcons.1 b)).union_eq_left_of_choice_subset
    ((M.choiceB_subset_outcomeOf hp b).trans hAU)

theorem choiceS_eq_of_isFixedPt (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.deferredAcceptanceOperator p) (s : S) {U V : Set X}
    (hAU : M.outcomeOf p ⊆ U) (hUV : U ⊆ V) (hXsV : p.1 ⊆ V)
    (hVU : ∀ y ∈ V, y ∉ U → y ∈ p.1) :
    M.choiceS s V = M.choiceS s U := by
  have hV : V = U ∪ p.1 := by
    apply Set.Subset.antisymm
    · intro y hy
      by_cases hyU : y ∈ U
      · exact Or.inl hyU
      · exact Or.inr (hVU y hy hyU)
    · exact Set.union_subset hUV hXsV
  rw [hV]
  exact ((hsub.2 s).pathIndependent (hcons.2 s)).union_eq_left_of_choice_subset
    ((M.choiceS_subset_outcomeOf hp s).trans hAU)

/-! ### HKContractDesign2017, Lemma 1 (p. 87): fixed points ↔ stable outcomes -/

/-- IRC alone makes the outcome of a fixed point individually rational.
Substitutability is needed for nonblocking, not for this conclusion. -/
theorem indRational_outcomeOf (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.deferredAcceptanceOperator p) :
    M.IndRational (M.outcomeOf p) := by
  have hAs : M.outcomeOf p ⊆ p.1 := fun x hx => hx.1
  have hAb : M.outcomeOf p ⊆ (ofDual p.2 : Set X) := fun x hx => hx.2
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

/-- Recompute the seller-available coordinate from the outcome. IRC identifies
the choices from the two menus; path independence preserves that identity when
one contract is added. -/
theorem toSellers_outcomeOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.deferredAcceptanceOperator p) :
    M.toSellers (M.outcomeOf p) = p.1 := by
  rw [← M.toSellers_eq_of_isFixedPt hp]
  ext x
  have heq := M.choiceB_eq_of_isFixedPt_sandwich hcons hp (M.buyer x)
    (subset_refl _) (fun _ hx => hx.2)
  have hpi := (hsub.1 (M.buyer x)).pathIndependent (hcons.1 (M.buyer x))
  have hins : M.choiceB (M.buyer x) (insert x (M.outcomeOf p)) =
      M.choiceB (M.buyer x) (insert x (ofDual p.2 : Set X)) := by
    simpa only [Set.union_singleton] using hpi.union_congr_left heq ({x} : Set X)
  change x ∈ M.choiceB (M.buyer x) (insert x (M.outcomeOf p)) ↔
    x ∈ M.choiceB (M.buyer x) (insert x (ofDual p.2 : Set X))
  rw [hins]

/-- Recompute the buyer-available coordinate from the outcome. -/
theorem toBuyers_outcomeOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.deferredAcceptanceOperator p) :
    M.toBuyers (M.outcomeOf p) = (ofDual p.2 : Set X) := by
  rw [← M.toBuyers_eq_of_isFixedPt hp]
  ext x
  have heq := M.choiceS_eq_of_isFixedPt_sandwich hcons hp (M.seller x)
    (subset_refl _) (fun _ hx => hx.1)
  have hpi := (hsub.2 (M.seller x)).pathIndependent (hcons.2 (M.seller x))
  have hins : M.choiceS (M.seller x) (insert x (M.outcomeOf p)) =
      M.choiceS (M.seller x) (insert x p.1) := by
    simpa only [Set.union_singleton] using hpi.union_congr_left heq ({x} : Set X)
  change x ∈ M.choiceS (M.seller x) (insert x (M.outcomeOf p)) ↔
    x ∈ M.choiceS (M.seller x) (insert x p.1)
  rw [hins]

/-- The fixed-point round trip is a choice-theoretic result, established
before stability and used to prove nonblocking. -/
theorem stateOf_outcomeOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.deferredAcceptanceOperator p) :
    M.stateOf (M.outcomeOf p) = p := by
  apply Prod.ext
  · exact M.toSellers_outcomeOf hsub hcons hp
  · exact congrArg toDual (M.toBuyers_outcomeOf hsub hcons hp)

/-- A fixed point is determined by its outcome. Stability of the outcome is
not an additional hypothesis. -/
theorem eq_of_isFixedPt_of_outcomeOf_eq_state (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} {p : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.deferredAcceptanceOperator p) (hout : M.outcomeOf p = A) :
    p = M.stateOf A :=
  (M.stateOf_outcomeOf hsub hcons hp).symm.trans (congrArg M.stateOf hout)

/-- The outcome map is injective on deferred-acceptance fixed points. -/
theorem outcomeOf_injOn_fixedPoints (hsub : M.Substitutable) (hcons : M.Consistent) :
    Set.InjOn M.outcomeOf {p | IsFixedPt M.deferredAcceptanceOperator p} := by
  intro p hp q hq hpq
  rw [← M.stateOf_outcomeOf hsub hcons hp, ← M.stateOf_outcomeOf hsub hcons hq]
  exact congrArg M.stateOf hpq

/-- HKContractDesign2017, Lemma 1 (p. 87), first half: a fixed point has a stable outcome.
The state round trip makes singleton nonblocking an immediate consequence of
membership in both coordinates. -/
theorem stable_outcomeOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.deferredAcceptanceOperator p) :
    M.Stable (M.outcomeOf p) := by
  apply PairwiseStable.stable_of_substitutable M hsub
  refine ⟨M.indRational_outcomeOf hcons hp, ?_⟩
  intro z hz
  obtain ⟨hzA, hzB, hzS⟩ := M.blocks_singleton_iff.mp hz
  have hzout : z ∈ M.outcomeOf (M.stateOf (M.outcomeOf p)) := ⟨hzB, hzS⟩
  rw [M.stateOf_outcomeOf hsub hcons hp] at hzout
  exact hzA hzout

/-- HKContractDesign2017, Lemma 1 (p. 87), second half (existence), specializing
the direct canonical-state certificate to the singleton-acceptance test
supplied by stability. -/
theorem isFixedPt_deferredAcceptanceOperator_of_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    IsFixedPt M.deferredAcceptanceOperator (M.deferredAcceptanceOperator (A, toDual A)) :=
  M.isFixedPt_stateOf_of_indRational_of_accepts hsub hcons hA.1
    (fun _ hyB hyS => M.not_blocking_singleton hA hyB hyS)

/-- Recovering a stable outcome from its canonical state needs no choice
regularity: individual rationality gives one inclusion and absence of singleton
blocks gives the other. -/
theorem outcomeOf_stateOf_of_stable {A : Set X} (hA : M.Stable A) :
    M.outcomeOf (M.stateOf A) = A :=
  M.outcomeOf_stateOf_of_indRational_of_accepts hA.1
    (fun _ hyB hyS => M.not_blocking_singleton hA hyB hyS)

/-! #### The HKContractDesign2017, Lemma 1 (p. 87) round trips, in `stateOf` form

These interfaces use `stateOf A` in place of `deferredAcceptanceOperator (A, toDual A)`.
`outcomeOf_stateOf_of_stable` above omits the regularity hypotheses
in the outcome round trip. -/

theorem isFixedPt_stateOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {A : Set X} (hA : M.Stable A) : IsFixedPt M.deferredAcceptanceOperator (M.stateOf A) :=
  M.isFixedPt_deferredAcceptanceOperator_of_stable hsub hcons hA

/-! ### Existence and the two extremal states -/

/-- The seller-optimal stable contract set, under substitutability and IRC. -/
noncomputable def sellerOptimal (hsub : M.Substitutable)
    (_hcons : M.Consistent) : Set X :=
  M.outcomeOf (OrderHom.gfp (M.deferredAcceptanceOrderHom hsub))

/-- The buyer-optimal stable contract set, under substitutability and IRC. -/
noncomputable def buyerOptimal (hsub : M.Substitutable)
    (_hcons : M.Consistent) : Set X :=
  M.outcomeOf (OrderHom.lfp (M.deferredAcceptanceOrderHom hsub))

theorem isFixedPt_gfp_deferredAcceptanceOrderHom (hsub : M.Substitutable) :
    IsFixedPt M.deferredAcceptanceOperator (OrderHom.gfp (M.deferredAcceptanceOrderHom hsub)) :=
  (M.deferredAcceptanceOrderHom hsub).isGreatest_gfp.1

theorem le_gfp_deferredAcceptanceOrderHom (hsub : M.Substitutable) {q : Set X × (Set X)ᵒᵈ}
    (hq : IsFixedPt M.deferredAcceptanceOperator q) :
    q ≤ OrderHom.gfp (M.deferredAcceptanceOrderHom hsub) :=
  (M.deferredAcceptanceOrderHom hsub).isGreatest_gfp.2 hq

theorem isFixedPt_lfp_deferredAcceptanceOrderHom (hsub : M.Substitutable) :
    IsFixedPt M.deferredAcceptanceOperator (OrderHom.lfp (M.deferredAcceptanceOrderHom hsub)) :=
  (M.deferredAcceptanceOrderHom hsub).isLeast_lfp.1

theorem lfp_le_deferredAcceptanceOrderHom (hsub : M.Substitutable) {q : Set X × (Set X)ᵒᵈ}
    (hq : IsFixedPt M.deferredAcceptanceOperator q) :
    OrderHom.lfp (M.deferredAcceptanceOrderHom hsub) ≤ q :=
  (M.deferredAcceptanceOrderHom hsub).isLeast_lfp.2 hq

theorem stable_sellerOptimal (hsub : M.Substitutable) (hcons : M.Consistent) :
    M.Stable (M.sellerOptimal hsub hcons) :=
  M.stable_outcomeOf hsub hcons (M.isFixedPt_gfp_deferredAcceptanceOrderHom hsub)

theorem stable_buyerOptimal (hsub : M.Substitutable) (hcons : M.Consistent) :
    M.Stable (M.buyerOptimal hsub hcons) :=
  M.stable_outcomeOf hsub hcons (M.isFixedPt_lfp_deferredAcceptanceOrderHom hsub)

/-- Stable existence as in HKContractDesign2017, Theorem 1 (p. 87), with
explicit substitutability and set-form IRC on arbitrary contract types. -/
theorem exists_stable (hsub : M.Substitutable) (hcons : M.Consistent) :
    ∃ A : Set X, M.Stable A :=
  ⟨M.sellerOptimal hsub hcons, M.stable_sellerOptimal hsub hcons⟩

/-- On finite contract types, the law of aggregate demand supplies the IRC hypothesis. -/
theorem exists_stable_of_sizeMonotone [Finite X]
    (hsub : M.Substitutable) (hload : M.SizeMonotone) :
    ∃ A : Set X, M.Stable A :=
  M.exists_stable hsub (M.consistent_of_substitutable_sizeMonotone hsub hload)

end Market

end MathEconLib.Matching
