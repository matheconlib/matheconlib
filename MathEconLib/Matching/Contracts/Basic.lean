/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

/-
Matching with contracts, Layer 1: two-sided markets and stability.
-/
public import MathEconLib.Choice.Conditions

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert

/-!
# Two-sided matching markets with contracts

A contract is an element of a bare type `X` equipped with maps to
the buyer type `B` and seller type `S`; the "terms" of the contract
are absorbed into contract identity. A market attaches one `ChoiceFunction X`
to every agent, subject only to the *support* condition (agents choose only
contracts to which they are associated).

Irrelevance of rejected contracts (IRC) and substitutability are theorem
hypotheses via the market-level predicates below, never structure fields.
This also permits non-substitutable instances.

Everything here is implemented at Hatfield–Kominers **many-to-many generality**.
The definitions impose no unit-demand or unitarity hypotheses.

## Main definitions

* `Market B S X` — the carrier.
* `Market.buyerSide`, `Market.sellerSide` — an agent's contracts within a set.
* `Market.Local` — absence of menu externalities, independently of IRC.
* `Market.Consistent`, `Market.Substitutable`, `Market.SizeMonotone` —
  hypothesis bundles quantifying the choice-layer predicates over all agents.
* `Market.IndRational`, `Market.Blocks`, `Market.Stable`,
  `Market.PairwiseStable` — HKContractDesign2017, Definition 2 and the following
  discussion (p. 81).
* `Market.SellerChosen`, `Market.BuyerChosen` — the relations `⊒S`, `⊒B`.

## Main statements

* `Market.choiceB_buyerSide`, `Market.choiceS_sellerSide` — locality from
  set-form IRC (one line; the reason IRC is taken in set form).
* `Market.blocks_singleton_iff` — the single-contract blocking test in the
  `insert z A` form used by every downstream proof.
* `Market.Stable.pairwiseStable`,
  `Market.pairwiseStable_iff_stable_of_substitutable` —
  the stable/pairwise-stable portion of HKContractDesign2017, Proposition 2
  (p. 81); IRC is not needed here.

## References

HKContractDesign2017: John William Hatfield and Scott Duke Kominers,
*Contract design and stability in many-to-many matching*, Games and Economic
Behavior **101** (2017), 78–97. Definition 2 and Proposition 2 are on p. 81;
pairwise stability is defined in the paragraph following Definition 2.
https://doi.org/10.1016/j.geb.2016.01.002

Proposition 2 also includes a many-to-one stability notion not formalized here.
The article uses preference-induced choices; IRC is discussed in footnote 8
(p. 80) and Definition 6 (p. 91). The present statements expose choice
regularity separately and allow arbitrary agent and contract types.

## Implementation notes

`Market` is a structure; the predicates below are plain `def`s unfolding to
`∧`/`∀`. The explicit `mem_buyerSide`/`mem_sellerSide` simp lemmas and
`blocks_singleton_iff` provide stable rewriting interfaces, so downstream
proofs need not unfold the predicates by hand.
-/

@[expose] public section

namespace MathEconLib.Matching

open MathEconLib.Choice

universe u v w

variable {B : Type u} {S : Type v} {X : Type w}

/-- A **two-sided market with contracts**: contracts `X` with buyer and seller
assignments, and a choice function for every agent, choosing only own
contracts. -/
structure Market (B : Type u) (S : Type v) (X : Type w) where
  /-- The buyer of a contract. -/
  buyer : X → B
  /-- The seller of a contract. -/
  seller : X → S
  /-- Buyer `b`'s choice function on contracts. -/
  choiceB : B → ChoiceFunction X
  /-- Seller `s`'s choice function on contracts. -/
  choiceS : S → ChoiceFunction X
  /-- Support: buyers choose only contracts they buy. -/
  buyer_eq_of_mem : ∀ ⦃b Y x⦄, x ∈ choiceB b Y → buyer x = b
  /-- Support: sellers choose only contracts they sell. -/
  seller_eq_of_mem : ∀ ⦃s Y x⦄, x ∈ choiceS s Y → seller x = s

namespace Market

variable (M : Market B S X)

/-- The contracts in `Y` bought by `b`. -/
def buyerSide (b : B) (Y : Set X) : Set X := {x ∈ Y | M.buyer x = b}

/-- The contracts in `Y` sold by `s`. -/
def sellerSide (s : S) (Y : Set X) : Set X := {x ∈ Y | M.seller x = s}

@[simp] lemma mem_buyerSide {b : B} {Y : Set X} {x : X} :
    x ∈ M.buyerSide b Y ↔ x ∈ Y ∧ M.buyer x = b := Iff.rfl

@[simp] lemma mem_sellerSide {s : S} {Y : Set X} {x : X} :
    x ∈ M.sellerSide s Y ↔ x ∈ Y ∧ M.seller x = s := Iff.rfl

lemma buyerSide_subset (b : B) (Y : Set X) : M.buyerSide b Y ⊆ Y :=
  fun _ hx => (M.mem_buyerSide.mp hx).1

lemma sellerSide_subset (s : S) (Y : Set X) : M.sellerSide s Y ⊆ Y :=
  fun _ hx => (M.mem_sellerSide.mp hx).1

/-- The choice set sits inside the agent's own side, by support. -/
lemma choiceB_subset_buyerSide (b : B) (Y : Set X) :
    M.choiceB b Y ⊆ M.buyerSide b Y := fun _ hx =>
  M.mem_buyerSide.mpr ⟨(M.choiceB b).choose_subset Y hx, M.buyer_eq_of_mem hx⟩

lemma choiceS_subset_sellerSide (s : S) (Y : Set X) :
    M.choiceS s Y ⊆ M.sellerSide s Y := fun _ hx =>
  M.mem_sellerSide.mpr ⟨(M.choiceS s).choose_subset Y hx, M.seller_eq_of_mem hx⟩

/-! ### Hypothesis bundles -/

/-- Each agent's choice depends only on the contracts involving that agent.
Support alone does not imply this absence of menu externalities. -/
def Local : Prop :=
  (∀ b Y, M.choiceB b (M.buyerSide b Y) = M.choiceB b Y) ∧
    ∀ s Y, M.choiceS s (M.sellerSide s Y) = M.choiceS s Y

/-- Every agent's choice function satisfies the IRC condition. -/
def Consistent : Prop :=
  (∀ b, (M.choiceB b).Consistent) ∧ ∀ s, (M.choiceS s).Consistent

/-- Every agent's choice function is substitutable. -/
def Substitutable : Prop :=
  (∀ b, (M.choiceB b).Substitutable) ∧ ∀ s, (M.choiceS s).Substitutable

/-- Every agent's choice function satisfies the law of aggregate demand on
finite menus. -/
def SizeMonotone : Prop :=
  (∀ b, (M.choiceB b).SizeMonotone) ∧ ∀ s, (M.choiceS s).SizeMonotone

/-- In a finite contract market, substitutability and the law of aggregate demand
already imply IRC on both sides. No finiteness of the agent types is needed. -/
theorem consistent_of_substitutable_sizeMonotone [Finite X]
    (hsub : M.Substitutable) (hload : M.SizeMonotone) : M.Consistent :=
  ⟨fun b => (hsub.1 b).consistent_of_sizeMonotone (hload.1 b),
   fun s => (hsub.2 s).consistent_of_sizeMonotone (hload.2 s)⟩

/-! ### Locality

Under set-form IRC and the support condition, an agent's choice depends only
on their own contracts — this is a *lemma*, not an axiom of `Market`.

Paper proof (finiteness-free): with `Z := buyerSide b Y` we have
`choiceB b Y ⊆ Z` by support and `Z ⊆ Y` by definition; apply `Consistent`. -/

theorem choiceB_buyerSide {b : B} (h : (M.choiceB b).Consistent) (Y : Set X) :
    M.choiceB b (M.buyerSide b Y) = M.choiceB b Y :=
  h (M.choiceB_subset_buyerSide b Y) (M.buyerSide_subset b Y)

theorem choiceS_sellerSide {s : S} (h : (M.choiceS s).Consistent) (Y : Set X) :
    M.choiceS s (M.sellerSide s Y) = M.choiceS s Y :=
  h (M.choiceS_subset_sellerSide s Y) (M.sellerSide_subset s Y)

/-- IRC and support imply locality, without finiteness or substitutability. -/
theorem Consistent.local (h : M.Consistent) : M.Local :=
  ⟨fun b Y => M.choiceB_buyerSide (h.1 b) Y,
    fun s Y => M.choiceS_sellerSide (h.2 s) Y⟩

/-! ### Stability (HKContractDesign2017, Definition 2, p. 81) -/

/-- An outcome `A` is **individually rational** if every agent chooses exactly
their part of `A` from `A`. -/
def IndRational (A : Set X) : Prop :=
  (∀ b, M.choiceB b A = M.buyerSide b A) ∧
    ∀ s, M.choiceS s A = M.sellerSide s A

/-- An individually rational outcome is chosen by each contract's buyer. -/
theorem mem_choiceB_of_indRational {A : Set X} (h : M.IndRational A) {x : X}
    (hx : x ∈ A) : x ∈ M.choiceB (M.buyer x) A := by
  rw [h.1 (M.buyer x)]
  exact M.mem_buyerSide.mpr ⟨hx, rfl⟩

/-- An individually rational outcome is chosen by each contract's seller. -/
theorem mem_choiceS_of_indRational {A : Set X} (h : M.IndRational A) {x : X}
    (hx : x ∈ A) : x ∈ M.choiceS (M.seller x) A := by
  rw [h.2 (M.seller x)]
  exact M.mem_sellerSide.mpr ⟨hx, rfl⟩

/-- `Z` **blocks** `A`: `Z` is a nonempty set of new contracts, all of which
every involved agent takes when offered `A ∪ Z`. (For an agent with no
contract in `Z` the condition is vacuous.) -/
def Blocks (A Z : Set X) : Prop :=
  Z.Nonempty ∧ Disjoint Z A ∧
    (∀ b, M.buyerSide b Z ⊆ M.choiceB b (A ∪ Z)) ∧
      ∀ s, M.sellerSide s Z ⊆ M.choiceS s (A ∪ Z)

/-- **Stability**: individually rational and unblocked. -/
def Stable (A : Set X) : Prop :=
  M.IndRational A ∧ ∀ Z, ¬ M.Blocks A Z

/-- **Pairwise stability**: individually rational with no single blocking
contract. -/
def PairwiseStable (A : Set X) : Prop :=
  M.IndRational A ∧ ∀ z, ¬ M.Blocks A {z}

/-- A singleton blocks exactly when its contract is new and both of its
agents choose it from `insert z A`. -/
theorem blocks_singleton_iff {A : Set X} {z : X} :
    M.Blocks A {z} ↔
      z ∉ A ∧ z ∈ M.choiceB (M.buyer z) (insert z A) ∧
        z ∈ M.choiceS (M.seller z) (insert z A) := by
  -- The one set identity the whole proof turns on.
  have hAz : A ∪ ({z} : Set X) = insert z A := Set.union_singleton
  constructor
  · rintro ⟨-, hdisj, hB, hS⟩
    refine ⟨Set.disjoint_singleton_left.mp hdisj, ?_, ?_⟩
    · have hmem := hB (M.buyer z)
        (M.mem_buyerSide.mpr ⟨Set.mem_singleton_iff.mpr rfl, rfl⟩)
      rwa [hAz] at hmem
    · have hmem := hS (M.seller z)
        (M.mem_sellerSide.mpr ⟨Set.mem_singleton_iff.mpr rfl, rfl⟩)
      rwa [hAz] at hmem
  · rintro ⟨hzA, hB, hS⟩
    refine ⟨Set.singleton_nonempty z, Set.disjoint_singleton_left.mpr hzA,
      ?_, ?_⟩
    · intro b x hx
      obtain ⟨hxz, hxb⟩ := M.mem_buyerSide.mp hx
      have hxz' : x = z := Set.mem_singleton_iff.mp hxz
      have hbz : M.buyer z = b := by rw [← hxz']; exact hxb
      rw [hAz, hxz', ← hbz]
      exact hB
    · intro s x hx
      obtain ⟨hxz, hxs⟩ := M.mem_sellerSide.mp hx
      have hxz' : x = z := Set.mem_singleton_iff.mp hxz
      have hsz : M.seller z = s := by rw [← hxz']; exact hxs
      rw [hAz, hxz', ← hsz]
      exact hS

/-- Every stable outcome is pairwise stable, directly from the definitions. -/
theorem Stable.pairwiseStable {A : Set X} (h : M.Stable A) :
    M.PairwiseStable A :=
  ⟨h.1, fun z => h.2 {z}⟩

/-- Substitutability reduces every blocking set to a blocking contract.
This is the implication used in HKContractDesign2017, Proposition 2 (p. 81),
proved there as Lemma 2 in Appendix A (p. 91);
the present proof requires neither IRC nor finiteness. -/
theorem PairwiseStable.stable_of_substitutable (hsub : M.Substitutable)
    {A : Set X} (h : M.PairwiseStable A) : M.Stable A := by
  refine ⟨h.1, fun Z hZ => ?_⟩
  obtain ⟨⟨z, hz⟩, hdisj, hB, hS⟩ := hZ
  have hAZ : A ⊆ A ∪ Z := fun y hy => Or.inl hy
  have hzAZ : z ∈ A ∪ Z := Set.mem_union_right A hz
  refine h.2 z (M.blocks_singleton_iff.mpr
    ⟨Set.disjoint_left.mp hdisj hz, ?_, ?_⟩)
  · -- Buyers: shrink the menu from `A ∪ Z` to `insert z A`.
    have hmem : z ∈ M.choiceB (M.buyer z) (A ∪ Z) :=
      hB (M.buyer z) (M.mem_buyerSide.mpr ⟨hz, rfl⟩)
    have h1 : z ∈ M.choiceB (M.buyer z) (insert z (A ∪ Z)) := by
      rwa [Set.insert_eq_of_mem hzAZ]
    exact (hsub.1 (M.buyer z)).mem_insert_of_subset hAZ h1
  · -- sellers: the mirror argument
    have hmem : z ∈ M.choiceS (M.seller z) (A ∪ Z) :=
      hS (M.seller z) (M.mem_sellerSide.mpr ⟨hz, rfl⟩)
    have h1 : z ∈ M.choiceS (M.seller z) (insert z (A ∪ Z)) := by
      rwa [Set.insert_eq_of_mem hzAZ]
    exact (hsub.2 (M.seller z)).mem_insert_of_subset hAZ h1

/-- Under substitutability, pairwise stability and stability coincide. -/
theorem pairwiseStable_iff_stable_of_substitutable (hsub : M.Substitutable)
    {A : Set X} : M.PairwiseStable A ↔ M.Stable A :=
  ⟨fun h => h.stable_of_substitutable M hsub, fun h => h.pairwiseStable M⟩

/-- Compatibility form of `PairwiseStable.stable_of_substitutable`. The IRC
argument is redundant; new callers can use the stronger theorem. -/
theorem PairwiseStable.stable (hsub : M.Substitutable) (_hcons : M.Consistent)
    {A : Set X} (h : M.PairwiseStable A) : M.Stable A :=
  h.stable_of_substitutable M hsub

/-- Compatibility form of `pairwiseStable_iff_stable_of_substitutable`. -/
theorem pairwiseStable_iff_stable (hsub : M.Substitutable)
    (_hcons : M.Consistent) {A : Set X} :
    M.PairwiseStable A ↔ M.Stable A :=
  M.pairwiseStable_iff_stable_of_substitutable hsub

/-! ### The seller- and buyer-chosen relations (`⊒S`, `⊒B`) -/

/-- `Y` is **seller-chosen** over `Z`: every seller chooses their part of `Y`
from `Y ∪ Z`. Under substitutability and IRC, this relation describes the
reverse of the lattice order on stable outcomes: `A ≤ A'` means
`SellerChosen A' A`. -/
def SellerChosen (Y Z : Set X) : Prop :=
  ∀ s, M.choiceS s (Y ∪ Z) = M.sellerSide s Y

/-- `Y` is **buyer-chosen** over `Z`. -/
def BuyerChosen (Y Z : Set X) : Prop :=
  ∀ b, M.choiceB b (Y ∪ Z) = M.buyerSide b Y

/-- Both relations are reflexive on individually rational outcomes. -/
theorem sellerChosen_self {A : Set X} (h : M.IndRational A) :
    M.SellerChosen A A := by
  intro s
  rw [Set.union_self, h.2 s]

theorem buyerChosen_self {A : Set X} (h : M.IndRational A) :
    M.BuyerChosen A A := by
  intro b
  rw [Set.union_self, h.1 b]

end Market

end MathEconLib.Matching
