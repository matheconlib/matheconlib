/-
Matching with contracts, Layer 1: two-sided markets and stability.
-/
import Matching.Choice.Basic

/-!
# Two-sided markets with contracts

A contract is an element of a bare type `X` equipped with maps to
the buyer type `B` and seller type `S`; the "terms" of the contract
are absorbed into contract identity. A market attaches one `ChoiceFunction X`
to every agent, subject only to the *support* condition (agents choose only
contracts to which they are associated).

Irrelevance of rejected contracts (IRC) and substitutability are theorem
hypotheses via the market-level predicates below, never structure fields —
the maximal-domain theorems (survey Thm 2.7/3.6) need non-substitutable instances.

Everything here is implemented at Hatfield--Kominers **many-to-many generality**.
No unit-demand or unitarity hypothesis appears in this file or in `FixedPoint.lean`.

## Main definitions

* `Market B S X` — the carrier.
* `Market.buyerSide`, `Market.sellerSide` — an agent's contracts within a set.
* `Market.Consistent`, `Market.Substitutable`, `Market.SizeMonotone` —
  hypothesis bundles quantifying the choice-layer predicates over all agents.
* `Market.IndRational`, `Market.Blocks`, `Market.Stable`,
  `Market.PairwiseStable` — survey Definitions 2.3/2.4.
* `Market.SellerChosen`, `Market.BuyerChosen` — the relations `⊒S`, `⊒B`.

## Main statements

* `Market.choiceB_buyerSide` — locality from set-form IRC (one line; the
  reason IRC is taken in set form).
* `Market.Stable.pairwiseStable`, `Market.pairwiseStable_iff_stable` —
  survey Theorem 2.1(i)–(ii)/3.1.
-/

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

/-! ### Hypothesis bundles -/

/-- Every agent's choice function satisfies the IRC condition. -/
def Consistent : Prop :=
  (∀ b, (M.choiceB b).Consistent) ∧ ∀ s, (M.choiceS s).Consistent

/-- Every agent's choice function is substitutable. -/
def Substitutable : Prop :=
  (∀ b, (M.choiceB b).Substitutable) ∧ ∀ s, (M.choiceS s).Substitutable

/-- Every agent's choice function satisfies the law of aggregate demand. -/
def SizeMonotone : Prop :=
  (∀ b, (M.choiceB b).SizeMonotone) ∧ ∀ s, (M.choiceS s).SizeMonotone

/-! ### Locality

Under set-form IRC and the support condition, an agent's choice depends only
on their own contracts — this is a *lemma*, not an axiom of `Market`.

Paper proof (finiteness-free): with `Z := buyerSide b Y` we have
`choiceB b Y ⊆ Z` by support and `Z ⊆ Y` by definition; apply `Consistent`. -/

theorem choiceB_buyerSide {b : B} (h : (M.choiceB b).Consistent) (Y : Set X) :
    M.choiceB b (M.buyerSide b Y) = M.choiceB b Y := by
  sorry

theorem choiceS_sellerSide {s : S} (h : (M.choiceS s).Consistent) (Y : Set X) :
    M.choiceS s (M.sellerSide s Y) = M.choiceS s Y := by
  sorry

/-! ### Stability (survey Definitions 2.3 and 2.4) -/

/-- An outcome `A` is **individually rational** if every agent chooses exactly
their part of `A` from `A`. -/
def IndRational (A : Set X) : Prop :=
  (∀ b, M.choiceB b A = M.buyerSide b A) ∧
    ∀ s, M.choiceS s A = M.sellerSide s A

/-- `Z` **blocks** `A`: `Z` is a nonempty set of new contracts, all of which
every involved agent takes when offered `A ∪ Z`. (For an agent with no
contract in `Z` the condition is vacuous — survey fn. 17.) -/
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

/-- Theorem 2.1(i): stable outcomes are pairwise stable. -/
theorem Stable.pairwiseStable {A : Set X} (h : M.Stable A) :
    M.PairwiseStable A :=
  ⟨h.1, fun z => h.2 {z}⟩

/-- Theorem 2.1(ii)/3.1: under substitutability (and IRC), a blocking set
yields a blocking contract, so pairwise stability implies stability.

Proof plan (survey, after Thm 2.1): take `z ∈ Z` for a blocking set `Z`;
substitutability in the `mem_insert_of_subset` form applied to
`A ∪ {z} ⊆ A ∪ Z` shows `{z}` blocks. -/
theorem PairwiseStable.stable (hsub : M.Substitutable) (hcons : M.Consistent)
    {A : Set X} (h : M.PairwiseStable A) : M.Stable A := by
  sorry

theorem pairwiseStable_iff_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} :
    M.PairwiseStable A ↔ M.Stable A :=
  ⟨fun h => h.stable M hsub hcons, fun h => h.pairwiseStable M⟩

/-! ### The seller- and buyer-chosen relations (`⊒S`, `⊒B`) -/

/-- `Y` is **seller-chosen** over `Z`: every seller chooses their part of `Y`
from `Y ∪ Z`. On stable outcomes this is the order `⊒S`; its order structure
is developed in `Matching.Contracts.Order` by transport from the fixed-point
lattice, not proved directly. -/
def SellerChosen (Y Z : Set X) : Prop :=
  ∀ s, M.choiceS s (Y ∪ Z) = M.sellerSide s Y

/-- `Y` is **buyer-chosen** over `Z`. -/
def BuyerChosen (Y Z : Set X) : Prop :=
  ∀ b, M.choiceB b (Y ∪ Z) = M.buyerSide b Y

/-! ### Decidability

`Decidable` instances for `IndRational`, `Blocks`, `Stable` under
`[Fintype X]` + decidable choice functions live in a dedicated file once the
encoding question (SPEC §8 Q5: `Fintype (Set X)` vs a `Finset` mirror) is
settled on Example 2.1. -/

end Market
