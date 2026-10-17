/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
/-
Matching with contracts: weakened substitutability conditions.
-/
import MathEconLib.Matching.Contracts.Basic
import MathEconLib.Choice.Matching.Relationships

/-!
# Buyer weak substitutes and completion hypotheses

Buyers are the hospitals/branches and sellers the unit-demand doctors/cadets
in Hatfield–Kojima (2010). The completion framework follows
Hatfield–Kominers (2025), §6.1, p. 471. Weak substitutability is imposed on
each buyer's choice with freshness measured by `M.seller`.
The choice-level definitions live in
`Choice/Matching/WeakSubstitutability.lean`; completion and
completability definitions and elementary facts live in
`Choice/Matching/Completion.lean`. Neither imports the market layer.

A completion-based existence reduction requires IRC of the same completion
that satisfies substitutability. `BuyersHaveConsistentSubstitutableCompletions`
records this joint requirement. The survey's completion definition and
Definition 6.1, p. 471, do not separately include IRC; the chapter assumes
IRC throughout (p. 413). Lean keeps the bare formula and the joint
requirement separate. The choice-level substitute-hull theorem
supplies such completions from unilateral substitutability, IRC, counterparty
feasibility, and finite-valued buyer choice. Neither the contract type nor the
agent types need be finite for this implication. Its finite-contract
specialization is also provided below.

These are hypotheses and choice-level implications. The market reduction in
`Contracts/Completion.lean` combines them with seller unit demand and IRC to
obtain stable outcomes in the original market.

## References

* John William Hatfield and Scott Duke Kominers (2025), *The theory of
  matching with contracts*, Chapter 5, Handbook of the Economics of
  Matching 2, 409–487, https://doi.org/10.1016/bs.hesmat.2025.10.005.
* Jun Zhang (2016), *On sufficient conditions for the existence of stable
  matchings with contracts*, Economics Letters 145, 230–234,
  https://doi.org/10.1016/j.econlet.2016.06.029.
-/

namespace MathEconLib.Matching

open MathEconLib.Choice

namespace Market

variable {B : Type*} {S : Type*} {X : Type*} (M : Market B S X)

/-- Every **buyer**'s choice function is unilaterally substitutable, side
conditions referencing **sellers**. See `Choice/Matching/WeakSubstitutability.lean`
for the checked literature definitions and the counterparty convention. -/
def BuyersUnilaterallySubstitutable : Prop :=
  ∀ b, (M.choiceB b).UnilaterallySubstitutable M.seller

/-- Every buyer's choice function is bilaterally substitutable, side
conditions referencing sellers. -/
def BuyersBilaterallySubstitutable : Prop :=
  ∀ b, (M.choiceB b).BilaterallySubstitutable M.seller

/-- Every buyer's choice function is substitutably completable with respect
to the seller map (Hatfield–Kominers 2025, §6.1, Definition 6.1, p. 471).
This predicate omits the survey's standing IRC assumption; the joint
requirement is recorded below. -/
def BuyersSubstitutablyCompletable : Prop :=
  ∀ b, (M.choiceB b).SubstitutablyCompletable M.seller

/-- Every buyer has one completion satisfying both substitutability and
IRC. Bare `BuyersSubstitutablyCompletable` does not assert the latter. -/
def BuyersHaveConsistentSubstitutableCompletions : Prop :=
  ∀ b, (M.choiceB b).HasConsistentSubstitutableCompletion M.seller

theorem buyersUnilaterallySubstitutable_of_substitutable
    (hsub : M.Substitutable) : M.BuyersUnilaterallySubstitutable :=
  fun b => (hsub.1 b).unilaterallySubstitutable M.seller

theorem buyersBilaterallySubstitutable_of_buyersUnilaterallySubstitutable
    (h : M.BuyersUnilaterallySubstitutable) :
    M.BuyersBilaterallySubstitutable :=
  fun b => (h b).bilaterallySubstitutable

/-- Ordinary substitutes are a special case of substitutable completability. -/
theorem buyersSubstitutablyCompletable_of_substitutable
    (hsub : M.Substitutable) : M.BuyersSubstitutablyCompletable :=
  fun b => (hsub.1 b).substitutablyCompletable M.seller

/-- Ordinary substitutes with IRC provide consistent substitutable completions. -/
theorem buyersHaveConsistentSubstitutableCompletions
    (hsub : M.Substitutable) (hcons : M.Consistent) :
    M.BuyersHaveConsistentSubstitutableCompletions :=
  fun b => (hsub.1 b).hasConsistentSubstitutableCompletion (hcons.1 b) M.seller

/-- The finite-valued strengthening with an IRC completion of Zhang (2016),
Proposition 2, p. 233, applied separately to each buyer. Zhang establishes
bare substitutable completability; the additional IRC conclusion follows
from the hull theorem proved here. Only buyer-side hypotheses enter this
result; seller regularity is needed when using the completions in a market
reduction. -/
theorem buyersHaveConsistentSubstitutableCompletions_of_unilaterallySubstitutable_of_finiteValued
    (hUS : M.BuyersUnilaterallySubstitutable)
    (hcons : ∀ b, (M.choiceB b).Consistent)
    (hfeasible : ∀ b Y, Set.InjOn M.seller (M.choiceB b Y))
    (hfinite : ∀ b, (M.choiceB b).FiniteValued) :
    M.BuyersHaveConsistentSubstitutableCompletions :=
  fun b => (hUS b).hasConsistentSubstitutableCompletion_of_finiteValued
    (hcons b) (hfeasible b) (hfinite b)

/-- Finite-contract specialization. The buyer and seller types remain arbitrary. -/
theorem buyersHaveConsistentSubstitutableCompletions_of_unilaterallySubstitutable
    [Finite X] (hUS : M.BuyersUnilaterallySubstitutable)
    (hcons : ∀ b, (M.choiceB b).Consistent)
    (hfeasible : ∀ b Y, Set.InjOn M.seller (M.choiceB b Y)) :
    M.BuyersHaveConsistentSubstitutableCompletions :=
  M.buyersHaveConsistentSubstitutableCompletions_of_unilaterallySubstitutable_of_finiteValued
    hUS hcons hfeasible (fun _ _ => Set.toFinite _)

/-- A substitutable completion of a buyer's choice still selects only that
buyer's contracts. Thus support need not be postulated separately when
constructing a market of substitutable completions. -/
theorem buyer_eq_of_mem_completion {b : B} {D : ChoiceFunction X}
    (hcomp : (M.choiceB b).IsCompletionOf M.seller D)
    (hsub : D.Substitutable) {Y : Set X} {x : X} (hx : x ∈ D Y) :
    M.buyer x = b :=
  hcomp.preserves_support hsub
    (P := {x | M.buyer x = b})
    (fun _Y _x hx' => M.buyer_eq_of_mem hx') Y hx

end Market

end MathEconLib.Matching
