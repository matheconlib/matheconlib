/-
Matching with contracts: weakened substitutability conditions (survey §6).
-/
import MatchingTheory.Contracts.Basic
import MatchingTheory.Choice.WeakSubstitutes

/-!
# Market-level weak substitutability

Buyers are the hospitals/branches and sellers the unit-demand doctors/cadets
in the orientation of survey §6. Accordingly, weak substitutability is
imposed on each buyer's choice with freshness measured by `M.seller`.
The choice-level definitions and elementary completion API live in
`Choice/WeakSubstitutes.lean`, which does not import the market layer.

The completion-based existence theorem requires IRC of the same completion
that satisfies substitutability. The stronger hypothesis below records this
explicitly. Original buyer IRC cannot silently substitute for completion IRC.
Sellers' unit demand and regularity belong in the eventual reduction theorem,
not in these definitions.
-/

namespace Market

variable {B : Type*} {S : Type*} {X : Type*} (M : Market B S X)

/-- Every **buyer**'s choice function is unilaterally substitutable, side
conditions referencing **sellers** — the orientation of survey §6 and all its
applications (cadet–branch, IPMM). -/
def BuyersUnilaterallySubstitutable : Prop :=
  ∀ b, (M.choiceB b).UnilaterallySubstitutable M.seller

/-- Every buyer's choice function is bilaterally substitutable, side
conditions referencing sellers. -/
def BuyersBilaterallySubstitutable : Prop :=
  ∀ b, (M.choiceB b).BilaterallySubstitutable M.seller

/-- Every buyer's choice function is substitutably completable with respect
to the seller map (survey §6.1; Hatfield–Kominers, *Hidden Substitutes*). -/
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
