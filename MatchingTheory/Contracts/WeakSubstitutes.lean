/-
Matching with contracts: weakened substitutability conditions (survey §6).

DRAFT — design signatures; not compiled. See SPEC.md. The implication proofs
here are the only real (non-`sorry`) proofs in the draft — deliberately, as
they demonstrate the payoff of defining `Substitutable` in choice language.
-/
import MatchingTheory.Contracts.Basic

/-!
# Weakened substitutability

The conditions of survey §6 — bilateral and unilateral substitutability
(Hatfield–Kojima 2010) and substitutable completability (Hatfield–Kominers
2020) — are the reason `ChoiceFunction.Substitutable` is *defined* in choice
language (SPEC D2, revised v0.3): each is that definition with restricted
quantifiers, so the implication chain

  `Substitutable → UnilaterallySubstitutable → BilaterallySubstitutable`

is quantifier bookkeeping, and both steps below are term-mode one-liners.

## Orientation

Two roles must not be conflated:

* The conditions are **imposed on** the multi-unit-demand side's choice
  functions — HK 2010's *hospitals*, Sönmez–Switzer's *branches*: the
  **buyers** of the survey's dictionary (fn. 9: sellers are the unit-demand
  doctors/workers).
* The **side conditions inside** the definitions quantify over the
  unit-demand counterparties of the contracts — HK 2010's `d(x), d(z) ∉ d(Y)`
  with `d` the *doctor* map: the **sellers** of the survey's dictionary.

Why the referenced side is the proposing, unit-demand side: violations
guarded away by the freshness conditions are exactly those a seller-proposing
cumulative offer process can never observe. Survey Example 6.1 is the
witness — the rescued contract `x′` shares its *seller* with the contract `x`
already on the menu, so the violation never materializes along the process.

Accordingly, the choice-layer definitions below take a neutral
`counterparty : X → A` map (they are market-relative — no bare
`ChoiceFunction` version exists), and the `Market` section instantiates the
§6 orientation: buyer choice functions with `counterparty := M.seller`. The
mirror instantiation (seller choice functions referencing buyers) is free if
a buyer-proposing variant is ever needed.

These are inherently finite-market notions, stated in the literature's
single-new-contract shape mirroring
`ChoiceFunction.Substitutable.not_mem_insert_insert`; no superset
generalization is attempted. **Fidelity caveat (SPEC §8 Q10):** the
statements are drafted from the survey's prose and must be certified against
HK 2010's original definitions before anything is built on them.

This file is a design stub establishing the family shape; the §6 development
proper (Thm 6.1/6.2 via completions as a reduction into the many-to-many
theorems, observable substitutability and Thm 6.3/6.4) is milestone M7+.
-/

namespace ChoiceFunction

variable {A : Type*} {X : Type*}

section Defs

variable (counterparty : X → A) (C : ChoiceFunction X)

/-- No contract in `Y` shares its counterparty with `x` — the literature's
`d(x) ∉ d(Y)` (Hatfield–Kojima 2010, `d` the doctor map; sellers, in the
survey's dictionary). -/
def Fresh (x : X) (Y : Set X) : Prop :=
  ∀ y ∈ Y, counterparty y ≠ counterparty x

/-- **Unilateral substitutability** (Hatfield–Kojima 2010): the
substitutability implication is required only when the *rejected* contract's
counterparty has no other contract on the menu. -/
def UnilaterallySubstitutable : Prop :=
  ∀ ⦃x z : X⦄ ⦃Y : Set X⦄, Fresh counterparty x Y →
    x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y))

/-- **Bilateral substitutability** (Hatfield–Kojima 2010): the implication is
required only when *both* the rejected contract's and the newly available
contract's counterparties have no contract on the menu. -/
def BilaterallySubstitutable : Prop :=
  ∀ ⦃x z : X⦄ ⦃Y : Set X⦄,
    Fresh counterparty x Y → Fresh counterparty z Y →
      x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y))

/-- `C'` is a **completion** of `C`: on every menu it either agrees with `C`
or chooses at least two contracts with a common counterparty
(Hatfield–Kominers 2020). -/
def IsCompletionOf (C' : ChoiceFunction X) : Prop :=
  ∀ Y, C' Y = C Y ∨
    ∃ x ∈ C' Y, ∃ x' ∈ C' Y, x ≠ x' ∧ counterparty x = counterparty x'

/-- **Substitutable completability**: some completion is substitutable. -/
def SubstitutablyCompletable : Prop :=
  ∃ C' : ChoiceFunction X, C.IsCompletionOf counterparty C' ∧ C'.Substitutable

end Defs

/-- Substitutability implies unilateral substitutability, for any
counterparty map: discard the side condition and apply the
single-new-contract form. -/
theorem Substitutable.unilaterallySubstitutable {C : ChoiceFunction X}
    (hC : C.Substitutable) (counterparty : X → A) :
    C.UnilaterallySubstitutable counterparty :=
  fun _x _z _Y _hfresh hx => hC.not_mem_insert_insert hx

/-- Unilateral substitutability implies bilateral substitutability:
strengthen the hypotheses. -/
theorem UnilaterallySubstitutable.bilaterallySubstitutable
    {counterparty : X → A} {C : ChoiceFunction X}
    (hC : C.UnilaterallySubstitutable counterparty) :
    C.BilaterallySubstitutable counterparty :=
  fun _x _z _Y hfx _hfz hx => hC hfx hx

end ChoiceFunction

/-! ## The §6 orientation, instantiated

Buyers (hospitals, branches) carry the weakened conditions; the side
conditions reference sellers (doctors, cadets). -/

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
to the seller map (survey §6.1; Hatfield–Kominers 2020). -/
def BuyersSubstitutablyCompletable : Prop :=
  ∀ b, (M.choiceB b).SubstitutablyCompletable M.seller

theorem buyersUnilaterallySubstitutable_of_substitutable
    (hsub : M.Substitutable) : M.BuyersUnilaterallySubstitutable :=
  fun b => (hsub.1 b).unilaterallySubstitutable M.seller

theorem buyersBilaterallySubstitutable_of_buyersUnilaterallySubstitutable
    (h : M.BuyersUnilaterallySubstitutable) :
    M.BuyersBilaterallySubstitutable :=
  fun b => (h b).bilaterallySubstitutable

/-! ### TODO (M7+)

* Certify all definitions against HK 2010 (SPEC §8 Q10).
* `Substitutable → SubstitutablyCompletable` (take `C' := C`).
* Observable substitutability and observable size monotonicity
  (Hatfield–Kominers–Westkamp 2021): quantified over *offer processes*, i.e.
  finite sequences of contracts — needs `List X`-based infrastructure; design
  alongside `Contracts/CumulativeOffer.lean`.
* Thm 6.1 as a reduction into `Market.exists_stable` for the completed
  market; the Example 6.1 market as a `decide` test that a non-substitutable
  but substitutably-completable profile has a stable outcome.
-/

end Market
