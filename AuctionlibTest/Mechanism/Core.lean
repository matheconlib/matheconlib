module

public import Auctionlib.Mechanism.Auctions.AllPurchase.Spec
public import Auctionlib.Mechanism.Core.SolutionConcepts

/-!
# Reporting rules, payments, and incentive compatibility

For a mechanism with agents `I`, action spaces `A i`, and outcomes `O`, sequential reporting maps
compose while preserving the resulting outcomes and transfers. Payments are money paid by agents,
and revenue sums those payments. Dominant-strategy incentive compatibility compares truthful
reporting with deviations, and efficiency maximizes total value across outcomes.

The all-purchase example relates its payment and prize rules to a positive posted price and a
continuous, strictly decreasing scarcity schedule. A mechanism with agents indexed by `ℕ` provides
an example with Boolean actions, a single outcome, and zero transfers.

## Main definitions

* `infiniteAgentMechanism`: a mechanism with agents indexed by `ℕ`, Boolean actions, a single
  outcome, and zero transfers.

## Main statements

* `comap_composition`: sequential reporting maps agree with their composition.
* `payment_sign` and `revenue_payments`: payments negate transfers, and revenue sums payments.
* `dsic_scope` and `efficiency_scope`: truthfulness compares reports at fixed true types, and
  efficiency maximizes total value.
* `allPurchase_existence`: all-purchase rules admit a posted-price and scarcity specification.

## Tags

mechanism design, reporting rules, transfers, revenue, incentive compatibility, welfare
-/

@[expose] public section

open Auctionlib.Mechanism Auctionlib.Mechanism.Auctions

namespace Auctionlib.Tests.Mechanism

universe uI uA uB uC uΘ uO

variable {I : Type uI} {A : I → Type uA} {B : I → Type uB} {C : I → Type uC}
variable {Θ : I → Type uΘ} {O : Type uO}

/-- Applying the reporting map `τ` and then `σ` gives the same outcome and transfers as applying
their composition. -/
lemma comap_composition (M : Mechanism I A O)
    (σ : ∀ i, B i → A i) (τ : ∀ i, C i → B i) :
    (M.comap σ).comap τ = M.comap (fun i => σ i ∘ τ i) := M.comap_comp σ τ

/-- Identity reporting preserves the entire mechanism. -/
lemma comap_identity (M : Mechanism I A O) : M.comap (fun _ => id) = M := M.comap_id

/-- Payments are money leaving the agent, so they negate the signed transfer. -/
lemma payment_sign (M : Mechanism I A O) (i : I) (a : Profile A) :
    M.payment i a = -M.transfer i a := rfl

/-- Revenue is the sum of agents' payments, with a positive payment representing money collected
from the agent. -/
lemma revenue_payments [Fintype I] (M : Mechanism I A O) (a : Profile A) :
    M.revenue a = ∑ i, M.payment i a := M.revenue_eq_sum_payment a

/-- DSIC fixes true types while allowing arbitrary reports by the other agents. -/
lemma dsic_scope [DecidableEq I] (E : QuasilinearEnvironment I Θ O)
    (M : DirectMechanism I Θ O) :
    DirectMechanism.IsDSIC E M ↔ ∀ i (θ r : Profile Θ),
      E.utility M i θ r ≤ E.utility M i θ (Function.update r i (θ i)) := Iff.rfl

/-- Efficiency requires the outcome chosen at each type profile to maximize the sum of agents'
values over all outcomes `O`. -/
lemma efficiency_scope [Fintype I] (E : QuasilinearEnvironment I Θ O)
    (M : DirectMechanism I Θ O) :
    DirectMechanism.IsEfficient E M ↔
      ∀ θ o, E.totalValue θ o ≤ E.totalValue θ (M.outcome θ) :=
  DirectMechanism.isEfficient_iff E M

/-- A mechanism is all-purchase exactly when a positive posted price and a continuous, strictly
decreasing scarcity schedule support its payment rule and its prize rule awarding the prize to the
unique highest bidder. -/
lemma allPurchase_existence [Fintype I]
    (M : Mechanism I (fun _ => ℝ) O) (alloc : O → I → ℝ) :
    IsAllPurchase M alloc ↔ Nonempty (AllPurchaseSpec M alloc) := Iff.rfl

/-- A mechanism with agents indexed by `ℕ`, Boolean actions, a single outcome, and zero
transfers. -/
def infiniteAgentMechanism : Mechanism ℕ (fun _ => Bool) Unit where
  outcome _ := ()
  transfer _ _ := 0

/-- Each agent pays zero in `infiniteAgentMechanism`, for every action profile. -/
lemma infiniteAgentMechanism_payment (i : ℕ) (a : ℕ → Bool) :
    infiniteAgentMechanism.payment i a = 0 := neg_zero

end Auctionlib.Tests.Mechanism
