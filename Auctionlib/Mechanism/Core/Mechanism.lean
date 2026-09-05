/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Mechanism.Core.Profile
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic

/-!
# Mechanisms and signed transfers

A mechanism selects an outcome and a monetary transfer for each agent from a profile of actions.
Agents may have different action spaces. A positive transfer is money received by the agent, and a
negative transfer is money paid by the agent. The designer's revenue is the sum of the agents'
payments.

In a direct mechanism, each agent's action is a report of their type. The reported types determine
the outcome and transfers; truthful reporting means that every agent reports their own true type.

## Main definitions

* `Mechanism`: an outcome rule and signed monetary transfers on agents' action profiles.
* `DirectMechanism`: a mechanism whose actions are reports of agents' types.
* `Mechanism.payment`: the money charged to an agent at an action profile.
* `Mechanism.revenue`: the designer's net monetary receipts at an action profile.

## Main statements

* `Mechanism.payment_eq_neg_transfer`: an agent's payment is the negative of their transfer.
* `Mechanism.revenue_eq_neg_sum_transfer`: revenue is the negative of total transfers to agents.
* `Mechanism.revenue_eq_sum_payment`: revenue is the sum of agents' payments.

## Tags

mechanism design, direct mechanisms, transfers, payments, revenue
-/

@[expose] public section

-- The carrier `Mechanism` belongs to the library's `Auctionlib.Mechanism` namespace.
set_option linter.dupNamespace false

universe uI uA uO

namespace Auctionlib.Mechanism

/-- An outcome rule and monetary transfers for agents `I`, where `A i` is the action space of agent
`i` and `O` is the outcome space. At an action profile `a`, `outcome a` is the selected outcome and
`transfer i a` is agent `i`'s net monetary receipt: positive amounts are received by the agent, and
negative amounts are paid by the agent. -/
@[ext]
structure Mechanism (I : Type uI) (A : I → Type uA) (O : Type uO) where
  /-- The outcome selected at an action profile. -/
  outcome : Profile A → O
  /-- Net money received by agent `i` at an action profile, negative when the agent pays. -/
  transfer : (i : I) → Profile A → ℝ

/-- A mechanism in which each agent `i : I` reports a type in `Θ i`. The reported profile
determines an outcome in `O` and monetary transfers. Reports may differ from agents' true types;
truthful reporting means that each agent reports their own true type. -/
abbrev DirectMechanism (I : Type uI) (Θ : I → Type uA) (O : Type uO) :=
  Mechanism I Θ O

namespace Mechanism

variable {I : Type uI} {A : I → Type uA} {O : Type uO} (M : Mechanism I A O)

/-- The payment charged to agent `i`, the negative of money received by that agent. -/
def payment (i : I) (a : Profile A) : ℝ := -M.transfer i a

/-- An agent's payment is the negative of the monetary transfer they receive. -/
@[simp] theorem payment_eq_neg_transfer (i : I) (a : Profile A) :
    M.payment i a = -M.transfer i a := rfl

/-- The designer's net receipts, the negative of total money received by agents. -/
def revenue [Fintype I] (a : Profile A) : ℝ := -∑ i, M.transfer i a

/-- The designer's revenue is the negative of total monetary transfers to agents. -/
@[simp] theorem revenue_eq_neg_sum_transfer [Fintype I] (a : Profile A) :
    M.revenue a = -∑ i, M.transfer i a := rfl

/-- The designer's revenue is the sum of the payments charged to agents. -/
theorem revenue_eq_sum_payment [Fintype I] (a : Profile A) :
    M.revenue a = ∑ i, M.payment i a := by
  simp only [revenue, payment, Finset.sum_neg_distrib]

end Mechanism

end Auctionlib.Mechanism

end
