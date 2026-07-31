module

public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# Single-Parameter Problems

This file defines a deterministic choice problem for an agent whose private
type is a real number.

The agent chooses an action of type `Action`. An action determines an
allocation and a payment. The allocation is a number in `[0, 1]`, interpreted
as the probability of receiving one indivisible object. The payment is positive
when the agent pays and negative when the agent receives a transfer.

The agent's payoff is quasilinear:

`payoff(v, a) = v * allocation(a) - payment(a)`.

The action type is arbitrary. For example, an action can be a bid, a report, a
contract choice, or a complete response plan in a bargaining procedure.

This structure contains no probability distribution and no seller objective.
Those belong to later layers of the pricing development.
-/

@[expose] public section

open Set

universe u

/-- A deterministic choice problem for an agent with a one-dimensional type.

The type lies in the closed interval `[lowestType, highestType]`. The
`strategy` field records the action selected by each type.

The structure does not assume that `lowestType ≤ highestType`. A theorem that
needs a nonempty type interval can assume that inequality or work with a type
already known to belong to the interval. This matches the existing
`BidderProblem` convention. -/
structure SingleParameterProblem (Action : Type u) where
  /-- Lower endpoint of the type interval. -/
  lowestType : ℝ
  /-- Upper endpoint of the type interval. -/
  highestType : ℝ
  /-- Allocation produced by an action. -/
  allocation : Action → ℝ
  /-- Every allocation lies in the closed interval `[0, 1]`. -/
  allocation_range : ∀ a, allocation a ∈ Icc 0 1
  /-- Payment made by the agent after choosing an action. -/
  payment : Action → ℝ
  /-- Action selected by each type. -/
  strategy : ℝ → Action

namespace SingleParameterProblem

variable {Action : Type u} (P : SingleParameterProblem Action)

/-- The closed interval of types considered by the problem. -/
abbrev typeInterval : Set ℝ := Icc P.lowestType P.highestType

/-! ## Derived quantities -/

/-- Payoff of type `v` from action `a`.

A positive payment is subtracted from the agent's value for the allocation. -/
def payoff (v : ℝ) (a : Action) : ℝ :=
  v * P.allocation a - P.payment a

/-- Allocation received when type `v` follows the strategy. -/
def q (v : ℝ) : ℝ :=
  P.allocation (P.strategy v)

/-- Utility received when type `v` follows the strategy. -/
def U (v : ℝ) : ℝ :=
  P.payoff v (P.strategy v)

@[simp]
lemma payoff_eq (v : ℝ) (a : Action) :
    P.payoff v a = v * P.allocation a - P.payment a :=
  rfl

@[simp]
lemma q_eq (v : ℝ) :
    P.q v = P.allocation (P.strategy v) :=
  rfl

@[simp]
lemma U_eq (v : ℝ) :
    P.U v = v * P.allocation (P.strategy v) - P.payment (P.strategy v) :=
  rfl

/-- The allocation received under the strategy also lies in `[0, 1]`. -/
lemma q_range (v : ℝ) :
    P.q v ∈ Icc 0 1 :=
  P.allocation_range (P.strategy v)

end SingleParameterProblem

end
