/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
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
This flexibility concerns how actions are represented; utility must still be
affine in the type. A genuinely nonseparable primitive such as `V(v, a)` is
outside this structure.

This structure contains no probability distribution and no seller objective.
Those belong to later layers of the pricing development.
-/

namespace MathEconLib

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

/-! ## Changing strategy and passing to reduced form -/

/-- Replace the strategy while keeping the type bounds, allocation rule, and
payment rule fixed.

A `SingleParameterProblem` bundles the rules of the choice problem together
with a strategy. Consequently, its incentive-compatibility predicates concern
this entire mechanism-and-strategy pair. Replacing the strategy creates a new
problem whose incentive compatibility must be established separately. -/
def withStrategy (newStrategy : ℝ → Action) : SingleParameterProblem Action :=
  { P with strategy := newStrategy }

/-- Replacing a problem's strategy with the strategy it already has leaves the
problem unchanged. -/
theorem withStrategy_self : P.withStrategy P.strategy = P :=
  rfl

/-- The canonical direct reduced form of a single-parameter problem.

A reduced action is a reported type `w`. It produces the allocation and
payment generated when the original strategy chooses `P.strategy w`, while
truthful behavior in the reduced problem is the identity strategy.

This construction retains the on-strategy quantities used by envelope and
type-deviation IC. It can forget original actions outside the image of
`P.strategy`, so it does not by itself give an equivalence for universal IC. -/
def reduce : SingleParameterProblem ℝ where
  lowestType := P.lowestType
  highestType := P.highestType
  allocation := P.q
  allocation_range := P.q_range
  payment := fun w => P.payment (P.strategy w)
  strategy := id

/-- The reduced problem has the same induced allocation as the original
problem. -/
theorem reduce_q :
    P.reduce.q = P.q :=
  rfl

/-- The reduced problem has the same on-strategy utility as the original
problem. -/
theorem reduce_U :
    P.reduce.U = P.U :=
  rfl

/-- The payoff from reporting `w` in the reduced problem is the payoff from
the corresponding strategy action in the original problem. -/
theorem reduce_payoff (v w : ℝ) :
    P.reduce.payoff v w = P.payoff v (P.strategy w) :=
  rfl

end SingleParameterProblem

end

end MathEconLib
