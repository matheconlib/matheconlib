# Pricing Foundations: Mathematical Model and Compatibility Plan

## Status of this document

This is a design document. It describes definitions that are planned for later
commits, but it does not add or change any Lean definitions.

The first application will be optimal posted pricing for one buyer. The
foundations are intended to be reusable for auctions, screening, contracts,
and bargaining problems with a one-dimensional private type.

## Compatibility promise

The pricing development will extend the existing library without breaking its
current public interface.

In particular:

- `Mechanism`, `Auction`, and `BidderProblem` will remain available.
- Existing structure fields will keep their present names and meanings.
- Existing theorem names and theorem statements will continue to compile.
- Existing typeclass instances will not silently acquire stronger assumptions.
- New general definitions will be connected to existing definitions by
  explicit conversion functions and compatibility lemmas.
- A full build of the existing library will be required after every pull
  request.

Some existing proofs may eventually be shortened by applying a more general
theorem. Such a change is acceptable only when the statement available to
users remains unchanged.

## 1. The mathematical model

### 1.1 Types and actions

An agent has a private type

\[
v \in [\underline v,\overline v].
\]

The type is a real number. In the pricing application, `v` is the buyer's
value for receiving the object.

The agent chooses an action from a type `Action`. We do not require actions to
be real numbers. Depending on the application, an action might be:

- a bid;
- a report;
- a contract choice;
- a quantity choice;
- a complete response plan in a bargaining procedure.

Using an arbitrary action type is the main generalization beyond the current
`BidderProblem`, where every action is a real-valued bid.

### 1.2 Allocation and payment

Each action `a` determines:

- an allocation `x(a)` in the interval `[0, 1]`;
- a payment `t(a)` in `ℝ`.

The allocation can be interpreted as a probability of receiving one
indivisible object. A payment is positive when the agent pays the mechanism.
A negative payment is a transfer to the agent.

The initial development is therefore a single-unit model. More general
quantity spaces or multiple goods may require a later abstraction.

### 1.3 Strategy, payoff, allocation, and utility

A strategy maps each type to an action:

\[
\sigma : \mathbb R \to \mathit{Action}.
\]

The agent has quasilinear payoff

\[
\pi(v,a)=v\,x(a)-t(a).
\]

The allocation induced by the strategy is

\[
q(v)=x(\sigma(v)).
\]

The agent's utility when following the strategy is

\[
U(v)=\pi(v,\sigma(v))
    =v\,q(v)-t(\sigma(v)).
\]

The words `allocation` and `payment` will be used in new general definitions.
They correspond to `winProb` and `cost` in the existing `BidderProblem`.

## 2. Incentive compatibility

The existing library has three levels of incentive compatibility. The general
single-parameter model will retain the same hierarchy.

### 2.1 Envelope incentive compatibility

Envelope incentive compatibility requires

\[
(v-v')q(v') \le U(v)-U(v')
\]

for types `v` and `v'` in the type interval.

This is the weakest of the three conditions. It is sufficient for the
envelope theorem used in the existing library.

### 2.2 Type-deviation incentive compatibility

Type-deviation incentive compatibility requires type `v` to prefer its own
strategy action to the action assigned to any other type `v'`:

\[
\pi(v,\sigma(v')) \le \pi(v,\sigma(v)).
\]

This condition implies envelope incentive compatibility.

### 2.3 Universal incentive compatibility

Universal incentive compatibility requires type `v` to prefer its strategy
action to every feasible action `a`:

\[
\pi(v,a) \le \pi(v,\sigma(v)).
\]

This condition implies type-deviation incentive compatibility because
`σ(v')` is one of the feasible actions.

The intended implication chain is

\[
\text{Universal IC}
\Longrightarrow
\text{Type-deviation IC}
\Longrightarrow
\text{Envelope IC}.
\]

## 3. Envelope and payment results

The induced allocation `q` is nondecreasing under incentive compatibility.
The envelope theorem gives

\[
U(v)
=U(\underline v)
+\int_{\underline v}^{v}q(s)\,ds.
\]

Combining this identity with

\[
U(v)=v\,q(v)-t(\sigma(v))
\]

gives the payment identity

\[
t(\sigma(v))
=v\,q(v)-U(\underline v)
 -\int_{\underline v}^{v}q(s)\,ds.
\]

These are deterministic results. They do not require:

- a probability space;
- a probability distribution for the type;
- a density;
- independence from other agents;
- a seller objective.

Keeping these assumptions out of the single-parameter structure will make the
results usable in settings other than auctions.

## 4. Planned Lean interface

The snippets in this section are proposed syntax. They are included to make
the mathematical design precise, but they are not yet part of the Lean
library.

Some notation used below:

- `ℝ` is the type of real numbers.
- `A → B` is the type of functions from `A` to `B`.
- `∀ a, ...` means "for every `a`."
- `a ∈ S` means that `a` belongs to the set `S`.
- `:=` introduces the definition of a name.
- `/-- ... -/` is a documentation comment attached to the declaration that
  follows it.

### 4.1 Core structure

```lean
universe u

structure SingleParameterProblem (Action : Type u) where
  /-- Lower endpoint of the type interval. -/
  lowestType : ℝ

  /-- Upper endpoint of the type interval. -/
  highestType : ℝ

  /-- Allocation produced by an action. -/
  allocation : Action → ℝ

  /-- Every allocation lies in the interval `[0, 1]`. -/
  allocation_range : ∀ a, allocation a ∈ Set.Icc 0 1

  /-- Payment made by the agent after choosing an action. -/
  payment : Action → ℝ

  /-- Action selected by each type. -/
  strategy : ℝ → Action
```

The parameter

```lean
Action : Type u
```

means that `Action` can be any Lean type in a universe named `u`. No topology,
measurable space, order, or algebraic structure is imposed on actions.

As in the current `BidderProblem`, the structure records the two endpoints but
does not bundle a proof that `lowestType ≤ highestType`. A theorem that needs a
nonempty type interval will assume that fact or obtain it from a type known to
belong to the interval. This choice makes the later conversion from
`BidderProblem` unconditional.

### 4.2 Derived definitions

```lean
namespace SingleParameterProblem

variable {Action : Type u} (P : SingleParameterProblem Action)

/-- The closed interval of types considered by the problem. -/
abbrev typeInterval : Set ℝ :=
  Set.Icc P.lowestType P.highestType

/-- Payoff of type `v` from action `a`. -/
def payoff (v : ℝ) (a : Action) : ℝ :=
  v * P.allocation a - P.payment a

/-- Allocation received when type `v` follows the strategy. -/
def q (v : ℝ) : ℝ :=
  P.allocation (P.strategy v)

/-- Utility received when type `v` follows the strategy. -/
def U (v : ℝ) : ℝ :=
  P.payoff v (P.strategy v)

end SingleParameterProblem
```

The names `q` and `U` match the existing `BidderProblem` API.

### 4.3 Type-deviation incentive compatibility

```lean
class HasTypeDeviationIC
    {Action : Type u} (P : SingleParameterProblem Action) : Prop where
  typeDeviationIC :
    ∀ v ∈ P.typeInterval, ∀ v' ∈ P.typeInterval,
      P.payoff v (P.strategy v') ≤
        P.payoff v (P.strategy v)
```

Reading the quantified variables from left to right:

1. `v` is the agent's true type;
2. the first membership proof says that `v` is in the type interval;
3. `v'` is another type whose strategy action might be copied;
4. the second membership proof says that `v'` is in the type interval;
5. the inequality says that copying `v'` is no better than following the
   strategy for `v`.

### 4.4 Universal incentive compatibility

Universal incentive compatibility will use a feasible set

```lean
S : Set Action
```

instead of the current `Set ℝ`. Its mathematical content will be:

```lean
class HasUniversalIC
    {Action : Type u}
    (P : SingleParameterProblem Action)
    (S : outParam (Set Action)) : Prop where
  strategyInS :
    ∀ v ∈ P.typeInterval, P.strategy v ∈ S

  universalIC :
    ∀ v ∈ P.typeInterval, ∀ a ∈ S,
      P.payoff v a ≤ P.payoff v (P.strategy v)
```

The `outParam` annotation follows the existing `BidderProblem` design. It
allows Lean's typeclass search to infer the intended feasible action set.

## 5. Relationship to `BidderProblem`

The current `BidderProblem` will not be renamed or replaced.

A later commit will define a conversion whose fields have the following
correspondence:

| General field | Existing `BidderProblem` field |
|---|---|
| `lowestType` | `lowestType` |
| `highestType` | `highestType` |
| `allocation` | `winProb` |
| `allocation_range` | `winProb_range` |
| `payment` | `cost` |
| `strategy` | `strategy` |

The intended conversion has the shape

```lean
def BidderProblem.toSingleParameterProblem
    (B : BidderProblem) :
    SingleParameterProblem ℝ
```

Compatibility lemmas will state that, after conversion:

- the general payoff equals `BidderProblem.payoff`;
- the general induced allocation equals `BidderProblem.q`;
- the general utility equals `BidderProblem.U`;
- existing IC assumptions imply their general counterparts.

Existing auction code will continue to construct and use `BidderProblem`.
There is no requirement that existing applications immediately migrate to the
new structure.

## 6. Separation from distributions and seller objectives

The following data will be introduced in later pull requests, not in the
single-parameter problem:

- the probability distribution of the type;
- a density or cumulative distribution function;
- seller marginal cost;
- the seller's value for retaining the object;
- the cost of finding another buyer;
- continuation value from future buyers.

This separation matters mathematically:

- incentive compatibility describes the agent's choice problem;
- a value distribution determines expectations;
- a pricing problem specifies the seller's objective.

For example, Riley and Zeckhauser's cost of bringing a buyer into the store is
not the same object as the buyer's payment or the seller's marginal cost of
making a sale.

## 7. Decisions intentionally postponed

This design does not yet settle:

- general quantities outside `[0, 1]`;
- multidimensional types;
- multiple goods;
- non-quasilinear utility;
- risk-averse buyers;
- extensive-form syntax for bargaining histories;
- probability distributions and densities;
- seller optimization.

These topics should not complicate the first reusable layer unless a concrete
application shows that they are necessary.

## 8. Review checklist for later commits

Before a later commit changes Lean code, it should answer:

1. Does the new declaration belong to the deterministic single-parameter
   layer, the distribution layer, or an economic application?
2. Can the result be stated without auction-specific terminology?
3. Does an existing declaration already express the same idea?
4. If existing proofs are refactored, are their public statements unchanged?
5. Does the full existing library still build?

The goal is not abstraction for its own sake. Each generalization should make
at least one existing result and one planned pricing result fit the same
mathematical interface.
