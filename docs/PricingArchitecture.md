# Pricing Foundations: Mathematical Model and Compatibility Plan

## Status of this document

This is a permanent, versioned architecture document. It records the
mathematical model, terminology, compatibility promises, and reasons behind
the design. These parts should remain useful after the planned Lean
definitions have been implemented.

Some sections are necessarily provisional while implementation is in
progress. In particular, proposed Lean snippets, future-tense descriptions,
and postponed decisions should be updated as later commits settle them. Once
a declaration has been implemented, this document should describe and link to
the actual public interface rather than preserve stale pseudocode.

The core `SingleParameterProblem` structure and its elementary derived
quantities are implemented in
[`Auctionlib/SingleParameter/Basic.lean`](../Auctionlib/SingleParameter/Basic.lean).
The incentive-compatibility and participation predicates are implemented in
[`Auctionlib/SingleParameter/IC.lean`](../Auctionlib/SingleParameter/IC.lean).
The analytic envelope results are implemented in
[`Auctionlib/SingleParameter/EnvelopeIC.lean`](../Auctionlib/SingleParameter/EnvelopeIC.lean),
and the payment identity, uniqueness, and sufficiency results are implemented
in
[`Auctionlib/SingleParameter/Payment.lean`](../Auctionlib/SingleParameter/Payment.lean).
The compatibility bridge from `BidderProblem` is implemented in the existing
[`Auctionlib/BidderProblem`](../Auctionlib/BidderProblem) modules.
The deterministic posted-price example is implemented in
[`Auctionlib/SingleParameter/PostedPrice.lean`](../Auctionlib/SingleParameter/PostedPrice.lean).
End-to-end compile-time checks for both the new and legacy APIs are in
[`Auctionlib/SingleParameter/Regression.lean`](../Auctionlib/SingleParameter/Regression.lean).

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

Under envelope incentive compatibility, the induced allocation `q` is
nondecreasing and equilibrium utility is Lipschitz on the type interval. Its
derivative equals `q` almost everywhere, and the envelope theorem gives

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

The formal results are divided by their mathematical role:

- [`SingleParameter/EnvelopeIC.lean`](../Auctionlib/SingleParameter/EnvelopeIC.lean)
  proves `lipschitz`, `q_monotoneOn`, `aeDifferentiable`, `integral_rep`,
  `U_nonneg`, and the resulting individual-rationality condition.
- [`SingleParameter/Payment.lean`](../Auctionlib/SingleParameter/Payment.lean)
  proves `payment_identity`, `payment_unique`, and
  `typeDeviationIC_of_monotone_q`.

The payment-uniqueness theorem may compare problems with different action
types. This allows, for example, a direct-report mechanism and a posted-price
choice problem to share a payment conclusion when they induce the same
allocation and lowest-type utility.

## 4. Lean interface

The structure, derived definitions, incentive-compatibility classes,
participation predicates, and analytic results in this section are part of the
Lean library.

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

### 4.3 Envelope incentive compatibility

```lean
class HasEnvelopeIC
    {Action : Type u} (P : SingleParameterProblem Action) : Prop where
  envelopeIC :
    ∀ v ∈ P.typeInterval, ∀ v' ∈ P.typeInterval,
      (v - v') * P.q v' ≤ P.U v - P.U v'
```

This is the weakest IC condition in the hierarchy. It is the assumption used
by the analytic envelope and payment-necessity results.

### 4.4 Type-deviation incentive compatibility

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

### 4.5 Universal incentive compatibility

Universal incentive compatibility uses a feasible set

```lean
S : Set Action
```

instead of the `Set ℝ` used by the existing `BidderProblem` API:

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

### 4.6 The implication chain

The library provides typeclass instances for

```text
HasUniversalIC → HasTypeDeviationIC → HasEnvelopeIC
```

Consequently, a theorem that asks Lean for `HasEnvelopeIC P` can also be used
when the available assumption is one of the two stronger IC conditions.

### 4.7 Participation

Participation compares the utility from the strategy with an outside option.
The outside option is allowed to depend on the type:

```lean
def SatisfiesParticipation (outsideOption : ℝ → ℝ) : Prop :=
  ∀ v ∈ P.typeInterval, outsideOption v ≤ P.U v
```

The usual individual-rationality condition uses outside-option utility zero:

```lean
def IsIndividuallyRational : Prop :=
  P.SatisfiesParticipation (fun _ => 0)
```

The separate predicate

```lean
def HasZeroLowestTypeUtility : Prop :=
  P.U P.lowestType = 0
```

says that the lowest type's participation constraint binds at zero. This is
stronger than merely requiring the lowest type to receive nonnegative utility.

### 4.8 Envelope and payment theorem API

The main analytic declarations are:

```lean
theorem q_monotoneOn [HasEnvelopeIC P] :
    MonotoneOn P.q P.typeInterval

theorem integral_rep [HasEnvelopeIC P]
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.U v =
      P.U P.lowestType + ∫ w in P.lowestType..v, P.q w

theorem payment_identity [HasEnvelopeIC P]
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.payment (P.strategy v) =
      v * P.q v - P.U P.lowestType -
        ∫ w in P.lowestType..v, P.q w
```

The converse theorem, `typeDeviationIC_of_monotone_q`, constructs a
`HasTypeDeviationIC P` instance from monotonicity of `q` and the displayed
payment formula. Together, the necessity and sufficiency directions provide a
general one-dimensional version of Myerson's payment characterization.

### 4.9 Fixed posted-price problem

The first concrete use of the general action type is a buyer facing a fixed
posted price. The buyer's type still ranges over a real interval, so the type
model is continuous. The action type is the finite inductive type

```lean
inductive PurchaseDecision where
  | buy
  | doNotBuy
```

For a price `p`, buying has allocation `1`, payment `p`, and payoff `v - p`.
Not buying has allocation, payment, and payoff all equal to `0`. The strategy
is therefore

```lean
if p ≤ v then PurchaseDecision.buy
else PurchaseDecision.doNotBuy
```

The definition `postedPriceProblem lowestType highestType p` packages these
objects as a `SingleParameterProblem PurchaseDecision`. The library proves:

- the displayed payoff, allocation, and utility formulas;
- universal IC over the two purchase decisions;
- monotonicity of the induced allocation using the general IC chain;
- individual rationality because not buying is available;
- zero utility for the lowest type whenever `lowestType ≤ p`.

This example remains deterministic. A distribution of buyer values, expected
seller revenue, virtual values, and optimization over `p` belong to later pull
requests.

## 5. Relationship to `BidderProblem`

The current `BidderProblem` has not been renamed or replaced.

The conversion `BidderProblem.toSingleParameterProblem` is implemented in
[`BidderProblem/Basic.lean`](../Auctionlib/BidderProblem/Basic.lean). Its fields
have the following correspondence:

| General field | Existing `BidderProblem` field |
|---|---|
| `lowestType` | `lowestType` |
| `highestType` | `highestType` |
| `allocation` | `winProb` |
| `allocation_range` | `winProb_range` |
| `payment` | `cost` |
| `strategy` | `strategy` |

The conversion has the shape

```lean
def BidderProblem.toSingleParameterProblem
    (B : BidderProblem) :
    SingleParameterProblem ℝ
```

Simplification lemmas state that, after conversion:

- the general payoff equals `BidderProblem.payoff`;
- the general induced allocation equals `BidderProblem.q`;
- the general utility equals `BidderProblem.U`;
- the type interval and each underlying field are unchanged.

Each existing bidder IC assumption automatically supplies its general
counterpart:

```text
BidderProblem.HasEnvelopeIC
  → SingleParameterProblem.HasEnvelopeIC

BidderProblem.HasTypeDeviationIC
  → SingleParameterProblem.HasTypeDeviationIC

BidderProblem.HasUniversalIC
  → SingleParameterProblem.HasUniversalIC
```

Explicit theorems provide the converse directions without registering them as
instances. Keeping only one direction automatic avoids cycles in typeclass
search.

Existing auction code will continue to construct and use `BidderProblem`.
There is no requirement that existing applications immediately migrate to the
new structure. Its public envelope and payment theorem statements are
unchanged, but their proofs now apply the general single-parameter theorems.

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

## 9. First foundation milestone

The first pricing-foundations milestone establishes the deterministic layer
needed by later distributional and seller-optimization results. Its completion
criteria are:

- [x] types are real-valued while actions may have an arbitrary Lean type;
- [x] quasilinear payoff, induced allocation, utility, and participation are
  defined without probabilistic assumptions;
- [x] universal IC, type-deviation IC, and envelope IC form a reusable
  implication chain;
- [x] monotonicity, the envelope representation, payment necessity,
  uniqueness, and sufficiency are action-parametric;
- [x] `BidderProblem` converts losslessly to the general structure;
- [x] existing bidder theorem statements remain available and reuse the
  general proofs;
- [x] a fixed posted price demonstrates the API with a finite, non-real action
  type and a continuous real type interval;
- [x] regression examples compile through both the new pricing path and the
  legacy auction path;
- [x] the complete existing library builds successfully.

The next milestone may therefore add type distributions, expected seller
revenue, and virtual values without putting those assumptions into
`SingleParameterProblem`.
