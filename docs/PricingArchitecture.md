# Pricing Foundations: Mathematical Model and Architecture

## Status of this document

This is a permanent, versioned architecture document. It records the
mathematical scope, terminology, compatibility promises, and design boundaries
of the pricing foundations. The Lean source is authoritative for exact
declaration syntax; this document explains how the pieces fit together and
links to the public interface rather than duplicating it.
Unqualified Lean names below are relative to `MathEconLib`; the
[namespace guide](NamespaceMigration.md) records the public names.

The core `SingleParameterProblem` structure and its elementary derived
quantities are implemented in
[`MathEconLib/SingleParameter/Basic.lean`](../MathEconLib/SingleParameter/Basic.lean).
The incentive-compatibility and individual-rationality predicates are
implemented in
[`MathEconLib/SingleParameter/IC.lean`](../MathEconLib/SingleParameter/IC.lean).
The analytic envelope results are implemented in
[`MathEconLib/SingleParameter/EnvelopeIC.lean`](../MathEconLib/SingleParameter/EnvelopeIC.lean),
and the payment identity, uniqueness, and sufficiency results are implemented
in
[`MathEconLib/SingleParameter/Payment.lean`](../MathEconLib/SingleParameter/Payment.lean).
The compatibility bridge from `BidderProblem` is implemented in the existing
[`MathEconLib/BidderProblem`](../MathEconLib/BidderProblem) modules.
The deterministic posted-price example is implemented in
[`MathEconLib/SingleParameter/PostedPrice.lean`](../MathEconLib/SingleParameter/PostedPrice.lean).
The measure-first representation of real-valued type distributions and its
optional bounded-support predicate are implemented in
[`MathEconLib/ValueDistribution/Basic.lean`](../MathEconLib/ValueDistribution/Basic.lean),
while posted-price demand and its relationship to the CDF are implemented in
[`MathEconLib/ValueDistribution/Demand.lean`](../MathEconLib/ValueDistribution/Demand.lean).
Generic expected allocation, expected payment, seller profit, and their
reduced-form contracts are implemented in
[`MathEconLib/ValueDistribution/SingleParameter.lean`](../MathEconLib/ValueDistribution/SingleParameter.lean).
Their specialization to distributional posted pricing is implemented in
[`MathEconLib/ValueDistribution/PostedPrice.lean`](../MathEconLib/ValueDistribution/PostedPrice.lean).
Optional density and virtual-surplus vocabulary are implemented in
[`MathEconLib/ValueDistribution/Density.lean`](../MathEconLib/ValueDistribution/Density.lean)
and
[`MathEconLib/ValueDistribution/VirtualValue.lean`](../MathEconLib/ValueDistribution/VirtualValue.lean).
The density-free tail identity and its applications to expected payment and
seller profit are implemented in
[`MathEconLib/ValueDistribution/TailIntegral.lean`](../MathEconLib/ValueDistribution/TailIntegral.lean),
[`MathEconLib/ValueDistribution/ExpectedPayment.lean`](../MathEconLib/ValueDistribution/ExpectedPayment.lean),
and
[`MathEconLib/ValueDistribution/SellerProfit.lean`](../MathEconLib/ValueDistribution/SellerProfit.lean).
The posted-price cutoff representation and sufficient sign conditions for
global and boundary optimality among posted prices are implemented in
[`MathEconLib/ValueDistribution/PostedPriceOptimality.lean`](../MathEconLib/ValueDistribution/PostedPriceOptimality.lean).
Pointwise differentiation of posted-price seller profit and necessary
first-order conditions at an interior local optimum are implemented in
[`MathEconLib/ValueDistribution/PostedPriceFirstOrder.lean`](../MathEconLib/ValueDistribution/PostedPriceFirstOrder.lean).
Reusable interval-uniform distribution facts are in
[`MathEconLib/ValueDistribution/Uniform.lean`](../MathEconLib/ValueDistribution/Uniform.lean),
while the uniform profit and virtual-surplus formulas, constrained optimum,
interior first-order condition, and comparative statics are in
[`MathEconLib/ValueDistribution/UniformPricing.lean`](../MathEconLib/ValueDistribution/UniformPricing.lean).
The additive bridge from auction type random variables to bidder value
distributions is implemented in
[`MathEconLib/Auction/ValueDistribution.lean`](../MathEconLib/Auction/ValueDistribution.lean).
End-to-end compile-time checks for both the new and legacy APIs are in
[`MathEconLibTest/SingleParameter/Compatibility.lean`](../MathEconLibTest/SingleParameter/Compatibility.lean)
and
[`MathEconLibTest/ValueDistribution/Compatibility.lean`](../MathEconLibTest/ValueDistribution/Compatibility.lean),
with representative continuous, finite-support, and unbounded distributions in
[`MathEconLibTest/ValueDistribution/Examples.lean`](../MathEconLibTest/ValueDistribution/Examples.lean)
and end-to-end seller-objective checks in
[`MathEconLibTest/Pricing/Compatibility.lean`](../MathEconLibTest/Pricing/Compatibility.lean).

The first application is optimal posted pricing for one buyer. The
foundations are intended to be reusable for auctions, screening, contracts,
and bargaining problems with a one-dimensional private type whenever utility
has the affine form described below. They do not represent arbitrary
nonseparable type-action utility.

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

The foundational restriction is that utility is affine in the private type:

\[
u(v,a)=v\,x(a)-t(a).
\]

The action type may be rich, but all dependence on `v` passes through the one
scalar coefficient `x(a)`. This affine structure—not the choice of action
type—is what supports the envelope and payment results in this development.

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
- a normalized quantity choice;
- a complete response plan in a bargaining procedure.

Using an arbitrary action type generalizes the interface beyond the current
`BidderProblem`, where every action is a real-valued bid. It does not enlarge
the affine-in-type class of preferences.

### 1.2 Allocation and payment

Each action `a` determines:

- an allocation `x(a)` in the interval `[0, 1]`;
- a payment `t(a)` in `ℝ`.

The allocation can be interpreted as a probability of receiving one
indivisible object. It can also encode a physical quantity after normalization
when the type's value contribution is exactly `v * x(a)` and the resulting
coefficient lies in `[0, 1]`. Unnormalized quantities, multiple value
coefficients, and multiple goods require a different or extended abstraction.
A payment is positive when the agent pays the mechanism; a negative payment is
a transfer to the agent.

### 1.3 Strategy, payoff, allocation, and utility

A strategy maps each type to an action:

\[
\sigma : \mathbb R \to \mathit{Action}.
\]

The strategy is deliberately a field of `SingleParameterProblem`. Therefore,
the IC predicates below apply to the bundled allocation rule, payment rule,
and strategy—not to the allocation and payment rules in isolation. The
operation `P.withStrategy newStrategy` is the explicit way to hold the other
fields fixed while changing the strategy; IC for the resulting problem must be
proved separately.

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

A primitive such as

\[
V(v,a)-t(a)
\]

with genuinely nonseparable `V` is outside the current model. It fits only if
its action-dependent part can be represented in the displayed affine form
(with any type-independent term absorbed into the payment).

## 2. Incentive compatibility

The existing library has three levels of incentive compatibility. The general
single-parameter model retains the same hierarchy.

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

Universal incentive compatibility requires the strategy action `σ(v)` to be
feasible for every type in the interval and to give at least as much utility
as every feasible action `a`:

\[
\pi(v,a) \le \pi(v,\sigma(v)).
\]

This condition implies type-deviation incentive compatibility because
`σ(v')` is one of the feasible actions.

The implication chain is

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

### 3.1 Canonical reduced form

For a problem `P`, the operation `P.reduce` constructs a direct problem whose
actions are real-valued type reports. Reporting `w` produces the allocation
`P.q w` and the payment generated by the original action `P.strategy w`; the
reduced strategy is the identity.

Consequently, `P.reduce` has the same induced allocation `q`, on-strategy
utility `U`, and type-report deviation payoffs as `P`. Envelope IC and
type-deviation IC therefore pass in both directions. This makes explicit that
the envelope representation and payment identity depend on the reduced
functions `q` and `U`, not on how richly the original action was described.

Reduction need not retain an original action outside the image of
`P.strategy`. Universal IC, which compares the chosen action with arbitrary
feasible actions, therefore has no unqualified equivalence with universal IC
after reduction.

The formal results are divided by their mathematical role:

- [`SingleParameter/EnvelopeIC.lean`](../MathEconLib/SingleParameter/EnvelopeIC.lean)
  proves `lipschitz`, `q_monotoneOn`, `aeDifferentiable`, `integral_rep`,
  and `U_nonneg`.
- [`SingleParameter/Payment.lean`](../MathEconLib/SingleParameter/Payment.lean)
  proves `payment_identity`, `payment_unique`, and
  `typeDeviationIC_of_monotone_q`.

The payment-uniqueness theorem may compare problems with different action
types. This allows, for example, a direct-report mechanism and a posted-price
choice problem to share a payment conclusion when they have the same type
interval, induced allocation, and lowest-type utility.

## 4. Public Lean API map

The Lean source files are authoritative for declaration syntax. This section
is a map of the stable interface and the role of each module, not a second copy
of their definitions.

| Source | Principal public API | Architectural role |
|---|---|---|
| [`SingleParameter/Basic.lean`](../MathEconLib/SingleParameter/Basic.lean) | `SingleParameterProblem`, `typeInterval`, `payoff`, `q`, `U`, `withStrategy`, `reduce` | Deterministic affine-in-type model, explicit strategy replacement, and canonical direct reduction |
| [`SingleParameter/IC.lean`](../MathEconLib/SingleParameter/IC.lean) | `HasEnvelopeIC`, `HasTypeDeviationIC`, `HasUniversalIC`, `IsIndividuallyRational`, `HasZeroLowestTypeUtility` | IC hierarchy, participation normalization, and envelope/type-deviation bridges to `P.reduce` |
| [`SingleParameter/EnvelopeIC.lean`](../MathEconLib/SingleParameter/EnvelopeIC.lean) | `lipschitz`, `q_monotoneOn`, `aeDifferentiable`, `integral_rep`, `U_nonneg` | Analytic consequences of envelope IC |
| [`SingleParameter/Payment.lean`](../MathEconLib/SingleParameter/Payment.lean) | `payment_identity`, `payment_unique`, `typeDeviationIC_of_monotone_q` | Payment necessity, uniqueness, and sufficiency |
| [`SingleParameter/PostedPrice.lean`](../MathEconLib/SingleParameter/PostedPrice.lean) | `PurchaseDecision`, `postedPriceProblem`, its payoff, demand, IC, and participation results | Finite-action example with a continuous real type interval |
| [`ValueDistribution/Basic.lean`](../MathEconLib/ValueDistribution/Basic.lean) | `ValueDistribution`, `ofRandomVariable`, `IsSupportedOnInterval` | Measure-first representation, pushforwards of random variables, and optional bounded support |
| [`ValueDistribution/Demand.lean`](../MathEconLib/ValueDistribution/Demand.lean) | `probAtLeast` and its monotonicity, lower-tail, CDF, and atom identities | Posted-price demand with tie-breaking that remains correct for atomic and mixed distributions |
| [`ValueDistribution/SingleParameter.lean`](../MathEconLib/ValueDistribution/SingleParameter.lean) | `expectedAllocation`, `expectedPayment`, `sellerProfit`, and their `_reduce` contracts | Ordinary-integral expectations and seller accounting for a separately supplied single-parameter problem |
| [`ValueDistribution/PostedPrice.lean`](../MathEconLib/ValueDistribution/PostedPrice.lean) | Posted-price expected allocation, payment, profit, comparison formulas, and acquisition-cost invariance | Distributional specialization of the deterministic posted-price problem and generic seller objective, without density or support assumptions |
| [`ValueDistribution/Density.lean`](../MathEconLib/ValueDistribution/Density.lean) | `realDensity` and integration against canonical or chosen density representatives | Optional absolutely continuous representation built from mathlib's Radon--Nikodym derivative, not a second density typeclass |
| [`ValueDistribution/VirtualValue.lean`](../MathEconLib/ValueDistribution/VirtualValue.lean) | `virtualSurplusWeight`, `virtualValue`, and their density and CDF forms | Density-weighted virtual surplus as the primary object, with virtual value available when division is justified |
| [`ValueDistribution/TailIntegral.lean`](../MathEconLib/ValueDistribution/TailIntegral.lean) | Tail-probability integral identity | Measure-theoretic bridge from envelope utility to expected payment, valid before choosing a density |
| [`ValueDistribution/ExpectedPayment.lean`](../MathEconLib/ValueDistribution/ExpectedPayment.lean) | Expected-payment identities in tail-probability, canonical-density, chosen-density, and CDF forms | Revenue-equivalence consequences expressed first without a density and then specialized under absolute continuity |
| [`ValueDistribution/SellerProfit.lean`](../MathEconLib/ValueDistribution/SellerProfit.lean) | Expected-allocation density representation and seller-profit virtual-surplus decompositions | Rewrites the existing scalar seller objective without adding costs, continuation values, or densities to foundational structures |
| [`ValueDistribution/PostedPriceOptimality.lean`](../MathEconLib/ValueDistribution/PostedPriceOptimality.lean) | Cutoff-integral seller profit and `IsMaxOn` sign and boundary theorems | Gives sufficient global optimality conditions among posted prices without claiming the full Riley--Zeckhauser result over arbitrary selling rules |
| [`ValueDistribution/PostedPriceFirstOrder.lean`](../MathEconLib/ValueDistribution/PostedPriceFirstOrder.lean) | Pointwise profit derivative, division-free interior first-order condition, and nonzero-density virtual-value corollaries | Gives necessary conditions at an interior local optimum without global smoothness or a global density representative |
| [`ValueDistribution/Uniform.lean`](../MathEconLib/ValueDistribution/Uniform.lean) | `uniformInterval`, support, atomlessness, density, demand, and CDF results | Reuses Mathlib's conditioned Lebesgue measure independently of the pricing application |
| [`ValueDistribution/UniformPricing.lean`](../MathEconLib/ValueDistribution/UniformPricing.lean) | Uniform profit and virtual-surplus formulas, clamped candidate, `IsMaxOn`, uniqueness, interior virtual-value condition, and comparative statics | Specializes the shared global-optimality and first-order theorems; uniqueness is restricted to prices in the value interval |
| [`Auction/ValueDistribution.lean`](../MathEconLib/Auction/ValueDistribution.lean) | `valueDistribution`, its pushforward and support contracts, equality under identical types, and `commonCDF` agreement | Additive reuse of auction type laws as ordinary value distributions without changing `Auction` |
| [`BidderProblem/Basic.lean`](../MathEconLib/BidderProblem/Basic.lean) and IC modules | `toSingleParameterProblem` and the forward and reverse IC bridges | Compatibility with the existing bidder-facing API |
| [`MathEconLibTest/SingleParameter/Compatibility.lean`](../MathEconLibTest/SingleParameter/Compatibility.lean) | Compile-time examples | Downstream checks for both the generic and legacy APIs |
| [`MathEconLibTest/ValueDistribution/Compatibility.lean`](../MathEconLibTest/ValueDistribution/Compatibility.lean) | Compile-time API pins | Young-layer contract checks, including atomic posted-price tie-breaking and the auction pushforward bridge |
| [`MathEconLibTest/ValueDistribution/Examples.lean`](../MathEconLibTest/ValueDistribution/Examples.lean) | Representative distribution examples | Bounded continuous, finite-support, and unbounded laws using mathlib probability measures |
| [`MathEconLibTest/Pricing/Compatibility.lean`](../MathEconLibTest/Pricing/Compatibility.lean) | End-to-end pricing examples | Certain sale and non-sale, acquisition-cost ranking invariance, and reduced-form seller profit |

The implication instances follow
`HasUniversalIC → HasTypeDeviationIC → HasEnvelopeIC`. A problem's IC instances
are keyed to the problem together with its bundled strategy. Forward instances
make envelope and type-deviation results available on `P.reduce`; named reverse
theorems recover the corresponding assumptions on `P` without creating
typeclass-search cycles. No general universal-IC equivalence is registered,
because the original off-strategy action space is not recoverable from the
reduced problem.

The fixed posted-price problem remains deterministic. `ValueDistribution` is
a separate layer over mathlib probability measures, and
`ValueDistribution/SingleParameter.lean` is the one-way bridge that takes a
distribution and a deterministic problem as separate arguments.
`ValueDistribution/PostedPrice.lean` specializes that bridge to derive demand,
payment, seller-profit, and price-comparison formulas without adding support or
density assumptions. The expected-payment layer first uses tail probabilities,
so its primary identity also applies to atomic and mixed distributions. Under
envelope IC, support on the type interval, and absolute continuity, later
modules express the resulting payment and profit in density-weighted
virtual-surplus form. The posted-price optimality module then uses a
single-crossing sign condition on the division-free net weight to prove global
and boundary optimality among feasible posted prices. These are sufficient
conditions. Separately, under atomlessness, the first-order module requires
differentiability of the CDF only at the candidate price and proves that an
interior local optimum has zero division-free net virtual surplus. When the
pointwise density is nonzero, virtual value therefore equals the continuation
value, and it equals zero for the last buyer. These are necessary conditions:
they do not establish optimality from a zero derivative. Nor do they claim a
zero derivative at a boundary optimum, where the existing one-sided sign
results are the relevant tool. Optimization over general selling rules remains
a subsequent layer.

The uniform family exercises both pricing theorems. For `a < b`, its virtual-surplus
weight is `(2 * value - b) / (b - a)` on `[a, b]`, and the resulting net-weight signs
establish optimality of `max a (min b ((b + r) / 2))` throughout the interior
and both boundary regimes. The first-order theorem gives virtual value `r`
when the optimum is interior. A private quadratic profit-gap identity proves
uniqueness within `[a, b]`; prices above `b` all yield no sale and are outside
that uniqueness claim. The existing unit-interval example applies these
public results through the `MathEconLib.ValueDistribution` umbrella import.

## 5. Relationship to `BidderProblem`

The current `BidderProblem` has not been renamed or replaced.

The conversion `BidderProblem.toSingleParameterProblem` is implemented in
[`BidderProblem/Basic.lean`](../MathEconLib/BidderProblem/Basic.lean). Its fields
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

Named compatibility lemmas state that, after conversion:

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

A type distribution is represented separately from
`SingleParameterProblem`. The foundational `ValueDistribution` object is a
transparent abbreviation for mathlib's `ProbabilityMeasure ℝ`; it does not
duplicate measures, integration, CDFs, or atomlessness. Distributions obtained
from random variables use the ordinary pushforward construction.

Bounded support is an optional predicate rather than part of the distribution
itself. This lets the same interface describe bounded, unbounded, continuous,
finite-support, and mixed distributions. A theorem using a bounded
single-parameter type interval can request support on that interval, while
results that do not need bounds remain available for arbitrary real-valued
probability distributions.

At a posted price `p`, the deterministic strategy buys when `p ≤ v`.
Distributional demand is consequently the probability of the closed upper
tail:

\[
D(p)=\Pr[V\ge p].
\]

For a potentially atomic distribution this satisfies

\[
D(p)=1-F(p)+\Pr[V=p].
\]

The familiar formula `D(p) = 1 - F(p)` is therefore used only when there is no
atom at `p`.

Expected allocation and expected payment integrate the on-strategy functions
`P.q` and `P.payment ∘ P.strategy` against a separately supplied distribution.
The generic seller objective then combines those expectations with the
seller's continuation value and the cost of approaching the buyer. These are
functions of the distribution and problem, not fields added to either object.
In this first objective the continuation value is constant across buyer types,
and the acquisition cost is an unconditional additive cost.

For posted prices, changing that cost preserves optimality over any fixed
feasible price set: it cancels from every pairwise profit difference. This
general result requires no density or bounded-support assumption. It does not
imply that the decision to approach the buyer is independent of the cost.

Under envelope IC, when the distribution is absolutely continuous and
supported on the problem's type interval, the seller objective has the
decomposition

\[
\Pi
= r-c-U(\underline v)
+\int_{\underline v}^{\overline v}
q(v)\bigl(w_{D,f}(v)-r f(v)\bigr)\,dv.
\]

Here `r` is the seller's continuation value, `c` is the unconditional cost of
approaching the buyer, and `U(underline v)` is the lowest type's utility. The
remaining integral is allocation-weighted virtual surplus net of the
continuation value forgone upon allocation. The acquisition cost is outside
the integral because it is paid independently of the allocation decision. The
weight `w_{D,f}(v) = v f(v) - Pr[V >= v]` is primary: it avoids dividing by a
density that may vanish. A chosen density is a representative that agrees
almost everywhere on the type interval with the distribution's canonical
`realDensity`.

The dependency direction is deliberately one-way:

```text
SingleParameter.Basic ──┐
                       ├── ValueDistribution.SingleParameter
ValueDistribution.Basic ┘
```

Thus the deterministic single-parameter theory does not import probability
theory. Measurability, integrability, support, and incentive-compatibility
assumptions are requested only by theorems that use them. In particular,
mathlib's integral is total, so results interpreting an integral as an economic
expectation must establish the required measurability and integrability.

The auction bridge follows the same one-way discipline. It turns each type
random variable into its pushforward `ValueDistribution` without adding a field
to `Auction`. `HasBoundedTypes` supplies optional interval support, while
`HasIdenticalTypes` identifies bidder distributions and recovers the existing
`commonCDF`. The old CDF and auction typeclasses remain available unchanged.

The following economic data and assumptions still belong to later application
or optimization layers, not in the single-parameter problem or the primitive
distribution:

- any additional seller cost beyond the scalar objective's continuation value
  and unconditional acquisition cost;
- regularity conditions supporting local or global optimization.

Absolute continuity and a chosen density are theorem assumptions rather than
fields of `ValueDistribution`. Auction-facing density results must obtain their
density assumption from the existing `Auction.HasDensity.θ_hasPDF` field rather
than introduce a parallel density abstraction in the `ValueDistribution`
namespace.

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
- non-affine or genuinely nonseparable type-action utility;
- risk-averse buyers;
- extensive-form syntax for bargaining histories;
- regularity assumptions and ironing for virtual values;
- optimization over general selling rules, including the Riley--Zeckhauser
  comparison between posted prices and haggling.

These topics should not complicate the first reusable layer unless a concrete
application shows that they are necessary.

## 8. Review checklist for later commits

Before a later commit changes Lean code, it should answer:

1. Does the new declaration belong to the deterministic single-parameter
   layer, the distribution layer, or an economic application?
2. Does the result assume that utility is affine in type? If not, does it need
   a genuinely new abstraction?
3. Does the result depend only on `q` and `U`, or on the full action space?
4. Can the result be stated without auction-specific terminology?
5. Does an existing declaration already express the same idea?
6. If existing proofs are refactored, are their public statements unchanged?
7. Does the full existing library still build?

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
- [x] compatibility examples compile through both the new pricing path and the
  legacy auction path;
- [x] the complete existing library builds successfully.

The current analytic and optimization milestones add optional density
representations, density-free expected-payment identities, virtual-surplus
seller-profit formulas, sufficient sign conditions for optimality among
posted prices, necessary virtual-value conditions at an interior local optimum,
and uniform-price optimality and comparative statics. They do so without
putting probabilistic assumptions into `SingleParameterProblem` or changing
`Auction`. Later layers will add the full Riley--Zeckhauser selling-rule result
and comparative statics beyond the uniform family.
