# auctionlib

A Lean 4 formalization of fundamental theorems in auction theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Getting Started

New to Lean 4, or to this library?
[*Lean 4 and `auctionlib` — A Beginner's Manual*](docs/BeginnersManual.md) goes
from installing the toolchain to reading
[`BidderProblem/Basic.lean`](Auctionlib/BidderProblem/Basic.lean) line by line,
with runnable exercises throughout. It assumes no Lean and no auction theory.

## Mathematical Reference

The auction-theory development is guided by an evolving overview provided by Scott Kominers, [*Auction Theory -- introduction and sketch of potential formalization objectives*](https://www.overleaf.com/project/698329a7c6b8506c1361f68b). The overview includes both completed and prospective objectives; this README describes the material currently implemented in Lean.

The extension from auctions to posted pricing and other single-parameter
problems is described in
[*Pricing Foundations: Mathematical Model and Architecture*](docs/PricingArchitecture.md).

## Architecture

The library has three main layers, separating the rules of a mechanism from its probabilistic environment and the resulting interim optimization problem:

```
Mechanism I A O  — outcome rule + signed transfers over dependent action profiles
Auction Ω n      — real-bid rules + measurable allocation + type environment on (Ω, ℙ)
BidderProblem    — one bidder's interim view (winProb, cost, strategy)
```

The reusable deterministic core
[`SingleParameterProblem Action`](Auctionlib/SingleParameter/Basic.lean)
models affine-in-type, quasilinear utility

$$u(v,a)=v\,x(a)-t(a).$$

The action may be a bid, report, contract choice, or bargaining plan, but the
type must enter utility through the scalar allocation coefficient `x(a)` in
`[0, 1]`. Thus richer actions generalize the modeling interface, not this
affine theory: a genuinely nonseparable primitive such as `V(v,a) - t(a)` is
outside the current abstraction. Physical quantity choices fit only after
their value contribution has been normalized into the scalar allocation.

The structure deliberately bundles a strategy with the allocation and payment
rules, so its IC predicates concern a mechanism-and-strategy pair.
`withStrategy` changes that strategy explicitly. The canonical `reduce`
operation turns any such problem into a direct real-report problem with the
same induced allocation `q` and utility `U`. The envelope and payment results
depend on these reduced quantities; reduction may forget original actions
outside the strategy's image. The layer contains no probability distribution
or seller objective.

The existing `BidderProblem` API remains unchanged.
`BidderProblem.toSingleParameterProblem` supplies a lossless compatibility
bridge, so existing auction results can reuse the general theorems.

**`Auction → BidderProblem`**: `Auction.toBidderProblem` constructs the interim problem faced by bidder `i` when opponents use a strategy `σ`. For the direct mechanism (`σ = id`), BIC on the auction supplies `HasTypeDeviationIC` on the bidder problem, which in turn unlocks the envelope theorem, Myerson's lemma, and payment equivalence.

`BidderProblem` is the current name for the layer called `ReducedForm` in earlier versions of the library.

## Formalized Results

### Single-Parameter Problems (`SingleParameter/`)

[`SingleParameterProblem Action`](Auctionlib/SingleParameter/Basic.lean)
describes a deterministic quasilinear choice problem with a real-valued type
and an arbitrary action type, subject to the affine-in-type payoff restriction
described above.

| File | Contents |
|------|----------|
| [`SingleParameter/Basic.lean`](Auctionlib/SingleParameter/Basic.lean) | Type interval, allocation, payment, strategy, payoff, induced allocation `q`, utility `U`, strategy replacement, and canonical reduction |
| [`SingleParameter/IC.lean`](Auctionlib/SingleParameter/IC.lean) | Envelope, type-deviation, and universal IC; their implication chain; reduced-form bridges; individual rationality and lowest-type normalization |
| [`SingleParameter/EnvelopeIC.lean`](Auctionlib/SingleParameter/EnvelopeIC.lean) | Monotone allocation, Lipschitz and a.e. differentiable utility, the envelope integral representation, and utility nonnegativity |
| [`SingleParameter/Payment.lean`](Auctionlib/SingleParameter/Payment.lean) | Payment identity, payment uniqueness across action types, and the sufficiency of monotonicity plus the payment identity for type-deviation IC |
| [`SingleParameter/PostedPrice.lean`](Auctionlib/SingleParameter/PostedPrice.lean) | A fixed posted price with real-valued types, the two actions `buy` and `doNotBuy`, universal IC, monotone demand, and individual rationality |

Compile-time checks that the generic posted-price path and the existing
`BidderProblem` path expose the intended APIs live in the separate
[`AuctionlibTest/SingleParameter/Compatibility.lean`](AuctionlibTest/SingleParameter/Compatibility.lean)
test library.

### Value Distributions and Pricing (`ValueDistribution/`)

`ValueDistribution` is a transparent abbreviation for mathlib's
`ProbabilityMeasure ℝ`. The layer adds economic vocabulary and connects a
separately supplied value distribution to the deterministic
`SingleParameterProblem` API; it does not introduce a second probability or
integration theory.

| File | Contents |
|------|----------|
| [`ValueDistribution/Basic.lean`](Auctionlib/ValueDistribution/Basic.lean) | Real-valued probability distributions, random-variable pushforwards, and optional bounded support |
| [`ValueDistribution/Demand.lean`](Auctionlib/ValueDistribution/Demand.lean) | Closed-upper-tail posted-price demand, monotonicity, and atom-sensitive CDF identities |
| [`ValueDistribution/Density.lean`](Auctionlib/ValueDistribution/Density.lean) | Canonical real density and change of measure under absolute continuity |
| [`ValueDistribution/VirtualValue.lean`](Auctionlib/ValueDistribution/VirtualValue.lean) | Division-free virtual-surplus weight and secondary virtual value |
| [`ValueDistribution/TailIntegral.lean`](Auctionlib/ValueDistribution/TailIntegral.lean) | Density-free tail-integral identity, including atomic distributions |
| [`ValueDistribution/SingleParameter.lean`](Auctionlib/ValueDistribution/SingleParameter.lean) | Expected allocation, expected payment, seller profit, and reduced-form preservation |
| [`ValueDistribution/ExpectedPayment.lean`](Auctionlib/ValueDistribution/ExpectedPayment.lean) | Density-free expected-payment representation and density and CDF corollaries |
| [`ValueDistribution/SellerProfit.lean`](Auctionlib/ValueDistribution/SellerProfit.lean) | Expected-allocation density formula and seller-profit virtual-surplus representations |
| [`ValueDistribution/PostedPrice.lean`](Auctionlib/ValueDistribution/PostedPrice.lean) | Posted-price demand, expected payment, seller-profit, revenue, and price-comparison formulas |
| [`ValueDistribution/PostedPriceOptimality.lean`](Auctionlib/ValueDistribution/PostedPriceOptimality.lean) | Cutoff-integral seller profit and sufficient global and boundary optimality conditions among posted prices |
| [`ValueDistribution/PostedPriceFirstOrder.lean`](Auctionlib/ValueDistribution/PostedPriceFirstOrder.lean) | Pointwise seller-profit differentiation, the division-free necessary condition at an interior local optimum, and nonzero-density virtual-value corollaries |

Compile-time pins, representative distributions, and end-to-end pricing checks
live respectively in
[`AuctionlibTest/ValueDistribution/Compatibility.lean`](AuctionlibTest/ValueDistribution/Compatibility.lean),
[`AuctionlibTest/ValueDistribution/Examples.lean`](AuctionlibTest/ValueDistribution/Examples.lean),
and
[`AuctionlibTest/Pricing/Compatibility.lean`](AuctionlibTest/Pricing/Compatibility.lean).

### Mechanism (`Mechanism/`)

[`Auctionlib.Mechanism I A O`](Auctionlib/Mechanism/Core/Mechanism.lean) assigns an outcome and signed transfers to a dependent action profile. Positive transfers are money received by agents; payments are negative transfers. Import [`Auctionlib.Mechanism`](Auctionlib/Mechanism.lean) for the family API.

| File | Contents |
|------|----------|
| [`Mechanism/Core/Profile.lean`](Auctionlib/Mechanism/Core/Profile.lean) | Dependent action and type profiles |
| [`Mechanism/Core/Mechanism.lean`](Auctionlib/Mechanism/Core/Mechanism.lean) | Generic carrier, direct mechanisms, payments, and revenue |
| [`Mechanism/Core/Comap.lean`](Auctionlib/Mechanism/Core/Comap.lean) | Induced mechanisms and identity/composition laws |
| [`Mechanism/Core/Environment.lean`](Auctionlib/Mechanism/Core/Environment.lean) | Quasilinear environments, private values, utility, and welfare |
| [`Mechanism/Core/SolutionConcepts.lean`](Auctionlib/Mechanism/Core/SolutionConcepts.lean) | DSIC, ex-post IR, welfare efficiency, budget balance, and no deficit |
| [`Mechanism/Auctions/Allocation.lean`](Auctionlib/Mechanism/Auctions/Allocation.lean) | `IsUnitIntervalAllocation` coordinate bounds and `UsesStrictHighestBidAllocation` |
| [`Mechanism/Auctions/AllPurchase/Spec.lean`](Auctionlib/Mechanism/Auctions/AllPurchase/Spec.lean) | Explicit `AllPurchaseSpec` price/scarcity data and the `IsAllPurchase` existence predicate |

`IsUnitIntervalAllocation` bounds each coordinate in `[0, 1]`; aggregate feasibility depends on the outcome space and allocation rule. Welfare efficiency compares outcomes using a valuation environment. The strict-highest-bid rule instead describes allocations from bids, awarding nothing on ties.

Checked examples in [`AuctionlibTest/Mechanism/Core.lean`](AuctionlibTest/Mechanism/Core.lean) use the umbrella import, including a truthful posted-price mechanism, concrete all-purchase payments, and a mechanism with infinitely many agents.

### Bidder Problem (`BidderProblem/`)

[`BidderProblem`](Auctionlib/BidderProblem/Basic.lean) captures a bidder's interim view with quasi-linear payoff $\pi(v, b) = v \cdot \text{winProb}(b) - \text{cost}(b)$.

Three IC levels form a typeclass chain:

$$\texttt{HasUniversalIC} \Rightarrow \texttt{HasTypeDeviationIC} \Rightarrow \texttt{HasEnvelopeIC}$$

| File | Contents |
|------|----------|
| [`BidderProblem/Basic.lean`](Auctionlib/BidderProblem/Basic.lean) | `BidderProblem`, `payoff`, `q`, `U`, `IsRegular`, and the lossless conversion to `SingleParameterProblem ℝ` |
| [`BidderProblem/EnvelopeIC.lean`](Auctionlib/BidderProblem/EnvelopeIC.lean) | `HasEnvelopeIC`, its general compatibility bridge, and the original bidder envelope API backed by the general theorems |
| [`BidderProblem/TypeDeviationIC.lean`](Auctionlib/BidderProblem/TypeDeviationIC.lean) | `HasTypeDeviationIC`, its general compatibility bridge, payment identity and uniqueness, `allPayBid`, `netPaymentIdentity`, and Myerson sufficiency |
| [`BidderProblem/UniversalIC.lean`](Auctionlib/BidderProblem/UniversalIC.lean) | `HasUniversalIC` over a feasible bid set and bridges to both the bidder and general IC hierarchies |

### Auction (`Auction/`)

[`Auction Ω n`](Auctionlib/Auction/Basic.lean) combines real-bid mechanism rules with measurable allocation coordinates and the probabilistic environment. The generic mechanism itself has no measurability requirement.

Interim quantities use Mathlib’s totalized Bochner integral, which equals zero when its integrand is not integrable. Arbitrary strategies need not be measurable. Measurable strategies together with `IsUnitIntervalAllocation` ensure allocation integrability, including truthful reporting; payment integrability requires separate hypotheses.

| File | Contents |
|------|----------|
| [`Auction/Basic.lean`](Auctionlib/Auction/Basic.lean) | `Auction`, interim quantities `q`/`p`/`U` and `q_strat`/`p_strat`, IR notions, `BIC`, `toBidderProblem`, `payment_formula`, and `payment_equivalence` |
| [`Auction/Typeclasses.lean`](Auctionlib/Auction/Typeclasses.lean) | Composable assumptions on independent, identical, bounded, dense, and atomless types; `IsSymmetricIPV`; common type bounds and CDF |
| [`Auction/ValueDistribution.lean`](Auctionlib/Auction/ValueDistribution.lean) | Additive pushforward bridge from each bidder's type random variable to a real-valued value distribution |
| [`Auction/IdenticalTypes.lean`](Auctionlib/Auction/IdenticalTypes.lean) | Expectation identities requiring identical type distributions |
| [`Auction/SymmetricIPV.lean`](Auctionlib/Auction/SymmetricIPV.lean) | `bidThreshold`, `q_eq_pow`, `q_strat_eq_cdf_pow`, and the bridge to order statistics |
| [`Auction/RevenueEquivalence.lean`](Auctionlib/Auction/RevenueEquivalence.lean) | `payment_formula_efficient`, `total_revenue` (= $\mathbb{E}[S_2]$), `revenue_equivalence` |
| [`Auction/StrictMonotonicity.lean`](Auctionlib/Auction/StrictMonotonicity.lean) | `HasPosDensity`, strict monotonicity of an equilibrium strategy, and `no_ties` |

### All-Purchase Auctions (`Auction/AllPurchase/`)

The all-purchase development specializes the general framework to auctions in which every bidder purchases editions while the highest bid receives the allocation.

| File | Contents |
|------|----------|
| [`Auction/AllPurchase/Basic.lean`](Auctionlib/Auction/AllPurchase/Basic.lean) | The distribution-based all-pay benchmark bid `Auction.allPayBid` |
| [`Auction/AllPurchase/LinearScarcity.lean`](Auctionlib/Auction/AllPurchase/LinearScarcity.lean) | `QuadraticCostProblem`, `LinearCostProblem`, `InteriorRegimeProblem`, `IsBoundaryRegime`, `LinearScarcityAuction`, and `toQuadraticCostProblem` |
| [`Auction/AllPurchase/ExplicitSolutions.lean`](Auctionlib/Auction/AllPurchase/ExplicitSolutions.lean) | Constant-scarcity, boundary-regime, and interior-regime equilibrium strategy formulas at bidder-problem and auction levels |
| [`Auction/AllPurchase/RevenueDecomposition.lean`](Auctionlib/Auction/AllPurchase/RevenueDecomposition.lean) | Seller-revenue decomposition and the bundled-versus-standalone revenue comparison |
| [`Auction/AllPurchase/OptimalPricing.lean`](Auctionlib/Auction/AllPurchase/OptimalPricing.lean) | Interior-regime profit maximization, uniqueness, and feasibility of the optimal price |
| [`Auction/AllPurchase/UniformDistribution.lean`](Auctionlib/Auction/AllPurchase/UniformDistribution.lean) | Closed form for the all-pay benchmark bid under a uniform type distribution |
| [`Auction/AllPurchase/WelfareDecomposition.lean`](Auctionlib/Auction/AllPurchase/WelfareDecomposition.lean) | First-best edition surplus, Cournot and contest losses, the welfare decomposition, and the variance penalty |

### Affiliation (`Auction/Affiliation/`)

| File | Contents |
|------|----------|
| [`Auction/Affiliation/Basic.lean`](Auctionlib/Auction/Affiliation/Basic.lean) | Affiliated densities, product factorization, signal/value environments, private values, and independent and affiliated signals |
| [`Auction/Affiliation/LogSupermodular.lean`](Auctionlib/Auction/Affiliation/LogSupermodular.lean) | Equivalence between affiliation and log-supermodularity for strictly positive densities |
| [`Auction/Affiliation/FiniteCondExp.lean`](Auctionlib/Auction/Affiliation/FiniteCondExp.lean) | Finite weighted conditional averages and a reusable affiliation comparison for lattice-ordered conditioning events |
| [`Auction/Affiliation/MonotoneCondExp.lean`](Auctionlib/Auction/Affiliation/MonotoneCondExp.lean) | Monotonicity of conditional expectations for affiliated distributions on finite sublattices |
| [`Auction/Affiliation/WinnersCurse.lean`](Auctionlib/Auction/Affiliation/WinnersCurse.lean) | The winner's-curse inequality for affiliated distributions on finite sublattices |

The continuous conditional-expectation and winner's-curse results, together with later applications such as the Linkage Principle, are not yet formalized.

### Game Theory (`GameTheory/`)

| File | Contents |
|------|----------|
| [`GameTheory/Equilibrium/Problem.lean`](Auctionlib/GameTheory/Equilibrium/Problem.lean) | Shared admissible-deviation equilibrium and forward/backward transport |
| [`GameTheory/Strategic/Basic.lean`](Auctionlib/GameTheory/Strategic/Basic.lean) | Payoff-based games, dominance, and pure/strict/strong Nash equilibria |
| [`GameTheory/Strategic/Outcome.lean`](Auctionlib/GameTheory/Strategic/Outcome.lean) | Outcome games, payoff structures, probability-measure mixing, and expected utility |
| [`GameTheory/Strategic/Mixed.lean`](Auctionlib/GameTheory/Strategic/Mixed.lean) | Finite-simplex mixed strategies and agreement with probability-measure mixing |
| [`GameTheory/Strategic/Existence.lean`](Auctionlib/GameTheory/Strategic/Existence.lean) | Pure Nash existence for quasiconcave payoffs on compact convex action spaces and mixed Nash existence |
| [`GameTheory/Strategic/Bayesian/Finite.lean`](Auctionlib/GameTheory/Strategic/Bayesian/Finite.lean) | Finite-type pure BNE, null-type conventions, and expanded-game Nash |
| [`GameTheory/Strategic/Bayesian/FiniteMeasurable.lean`](Auctionlib/GameTheory/Strategic/Bayesian/FiniteMeasurable.lean) | Finite and measurable equilibrium agreement |
| [`GameTheory/Strategic/Bayesian/Measurable/PureBNE.lean`](Auctionlib/GameTheory/Strategic/Bayesian/Measurable/PureBNE.lean) | Measurable whole-strategy deviations and integrable ex-ante BNE |
| [`GameTheory/Strategic/Bayesian/Measurable/InterimConverse.lean`](Auctionlib/GameTheory/Strategic/Bayesian/Measurable/InterimConverse.lean) | Explicit conditional beliefs and the guarded interim/ex-ante equivalence |

`StrategicGame I A V`, `EquilibriumProblem S I V`, and `PayoffStructure I O V` take an explicit
payoff type. Pure Nash requires every unilateral deviation's payoff to be at most the incumbent
payoff. With partially ordered payoffs, this is stronger than absence of strict improvement;
the two agree under a linear order. Finite expected payoffs use real modules, and integral payoffs
use complete real normed spaces. Pure quasiconcave existence allows linearly ordered payoff spaces
with a closed order relation. Mixed-equilibrium existence and the measurable interim equilibrium
implications (`isBNE_of_ae_interim` and the theorems in `InterimConverse`) remain specialized to real
payoffs.

`MixedStrategy`, `mixedExtension`, and `IsMixedNash` use probability measures. The finite
computational interface is in `GameTheory/Strategic/Mixed/Finite.lean`, with `FiniteMixedStrategy`,
`finiteExpectedPayoff`, `finiteMixedExtension`, and `IsFiniteMixedNash`. It needs no measurable
structure on finite actions and evaluates payoffs by finite sums. Finite priors and finite mixed
actions share `FinDist`, a probability-oriented alias of Mathlib's real simplex. Both mixed
representation bridges follow from `StrategicGame.isNash_iff_of_actionEquiv` and payoff agreement.
The raw `mixedExtension` uses the totalized Bochner integral. `IsMixedNash` requires integrable
incumbent payoffs and compares unilateral deviations with integrable deviator payoffs. When all
unilateral payoffs are integrable, it agrees with Nash equilibrium of the raw mixed extension;
finite discrete games and bounded measurable payoffs in second countable payoff spaces satisfy
this condition.

The Bayesian game carrier takes players, types, actions, and payoff values as explicit parameters.
Priors are supplied separately. Finite BNE constrains positive-probability types, and the finite
Bayesian equivalences hold for partially ordered real modules whose order respects addition and
nonnegative scaling. Measurable BNE includes incumbent integrability and, for real payoffs, has an
almost-everywhere interim characterization under the stated measurability and
conditional-integrability assumptions. Pointwise auction IC and induced mechanism games remain
separate integration work.

### Key Theorems

| Result | Location |
|--------|----------|
| Envelope theorem ($U$ Lipschitz, $U' = q$ a.e., integral representation) | [`BidderProblem/EnvelopeIC.lean`](Auctionlib/BidderProblem/EnvelopeIC.lean) |
| Myerson's lemma (monotone allocation and payment identity, with a sufficiency direction) | [`BidderProblem/TypeDeviationIC.lean`](Auctionlib/BidderProblem/TypeDeviationIC.lean) |
| General payment equivalence for BIC auctions with the same type interval, interim allocation, and base utility | [`Auction/Basic.lean`](Auctionlib/Auction/Basic.lean) |
| $q(i,s)=F(s)^{n-1}$ under efficient allocation in the symmetric IPV setting | [`Auction/SymmetricIPV.lean`](Auctionlib/Auction/SymmetricIPV.lean) |
| Revenue equivalence and total revenue $=\mathbb{E}[S_2]$ under the stated BIC, IR, efficiency, and symmetry assumptions | [`Auction/RevenueEquivalence.lean`](Auctionlib/Auction/RevenueEquivalence.lean) |
| Strict monotonicity of equilibrium strategies under positive-density and IC assumptions | [`Auction/StrictMonotonicity.lean`](Auctionlib/Auction/StrictMonotonicity.lean) |
| All-purchase revenue decomposition and bundled-versus-standalone revenue comparison | [`Auction/AllPurchase/RevenueDecomposition.lean`](Auctionlib/Auction/AllPurchase/RevenueDecomposition.lean) |
| Interior-regime optimal pricing | [`Auction/AllPurchase/OptimalPricing.lean`](Auctionlib/Auction/AllPurchase/OptimalPricing.lean) |
| All-purchase welfare decomposition | [`Auction/AllPurchase/WelfareDecomposition.lean`](Auctionlib/Auction/AllPurchase/WelfareDecomposition.lean) |
| Winner's-curse inequality for affiliated finite-support environments | [`Auction/Affiliation/WinnersCurse.lean`](Auctionlib/Auction/Affiliation/WinnersCurse.lean) |
| Pure and mixed Nash existence theorems | [`GameTheory/Strategic/Existence.lean`](Auctionlib/GameTheory/Strategic/Existence.lean) |

### Auxiliary

| File | Contents |
|------|----------|
| [`Statistics/OrderStatistics.lean`](Auctionlib/Statistics/OrderStatistics.lean) | CDF/PDF of order statistics, `expected_second_highest` |
| [`ForMathlib/AbsolutelyContinuous.lean`](Auctionlib/ForMathlib/AbsolutelyContinuous.lean) | AC function raised to a power, CDF of AC measure |
| [`ForMathlib/Kakutani.lean`](Auctionlib/ForMathlib/Kakutani.lean) | Kakutani--Glicksberg--Fan fixed-point theorem used by the Nash-existence development |
| [`ForMathlib/Schauder.lean`](Auctionlib/ForMathlib/Schauder.lean) | Schauder fixed-point theorem |

## Building

```bash
lake exe cache get                           # fetch prebuilt Mathlib oleans (do this first)
lake exe mk_all --lib Auctionlib --git       # regenerate library imports
lake exe mk_all --lib AuctionlibTest --git   # regenerate test imports
lake build                                    # build library, API pins, tests, and examples
lake build MathEconLibExamples                 # build the mathematical economics examples
```

`MathEconLibExamples/GameTheory/MatchingPennies.lean` constructs matching pennies, proves that
uniform randomization is its unique mixed Nash equilibrium, and rules out pure Nash equilibria.

Run `lake exe cache get` before the first build, and again after any change that
bumps the Mathlib revision or after `lake clean`; without it Lean compiles
Mathlib from source, which takes hours. [Part 0 of the Beginner's
Manual](docs/BeginnersManual.md#part-0--working-with-lean-on-your-mac) covers
the editor setup in full.

## Coverage and Roadmap

The mathematical overview is intentionally broader than the current library. Current coverage includes:

- [x] Action-parametric single-parameter foundations and a deterministic fixed-price buyer problem
- [x] Measure-first value distributions, seller-profit decompositions, posted-price sign
  conditions, and interior virtual-value first-order conditions
- [x] General `Mechanism` + `Auction` + `BidderProblem` framework
- [x] Envelope theorem, Myerson's lemma, and revenue equivalence
- [x] All-purchase equilibrium characterization, explicit solutions, revenue analysis, optimal pricing, and welfare decomposition
- [x] Normal-form game foundations and pure/mixed Nash existence
- [x] Affiliation definitions, log-supermodularity, finite monotone conditional expectations, and the finite winner's-curse inequality

Further work includes:

- [ ] Full Riley--Zeckhauser comparison between posted prices and general selling rules
- [ ] Posted-price comparative statics, beginning with uniform-distribution parameters
- [ ] Continuous affiliation results, including the continuous winner's-curse inequality, and later applications such as the Linkage Principle
- [ ] Remaining game-theoretic concepts and their integration with the auction layer
- [ ] Extensive-form and obviously strategy-proof mechanisms
- [ ] Exploratory multi-unit and simultaneous ascending auction models
