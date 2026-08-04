# auctionlib

A Lean 4 formalization of fundamental theorems in auction theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Mathematical Reference

The auction-theory development is guided by an evolving overview provided by Scott Kominers, [*Auction Theory -- introduction and sketch of potential formalization objectives*](https://www.overleaf.com/project/698329a7c6b8506c1361f68b). The overview includes both completed and prospective objectives; this README describes the material currently implemented in Lean.

The extension from auctions to posted pricing and other single-parameter
problems is described in
[*Pricing Foundations: Mathematical Model and Architecture*](docs/PricingArchitecture.md).

## Architecture

The library has three main layers, separating the rules of a mechanism from its probabilistic environment and the resulting interim optimization problem:

```
Mechanism n      — allocation x + payment t over agent report vectors
Auction Ω n      — mechanism + type environment (θ, distributions) on (Ω, ℙ)
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

### Mechanism (`Mechanism/`)

[`Mechanism n`](Auctionlib/Mechanism/Basic.lean) defines allocation and payment rules as functions of the full report vector. Reports specialize to bids in the auction applications below.

| File | Contents |
|------|----------|
| [`Mechanism/Basic.lean`](Auctionlib/Mechanism/Basic.lean) | `Mechanism`, `HasValidAllocation`, and `IsEfficient` |
| [`Mechanism/AllPurchase.lean`](Auctionlib/Mechanism/AllPurchase.lean) | `Mechanism.IsAllPurchase`: efficient allocation together with a posted price, scarcity function, and payment identity `t_eq` |

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

[`Auction Ω n`](Auctionlib/Auction/Basic.lean) combines a `Mechanism` with the probabilistic environment.

| File | Contents |
|------|----------|
| [`Auction/Basic.lean`](Auctionlib/Auction/Basic.lean) | `Auction`, interim quantities `q`/`p`/`U` and `q_strat`/`p_strat`, IR notions, `BIC`, `toBidderProblem`, `payment_formula`, and `payment_equivalence` |
| [`Auction/Typeclasses.lean`](Auctionlib/Auction/Typeclasses.lean) | Composable assumptions on independent, identical, bounded, dense, and atomless types; `IsSymmetricIPV`; common type bounds and CDF |
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

The continuous conditional-expectation result and later applications such as the winner's curse and Linkage Principle are not yet formalized.

### Game Theory (`GameTheory/`)

| File | Contents |
|------|----------|
| [`GameTheory/Basic.lean`](Auctionlib/GameTheory/Basic.lean) | Normal-form games, payoff structures, dominant strategies, pure/strict/strong Nash equilibria, mixed games, and expected payoff |
| [`GameTheory/NashExistence.lean`](Auctionlib/GameTheory/NashExistence.lean) | Pure Nash existence for compact convex action spaces with quasiconcave payoffs, mixed Nash existence for compact metrizable action spaces, and finite-game mixed Nash existence |

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
| Pure and mixed Nash existence theorems | [`GameTheory/NashExistence.lean`](Auctionlib/GameTheory/NashExistence.lean) |

### Auxiliary

| File | Contents |
|------|----------|
| [`Statistics/OrderStatistics.lean`](Auctionlib/Statistics/OrderStatistics.lean) | CDF/PDF of order statistics, `expected_second_highest` |
| [`ForMathlib/AbsolutelyContinuous.lean`](Auctionlib/ForMathlib/AbsolutelyContinuous.lean) | AC function raised to a power, CDF of AC measure |
| [`ForMathlib/Kakutani.lean`](Auctionlib/ForMathlib/Kakutani.lean) | Kakutani--Glicksberg--Fan fixed-point theorem used by the Nash-existence development |
| [`ForMathlib/Schauder.lean`](Auctionlib/ForMathlib/Schauder.lean) | Schauder fixed-point theorem |

## Building

```bash
lake exe mk_all --lib Auctionlib --git       # regenerate library imports
lake exe mk_all --lib AuctionlibTest --git   # regenerate test imports
lake build                                    # build library and tests
```

## Coverage and Roadmap

The mathematical overview is intentionally broader than the current library. Current coverage includes:

- [x] Action-parametric single-parameter foundations and a deterministic fixed-price buyer problem
- [x] General `Mechanism` + `Auction` + `BidderProblem` framework
- [x] Envelope theorem, Myerson's lemma, and revenue equivalence
- [x] All-purchase equilibrium characterization, explicit solutions, revenue analysis, optimal pricing, and welfare decomposition
- [x] Normal-form game foundations and pure/mixed Nash existence
- [x] Affiliation definitions, log-supermodularity, and finite monotone conditional expectations

Further work includes:

- [ ] Continuous affiliation results and later applications, including the winner's curse and Linkage Principle
- [ ] Remaining game-theoretic concepts and their integration with the auction layer
- [ ] Extensive-form and obviously strategy-proof mechanisms
- [ ] Exploratory multi-unit and simultaneous ascending auction models
