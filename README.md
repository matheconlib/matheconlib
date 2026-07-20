# auctionlib

A Lean 4 formalization of fundamental theorems in auction theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Mathematical Reference

The auction-theory development is guided by an evolving overview provided by Scott Kominers, [*Auction Theory -- introduction and sketch of potential formalization objectives*](https://www.overleaf.com/project/698329a7c6b8506c1361f68b). The overview includes both completed and prospective objectives; this README describes the material currently implemented in Lean.

## Architecture

The library has three main layers, separating the rules of a mechanism from its probabilistic environment and the resulting interim optimization problem:

```
Mechanism n      — allocation x + payment t over agent report vectors
Auction Ω n      — mechanism + type environment (θ, distributions) on (Ω, ℙ)
BidderProblem    — one bidder's interim view (winProb, cost, strategy)
```

**`Auction → BidderProblem`**: `Auction.toBidderProblem` constructs the interim problem faced by bidder `i` when opponents use a strategy `σ`. For the direct mechanism (`σ = id`), BIC on the auction supplies `HasTypeDeviationIC` on the bidder problem, which in turn unlocks the envelope theorem, Myerson's lemma, and payment equivalence.

`BidderProblem` is the current name for the layer called `ReducedForm` in earlier versions of the library.

## Formalized Results

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
| [`BidderProblem/Basic.lean`](Auctionlib/BidderProblem/Basic.lean) | `BidderProblem`, `payoff`, `q`, `U`, and `IsRegular` |
| [`BidderProblem/EnvelopeIC.lean`](Auctionlib/BidderProblem/EnvelopeIC.lean) | `HasEnvelopeIC`, Lipschitz utility, monotone allocation, a.e. differentiability, the integral representation, and monotonicity of the strategy |
| [`BidderProblem/TypeDeviationIC.lean`](Auctionlib/BidderProblem/TypeDeviationIC.lean) | `HasTypeDeviationIC`, payment identity and uniqueness, `allPayBid`, `netPaymentIdentity`, and Myerson sufficiency |
| [`BidderProblem/UniversalIC.lean`](Auctionlib/BidderProblem/UniversalIC.lean) | `HasUniversalIC` over a feasible bid set and its bridge to `HasTypeDeviationIC` |

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
lake exe mk_all --lib Auctionlib --git   # regenerate import file
lake build                                # build the project
```

## Coverage and Roadmap

The mathematical overview is intentionally broader than the current library. Current coverage includes:

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
