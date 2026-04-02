# auctionlib

A Lean 4 formalization of fundamental theorems in auction theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Architecture

Three-layer design following the standard auction theory reference:

```
Mechanism n              — rules: allocation x + payment t over bid vectors
Auction Ω n              — rules + environment (θ, distributions) on (Ω, ℙ)
ReducedForm              — per-bidder interim view (winProb, cost, strategy)
```

**`Auction → ReducedForm`**: BIC on the auction implies `HasTypeDeviationIC` on the reduced form, unlocking the full analytic toolkit (envelope theorem, Myerson, payment equivalence).

## Formalized Results

### Mechanism (`Mechanism/`)

[`Mechanism n`](Auctionlib/Mechanism/Basic.lean) defines the rules of an auction: allocation rule $x_i(b)$ and payment rule $t_i(b)$ as functions of the full bid vector $b = (b_1, \ldots, b_n)$.

| File | Contents |
|------|----------|
| [`Mechanism/Basic.lean`](Auctionlib/Mechanism/Basic.lean) | `Mechanism` structure, `HasValidAllocation`, `IsFeasible`, `IsEfficient` |
| [`Mechanism/AllPurchase.lean`](Auctionlib/Mechanism/AllPurchase.lean) | `Mechanism.IsAllPurchase` (posted price + scarcity function + `x_eq`/`t_eq`), `hasValidAllocation` |

### Reduced Form (`ReducedForm/`)

[`ReducedForm`](Auctionlib/ReducedForm/Basic.lean) captures the per-bidder interim view with quasi-linear payoff $\pi(v, b) = v \cdot \text{winProb}(b) - \text{cost}(b)$.

Three IC levels form a typeclass chain:

$$\texttt{HasUniversalIC} \Rightarrow \texttt{HasTypeDeviationIC} \Rightarrow \texttt{HasEnvelopeIC}$$

| File | Contents |
|------|----------|
| [`ReducedForm/Basic.lean`](Auctionlib/ReducedForm/Basic.lean) | `ReducedForm` structure, `payoff`, `q`, `U`, `IsRegular` |
| [`ReducedForm/EnvelopeIC.lean`](Auctionlib/ReducedForm/EnvelopeIC.lean) | `HasEnvelopeIC` + `lipschitz`, `q_monotoneOn`, `aeDifferentiable`, `integral_rep`, `strategy_monotoneOn`, `U_nonneg` |
| [`ReducedForm/TypeDeviationIC.lean`](Auctionlib/ReducedForm/TypeDeviationIC.lean) | `HasTypeDeviationIC` + `payment_identity`, `payment_unique`, `allPayBid`, `netPaymentIdentity`, Myerson sufficiency |
| [`ReducedForm/UniversalIC.lean`](Auctionlib/ReducedForm/UniversalIC.lean) | `HasUniversalIC` |

### Auction (`Auction/`)

[`Auction Ω n`](Auctionlib/Auction/Basic.lean) combines a `Mechanism` with the probabilistic environment.

| File | Contents |
|------|----------|
| [`Auction/Basic.lean`](Auctionlib/Auction/Basic.lean) | `Auction` structure, `q`, `p`, `U`, `q_strat`, `p_strat`, `BIC`, `ExPostIR`/`InterimIR`/`ExAnteIR`, `toReducedForm`, `hasTypeDeviationIC_of_bic`, `payment_formula`, `payment_equivalence` |
| [`Auction/SymmetricIPV.lean`](Auctionlib/Auction/SymmetricIPV.lean) | Composable typeclasses: `HasIndependentTypes`, `HasIdenticalTypes`, `HasBoundedTypes`, `HasDensity`, `HasAtomlessTypes`, `IsSymmetricIPV`. CDF via Mathlib's `ProbabilityTheory.cdf`. `q_eq_pow`, `commonCDF`, `toOrderStatisticsSetup` |
| [`Auction/RevenueEquivalence.lean`](Auctionlib/Auction/RevenueEquivalence.lean) | `payment_formula_efficient`, `total_revenue` (= $\mathbb{E}[S_2]$), `revenue_equivalence` |
| [`Auction/AllPurchase.lean`](Auctionlib/Auction/AllPurchase.lean) | `allPayBid` (re-exports `Mechanism.IsAllPurchase` via import) |
| [`Auction/AllPurchase/LinearScarcity.lean`](Auctionlib/Auction/AllPurchase/LinearScarcity.lean) | `HasQuadraticCost`, `HasLinearCost`, `IsBoundaryRegime`, `IsInteriorRegime` (extends `HasQuadraticCost`), `HasLinearScarcity`, `meanPurchase`, `K_linear`, `allPurchaseNetCost`, `toAllPurchaseReducedForm` (winProb = `q_strat`, cost derived from `t_eq`) |
| [`Auction/AllPurchase/ExplicitSolutions.lean`](Auctionlib/Auction/AllPurchase/ExplicitSolutions.lean) | Propositions 6.5--6.7: `constant_scarcity_strategy`, `boundary_regime_strategy`, `interior_regime_strategy` (ReducedForm + Auction level) |
| [`Auction/AllPurchase/Welfare.lean`](Auctionlib/Auction/AllPurchase/Welfare.lean) | `editionWelfare`, `firstBestQuantity`, `cournotQuantity`, `welfare_decomposition` |
| [`Auction/AllPurchase/Revenue.lean`](Auctionlib/Auction/AllPurchase/Revenue.lean) | `revenue_decomposition`, `optimalPrice`, `bundled_exceeds_editionsOnly` |
| [`Auction/StrictMonotonicity.lean`](Auctionlib/Auction/StrictMonotonicity.lean) | `HasPosDensity`, `HasOrderStatWinProb`, `strictMonotonicity` (Lemma 6.2), `no_ties` |

### Key Theorems

| Result | Location |
|--------|----------|
| Envelope theorem ($U$ Lipschitz, $U' = q$ a.e., integral representation) | `ReducedForm.EnvelopeIC` |
| Myerson's lemma (necessity: $q$ monotone + payment identity; sufficiency) | `ReducedForm.TypeDeviationIC` |
| Payment equivalence (general: same $q$ + BIC $\Rightarrow$ same $p$) | `Auction.Basic` |
| $q(i, s) = F(s)^{n-1}$ under efficient allocation | `Auction.SymmetricIPV` |
| Revenue equivalence (same $q$ + BIC + IR $\Rightarrow$ same revenue) | `Auction.RevenueEquivalence` |
| Total revenue $= \mathbb{E}[S_2]$ | `Auction.RevenueEquivalence` |
| Strict monotonicity of equilibrium strategy (Lemma 6.2) | `Auction.StrictMonotonicity` |

### Auxiliary

| File | Contents |
|------|----------|
| [`Statistics/OrderStatistics.lean`](Auctionlib/Statistics/OrderStatistics.lean) | CDF/PDF of order statistics, `expected_second_highest` |
| [`ForMathlib/AbsolutelyContinuous.lean`](Auctionlib/ForMathlib/AbsolutelyContinuous.lean) | AC function raised to a power, CDF of AC measure |

## Building

```bash
lake exe mk_all --lib Auctionlib --git   # regenerate import file
lake build                                # build the project
```

## Roadmap

- [x] General Mechanism + ReducedForm + Auction framework
- [x] Envelope Theorem (Section 5.1)
- [x] Myerson's Lemma (Section 5.2)
- [x] Revenue Equivalence Theorem (Section 5.3)
- [x] All-Purchase Auction — equilibrium characterization (Chapter 6)
- [x] All-Purchase Auction — baseline demand & explicit solutions (Chapter 6)
- [x] All-Purchase Auction — economic analysis (Chapter 6)
- [ ] Game-theoretic concepts (Section 3)
- [x] Delete legacy files (`Envelope/`, `AllPurchase/`, `RevenueEquivalence/`)
