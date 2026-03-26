# auctionlib

A Lean 4 formalization of fundamental theorems in auction theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formalized Results

### General Mechanism Framework

[`Mechanism`](Auctionlib/Mechanism/Basic.lean) captures any single-item auction with quasi-linear interim payoff $\pi(v, b) = v \cdot \text{winProb}(b) - \text{cost}(b)$. Different auction formats are special cases:

| Auction | $\text{winProb}(\text{bid})$ | $\text{cost}(\text{bid})$ |
|---------|-----------------|------------------|
| All-purchase | $G(\text{bid})$ | $C(\text{bid})$ |
| First-price | $G(\text{bid})$ | $\text{bid} \cdot G(\text{bid})$ |
| All-pay | $G(\text{bid})$ | $\text{bid}$ |
| Second-price | $G(\text{bid})$ | $\mathbb{E}[\text{payment} \mid \text{bid}]$ |

Three levels of incentive compatibility form a typeclass chain:

$$\texttt{HasUniversalIC} \Rightarrow \texttt{HasTypeDeviationIC} \Rightarrow \texttt{HasEnvelopeIC}$$

| File | Contents |
|------|----------|
| [`Mechanism/Basic.lean`](Auctionlib/Mechanism/Basic.lean) | `Mechanism` structure, `payoff`, `q`, `U` |
| [`Mechanism/EnvelopeIC.lean`](Auctionlib/Mechanism/EnvelopeIC.lean) | `HasEnvelopeIC` + envelope theorem (`lipschitz`, `q_monotoneOn`, `aeDifferentiable`, `integral_rep`) |
| [`Mechanism/TypeDeviationIC.lean`](Auctionlib/Mechanism/TypeDeviationIC.lean) | `HasTypeDeviationIC` + Myerson results (`payment_identity`, `payment_unique`) |
| [`Mechanism/UniversalIC.lean`](Auctionlib/Mechanism/UniversalIC.lean) | `HasUniversalIC` (strongest IC) |

### Envelope Theorem (Section 5.1)

The main auction setup is [`EnvelopeSetup`](Auctionlib/Envelope/Theorem.lean), encoding an $n$-bidder independent private values (IPV) auction with allocation rule, payment rule, and interim utility. The key economic properties are:

- [`IncentiveCompatible`](Auctionlib/Envelope/Theorem.lean) (Bayesian IC): truthful reporting maximizes interim utility
- [`ExPostIR`](Auctionlib/Envelope/Theorem.lean), [`InterimIR`](Auctionlib/Envelope/Theorem.lean), [`ExAnteIR`](Auctionlib/Envelope/Theorem.lean): three levels of individual rationality

The core mathematical analysis lives in [`EnvelopeSetUpMathsCore`](Auctionlib/Envelope/Mathematics.lean):

| Result | Statement |
|--------|-----------|
| [`lipschitz`](Auctionlib/Envelope/Mathematics.lean) | $U$ is 1-Lipschitz on $[a, b]$ |
| [`q_monotoneOn`](Auctionlib/Envelope/Mathematics.lean) | $q$ is monotone on $[a, b]$ |
| [`aeDifferentiable`](Auctionlib/Envelope/Mathematics.lean) | $U' = q$ a.e. on $[a, b]$ |
| [`integral_rep`](Auctionlib/Envelope/Mathematics.lean) | $U(s) = U(a) + \int_a^s q(\psi)\, d\psi$ |

These are assembled into [`envelope_theorem`](Auctionlib/Envelope/Theorem.lean): BIC implies all of the above in the auction setting.

### Myerson's Lemma (Section 5.2)

Built on [`MyersonSetUpMathsCore`](Auctionlib/Envelope/Mathematics.lean) (necessity) and [`MyersonSufficiencySetup`](Auctionlib/Envelope/Mathematics.lean) (sufficiency):

| Result | Statement |
|--------|-----------|
| [`myerson_necessity`](Auctionlib/Envelope/Myerson.lean) | DSIC $\Rightarrow$ monotone allocation + payment identity |
| [`myerson_payment_unique`](Auctionlib/Envelope/Myerson.lean) | Payment is uniquely determined by allocation (up to a constant) |
| [`myerson_sufficiency`](Auctionlib/Envelope/Myerson.lean) | Monotone allocation $\Rightarrow$ canonical integral payment achieves DSIC |

### Payment Equivalence (General)

[`EnvelopeSetup.payment_formula`](Auctionlib/Envelope/Theorem.lean) and [`EnvelopeSetup.payment_equivalence`](Auctionlib/Envelope/Theorem.lean) are proved without any efficiency, symmetry, or distributional assumptions:

| Result | Statement |
|--------|-----------|
| [`payment_formula`](Auctionlib/Envelope/Theorem.lean) | Under IC: $p(s) = s \cdot q(s) - U(\underline\theta) - \int_{\underline\theta}^s q(\psi)\, d\psi$ |
| [`payment_equivalence`](Auctionlib/Envelope/Theorem.lean) | Same $q$, same $\underline\theta$, same $U(\underline\theta)$ $\Rightarrow$ same $p$ |

### Revenue Equivalence Theorem (Section 5.3)

[`RevenueEquivalenceSetup`](Auctionlib/RevenueEquivalence/Theorem.lean) extends the envelope setup with mutual independence, identical distributions, and atomless types. Efficiency is a separate predicate ([`Efficient`](Auctionlib/RevenueEquivalence/Theorem.lean)), required only where genuinely needed.

| Result | Statement |
|--------|-----------|
| [`q_eq_pow`](Auctionlib/RevenueEquivalence/Theorem.lean) | $q(s) = F(s)^{n-1}$ under efficient allocation |
| [`payment_formula`](Auctionlib/RevenueEquivalence/Theorem.lean) | $p(s) = s \cdot F(s)^{n-1} - \int F(\psi)^{n-1}\, d\psi$ under efficient allocation + IC + IR |
| [`total_revenue`](Auctionlib/RevenueEquivalence/Theorem.lean) | Expected revenue $= \mathbb{E}[S_2]$ under efficient allocation + IC + IR |
| [`revenue_equivalence`](Auctionlib/RevenueEquivalence/Theorem.lean) | Any two IC, IR mechanisms with the same $q$ yield the same total expected revenue (no efficiency needed) |

### All-Purchase Auction (Chapter 6)

[`AllPurchaseCore`](Auctionlib/AllPurchase/Definitions.lean) captures the pure analytic content: winning probability `G`, net expenditure `C`, equilibrium strategy `β`, and the IC inequality. It coerces to `EnvelopeSetUpMathsCore`, making the envelope theorem directly applicable. [`AllPurchaseSetup`](Auctionlib/AllPurchase/Definitions.lean) extends `RevenueEquivalenceSetup` with a posted price and scarcity function.

| Result | Statement |
|--------|-----------|
| [`q_monotoneOn`](Auctionlib/AllPurchase/Monotonicity.lean) | $q = G \circ \beta$ is nondecreasing on $[a, b]$ |
| [`weakMonotonicity`](Auctionlib/AllPurchase/Monotonicity.lean) | Lemma 6.1: $\beta$ is weakly increasing under strict $G$ |
| [`lipschitz`](Auctionlib/AllPurchase/Envelope.lean) | $U$ is 1-Lipschitz on $[a, b]$ |
| [`aeDifferentiable`](Auctionlib/AllPurchase/Envelope.lean) | $U'(v) = q(v)$ a.e. |
| [`integral_rep`](Auctionlib/AllPurchase/Envelope.lean) | Lemma 6.3: $U(v) = U(a) + \int_a^v q(\psi)\, d\psi$ |
| [`netPaymentIdentity`](Auctionlib/AllPurchase/NetPayment.lean) | Proposition 6.4: $C(\beta(v)) = b^{AP}(v) - U(a)$ |

| [`strictMonotonicity`](Auctionlib/AllPurchase/StrictMonotonicity.lean) | Lemma 6.2: $\beta$ is strictly increasing on $[0, \bar{v}]$ |
| [`no_ties`](Auctionlib/AllPurchase/StrictMonotonicity.lean) | Distinct types have distinct bids in the interior |

Lemma 6.2 is proved in a self-contained setup ([`StrictMonoSetup`](Auctionlib/AllPurchase/StrictMonotonicity.lean)) importing only Mathlib, via contradiction using strict monotonicity of $F^{n-1}$ and continuity of $C$.

#### Planned: Baseline Demand & Explicit Solutions (Chapter 6)

The following results from the reference document are not yet formalized:

| Result | Statement |
|--------|-----------|
| Corollary (`cor:regimes`) | Boundary regime ($\beta(0)=0 \Rightarrow \mathcal{U}(0)=0$) vs interior regime ($\beta(0)>0$) |
| Proposition (`prop:constant`) | Constant scarcity equilibrium: $\beta(v) = b^{AP}(v)/(p - u_0)$ |
| Proposition (`prop:boundary`) | Boundary regime equilibrium via fixed-point in $K$ |
| Proposition (`prop:interior`) | Interior regime equilibrium: $\beta(v) = A/(2\alpha) + \sqrt{b^{AP}(v)/\alpha}$ |
| Proposition (`prop:uniform`) | Closed-form solutions under uniform distribution |

#### Planned: Economic Analysis (Chapter 6)

| Result | Statement |
|--------|-----------|
| Proposition (`prop:revenue`) | Revenue decomposition: $\mathbb{E}[pB] = n\mathbb{E}[b^{AP}(V)] - n\mathcal{U}(0) + \mathbb{E}[B\phi(B)]$ |
| Corollary (`cor:revenue_comparison`) | Revenue comparison to standalone mechanisms |
| Proposition (`prop:optimal_price`) | Optimal price in interior regime: $p^* = (\bar\phi + c + 2\sqrt\alpha M)/2$ |
| Proposition (`prop:welfare`) | Welfare decomposition: $W^* - W^C = \mathcal{L}_{\text{Cournot}} + \mathcal{L}_{\text{Contest}}$ |

### Order Statistics

[`OrderStatisticsSetup`](Auctionlib/Statistics/OrderStatistics.lean) formalizes $n$ i.i.d. real-valued random variables with a common density.

| Result | Statement |
|--------|-----------|
| [`cdf_val`](Auctionlib/Statistics/OrderStatistics.lean) | CDF of the $k$-th order statistic |
| [`pdf_val`](Auctionlib/Statistics/OrderStatistics.lean) | Density of the $k$-th order statistic |
| [`expected_val`](Auctionlib/Statistics/OrderStatistics.lean) | Expected value of the $k$-th order statistic |
| [`expected_second_highest`](Auctionlib/Statistics/OrderStatistics.lean) | Key identity for the Revenue Equivalence Theorem |

### Auxiliary Lemmas

[AbsolutelyContinuous.lean](Auctionlib/ForMathlib/AbsolutelyContinuous.lean) contains results that may be upstreamed to Mathlib:

- [`AbsolutelyContinuousOnInterval.pow`](Auctionlib/ForMathlib/AbsolutelyContinuous.lean): AC function raised to a power is AC
- [`absolutelyContinuousOnInterval_cdf`](Auctionlib/ForMathlib/AbsolutelyContinuous.lean): CDF of an AC measure is AC

## Building

```bash
lake exe mk_all --lib Auctionlib --git   # regenerate import file
lake build                                # build the project
```

## Roadmap


- [x] General Mechanism framework with IC hierarchy
- [ ] Game-theoretic concepts (Section 3)
- [x] Envelope Theorem (Section 5.1)
- [x] Myerson's Lemma (Section 5.2)
- [x] Revenue Equivalence Theorem (Section 5.3)
- [x] All-Purchase Auction — equilibrium characterization (Chapter 6)
- [ ] All-Purchase Auction — baseline demand & explicit solutions (Chapter 6)
- [ ] All-Purchase Auction — economic analysis (Chapter 6)
