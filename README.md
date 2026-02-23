# auctionlib

A Lean 4 formalization of fundamental theorems in auction theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formalized Results

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


- [ ] Game-theoretic concepts (Section 3)
- [x] Envelope Theorem (Section 5.1)
- [x] Myerson's Lemma (Section 5.2)
- [x] Revenue Equivalence Theorem (Section 5.3)
