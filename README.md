# auctionlib

A Lean 4 formalization of fundamental theorems in auction theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formalized Results

### Envelope Theorem (Section 5.1)

The main auction setup is [`EnvelopeSetup`](Auctionlib/Envelope/Theorem.lean#L56), encoding an $n$-bidder independent private values (IPV) auction with allocation rule, payment rule, and interim utility. The key economic properties are:

- [`IncentiveCompatible`](Auctionlib/Envelope/Theorem.lean#L116) (Bayesian IC): truthful reporting maximizes interim utility
- [`ExPostIR`](Auctionlib/Envelope/Theorem.lean#L121), [`InterimIR`](Auctionlib/Envelope/Theorem.lean#L127), [`ExAnteIR`](Auctionlib/Envelope/Theorem.lean#L132): three levels of individual rationality

The core mathematical analysis lives in [`EnvelopeSetUpMathsCore`](Auctionlib/Envelope/Mathematics.lean#L52):

| Result | Statement |
|--------|-----------|
| [`lipschitz`](Auctionlib/Envelope/Mathematics.lean#L72) | $U$ is 1-Lipschitz on $[a, b]$ |
| [`q_monotoneOn`](Auctionlib/Envelope/Mathematics.lean#L87) | $q$ is monotone on $[a, b]$ |
| [`aeDifferentiable`](Auctionlib/Envelope/Mathematics.lean#L128) | $U' = q$ a.e. on $[a, b]$ |
| [`integral_rep`](Auctionlib/Envelope/Mathematics.lean#L143) | $U(s) = U(a) + \int_a^s q(\psi)\, d\psi$ |

These are assembled into [`envelope_theorem`](Auctionlib/Envelope/Theorem.lean#L174): BIC implies all of the above in the auction setting.

### Myerson's Lemma (Section 5.2)

Built on [`MyersonSetUpMathsCore`](Auctionlib/Envelope/Mathematics.lean#L168) (necessity) and [`MyersonSufficiencySetup`](Auctionlib/Envelope/Mathematics.lean#L227) (sufficiency):

| Result | Statement |
|--------|-----------|
| [`myerson_necessity`](Auctionlib/Envelope/Myerson.lean#L95) | DSIC $\Rightarrow$ monotone allocation + payment identity |
| [`myerson_payment_unique`](Auctionlib/Envelope/Myerson.lean#L107) | Payment is uniquely determined by allocation (up to a constant) |
| [`myerson_sufficiency`](Auctionlib/Envelope/Myerson.lean#L121) | Monotone allocation $\Rightarrow$ canonical integral payment achieves DSIC |

### Revenue Equivalence Theorem (Section 5.3)

[`RevenueEquivalenceSetup`](Auctionlib/RevenueEquivalence/Theorem.lean#L56) extends the envelope setup with mutual independence, identical distributions, efficient allocation, and atomless types.

| Result | Statement |
|--------|-----------|
| [`q_eq_pow`](Auctionlib/RevenueEquivalence/Theorem.lean#L150) | $q(s) = F(s)^{n-1}$ for efficient auctions |
| [`payment_formula`](Auctionlib/RevenueEquivalence/Theorem.lean#L179) | $p(s) = s \cdot F(s)^{n-1} - \int F(\psi)^{n-1}\, d\psi$ under IC + IR |
| [`total_revenue`](Auctionlib/RevenueEquivalence/Theorem.lean#L188) | Expected revenue $= \mathbb{E}[S_2]$ (expected second-highest order statistic) |
| [`payment_equivalence`](Auctionlib/RevenueEquivalence/Theorem.lean#L271) | Any two efficient IC IR mechanisms yield the same per-type payment |
| [`revenue_equivalence`](Auctionlib/RevenueEquivalence/Theorem.lean#L294) | Any two efficient IC IR mechanisms yield the same total expected revenue |

### Order Statistics

[`OrderStatisticsSetup`](Auctionlib/Statistics/OrderStatistics.lean#L148) formalizes $n$ i.i.d. real-valued random variables with a common density.

| Result | Statement |
|--------|-----------|
| [`cdf_val`](Auctionlib/Statistics/OrderStatistics.lean#L374) | CDF of the $k$-th order statistic |
| [`pdf_val`](Auctionlib/Statistics/OrderStatistics.lean#L504) | Density of the $k$-th order statistic |
| [`expected_val`](Auctionlib/Statistics/OrderStatistics.lean#L583) | Expected value of the $k$-th order statistic |
| [`expected_second_highest`](Auctionlib/Statistics/OrderStatistics.lean#L636) | Key identity for the Revenue Equivalence Theorem |

### Auxiliary Lemmas

[AbsolutelyContinuous.lean](Auctionlib/ForMathlib/AbsolutelyContinuous.lean) contains results that may be upstreamed to Mathlib:

- [`AbsolutelyContinuousOnInterval.pow`](Auctionlib/ForMathlib/AbsolutelyContinuous.lean#L29): AC function raised to a power is AC
- [`absolutelyContinuousOnInterval_cdf`](Auctionlib/ForMathlib/AbsolutelyContinuous.lean#L53): CDF of an AC measure is AC

## Building

```bash
lake exe mk_all --lib Auctionlib --git   # regenerate import file
lake build                                # build the project
```

## Roadmap

- [x] Envelope Theorem (Section 5.1)
- [x] Myerson's Lemma (Section 5.2)
- [x] Revenue Equivalence Theorem (Section 5.3)
- [ ] Game-theoretic concepts (Section 3)
