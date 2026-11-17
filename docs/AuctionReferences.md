# Auction theory references and provenance

The primary textbook reference for standard auction results is **Vijay Krishna,
*Auction Theory*, 2nd edition, Academic Press, 2010**, ISBN 978-0-12-374507-1.
Page numbers below are the book's printed page numbers.

The source map distinguishes textbook results from the library's more general
formulations and additional analysis. Each linked Lean statement gives the precise
assumptions; a reference does not imply identical hypotheses or notation.

## Standard results

The Krishna references below were checked against chapters 1–4 of the second edition.

| Formalized material | Reference | Relationship to the Lean development |
| --- | --- | --- |
| [Symmetric independent private values](../MathEconLib/Auction/Typeclasses.lean) | Krishna, §2.1, pp. 11–12 | The textbook environment motivates the separate independence, identical-distribution, boundedness, density, and atomlessness assumptions. Lean results request the assumptions they use. |
| [Winning probability under strict-highest-bid allocation](../MathEconLib/Auction/SymmetricIPV.lean) | Krishna, §2.2, p. 13: `G = F^(N−1)` | The common-CDF formula corresponds to `q_eq_pow`. The bid-threshold treatment of weakly increasing strategies is a further formal development. |
| [Revenue equivalence](../MathEconLib/Auction/RevenueEquivalence.lean) | Krishna, §3.1, Proposition 3.1, p. 28 | The standard symmetric IPV result. The library also states equivalence directly through matching interim allocations and lowest-type utilities. |
| [Equilibrium payment formula](../MathEconLib/Auction/RevenueEquivalence.lean) | Krishna, §3.1, equation (3.2), p. 28 | Integration by parts gives the library's `v F(v)^(n−1) − ∫ F(t)^(n−1) dt` form in the zero-lowest-type-utility case. |
| [Expected revenue equals the expected second-highest value](../MathEconLib/Auction/RevenueEquivalence.lean) and [the supporting order-statistic identity](../MathEconLib/Statistics/OrderStatistics.lean) | Krishna, §2.4, equations (2.6)–(2.7), pp. 18–19 | The textbook calculation motivates `expected_second_highest` and `total_revenue`; the latter extends the comparison through revenue equivalence. |
| [All-pay benchmark bid](../MathEconLib/Auction/AllPurchase/Basic.lean) | Krishna, §3.2.1, pp. 29–30, especially the unnumbered all-pay equilibrium formula on p. 30 | This is the standard all-pay benchmark used within the all-purchase analysis. |
| [Uniform-distribution all-pay formula](../MathEconLib/Auction/AllPurchase/UniformDistribution.lean) | Krishna, Example 3.1, p. 29, and §3.2.1, p. 30 | Krishna uses `[0, 1]`; the library derives the rescaled formula on `[0, vbar]`. |
| [Envelope and payment characterization](../MathEconLib/SingleParameter/Payment.lean), including [the bidder-facing API](../MathEconLib/BidderProblem/TypeDeviationIC.lean) | Myerson (1981), §4, Lemma 2, pp. 63–64, equations (4.2)–(4.3) | The monotonicity and utility-integral characterization supplies necessity and sufficiency. The library isolates the one-agent IC content from feasibility and participation conditions, and supports arbitrary action types. |

**Supplementary primary source:** Roger B. Myerson, “Optimal Auction Design,”
*Mathematics of Operations Research* 6(1), 1981, pp. 58–73
([paper](https://cramton.umd.edu/market-design-papers/myerson-optimal-auction-design.pdf)).
Krishna's §5.1.2, “Incentive Compatibility,” is further textbook reading; its detailed
statements were not included in the chapter excerpt used to verify this map.

The [general envelope development](../MathEconLib/SingleParameter/EnvelopeIC.lean)
proves Lipschitz continuity, almost-everywhere differentiability, and the utility
integral representation under its stated envelope-IC condition. These analytic
formulations should not be presented as verbatim textbook theorem statements.

The exact [strict-monotonicity theorem](../MathEconLib/Auction/StrictMonotonicity.lean),
full order-statistic API, and [finite affiliation and winner's-curse results](../MathEconLib/Auction/Affiliation/)
are referenced by their Lean statements here. No exact citation for these formulations
has been verified in the supplied Krishna chapters. In particular, Proposition 3.1
assumes an increasing equilibrium; it does not prove the library's strict-monotonicity
result. The affiliation results currently concern finite supports, not the continuous
winner's-curse or Linkage Principle results.

## All-purchase auctions

**Scott Duke Kominers observed the all-purchase format in NFT sales and developed
the economic analysis formalized in this repository.** He identified
[this sale announcement by @tiffatronn](https://x.com/tiffatronn/status/1928904850022265170)
as an example of the format. The announcement is provenance for the motivating
mechanism. The Lean model specifies the precise allocation, payment, scarcity,
and behavioral assumptions used in the analysis.

An **economic theory research write-up is pending**. For now, the references for
the analysis are the named definitions and results in the
[Lean all-purchase development](../MathEconLib/Auction/AllPurchase/), including:

- [The mechanism specification](../MathEconLib/Mechanism/Auctions/AllPurchase/Spec.lean).
- [Equilibrium formulas](../MathEconLib/Auction/AllPurchase/ExplicitSolutions.lean).
- [Revenue decomposition](../MathEconLib/Auction/AllPurchase/RevenueDecomposition.lean).
- [Interior pricing](../MathEconLib/Auction/AllPurchase/OptimalPricing.lean).
- [Edition-welfare decomposition](../MathEconLib/Auction/AllPurchase/WelfareDecomposition.lean).

Krishna supplies the standard auction-theory components used in this analysis,
including the all-pay benchmark. The all-purchase pricing and welfare results are
credited to Kominers's analysis and the Lean development, with a paper citation to
be added when the write-up is public. References use theorem names rather than
section or proposition numbers from the evolving development notes.
