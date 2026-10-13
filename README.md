# MathEconLib

MathEconLib is an effort to build a shared formal foundation for economics in [Lean 4](https://leanprover.github.io/), spanning microeconomic theory, macroeconomic theory, and econometrics. 

## Getting Started

New to Lean 4, or to this library? [*Lean 4 and `MathEconLib` — A Beginner's Manual*](docs/BeginnersManual.md) goes from installing the toolchain to reading [`BidderProblem/Basic.lean`](MathEconLib/BidderProblem/Basic.lean) line by line, with runnable exercises throughout. The manual does not require prior knowledge of Lean or economics.

### Quickstart
To install lean, see the [Lean website](https://lean-lang.org/install/). Once you have set up a project, add MathEconLib as a dependency in your `lakefile.toml`:

```toml
[[require]]
name = "matheconlib"
git = "https://github.com/matheconlib/matheconlib"
rev = "main"
```

## Contents

| Module | Highlights |
|--------|---------|
| [`Auction/`](MathEconLib/Auction/) | Bayesian incentive compatibility, symmetric independent private values, revenue equivalence, and equilibrium monotonicity |
| [`Auction/Affiliation/`](MathEconLib/Auction/Affiliation/) | Affiliated densities, log-supermodularity, finite monotone conditional expectations, and the finite winner's-curse inequality |
| [`Auction/AllPurchase/`](MathEconLib/Auction/AllPurchase/) | All-purchase equilibrium formulas, revenue decomposition, quadratic-profit maximization, and edition-welfare benchmarks |
| [`BidderProblem/`](MathEconLib/BidderProblem/) | Interim bidder optimization, the IC hierarchy, Myerson's lemma, and payment uniqueness |
| [`Choice/`](MathEconLib/Choice/) | Choice functions, substitutability, substitute hulls, and qualified completion results |
| [`ForMathlib/`](MathEconLib/ForMathlib/) | Supporting results in analysis, measure theory, order theory, and fixed-point theory |
| [`GameTheory/`](MathEconLib/GameTheory/) | Strategic and Bayesian games, pure and mixed Nash equilibria, and equilibrium existence under the stated assumptions |
| [`Matching/`](MathEconLib/Matching/) | Matching with contracts, stable-outcome existence and lattices, rural hospitals, and finite Gale–Shapley algorithms |
| [`Mechanism/`](MathEconLib/Mechanism/) | General mechanisms, quasilinear environments, incentive compatibility, welfare, and budget balance |
| [`Probability/`](MathEconLib/Probability/) | Finite probability distributions, mixtures, expectations, conditioning, and probability-measure bridges |
| [`SingleParameter/`](MathEconLib/SingleParameter/) | Quasilinear choice problems, incentive compatibility, envelope and payment theorems, and deterministic posted pricing |
| [`Statistics/`](MathEconLib/Statistics/) | Order-statistic distributions and the expected second-highest value |
| [`ValueDistribution/`](MathEconLib/ValueDistribution/) | Value distributions, demand, expected payments, virtual surplus, and posted-price optimality and comparative statics |

## Contributing

`MathEconLib` welcomes your contributions. Before opening a PR, please familiarize yourself with the project design principles in [`DESIGN.md`](DESIGN.md) and the guidelines in [`CONTRIBUTING.md`](CONTRIBUTING.md). If you're looking to contribute, please see issues tagged [good first issue](https://github.com/matheconlib/matheconlib/issues?q=is%3Aissue+state%3Aopen+label%3A%22good+first+issue%22).

Changes to the library API should be preceded by a design issue on GitHub and maintainer approval. 

## Worked Examples

A suite of worked examples is in [`MathEconLibExamples`](MathEconLibExamples/), including:
- [Becker-inspired crime choice](https://github.com/matheconlib/matheconlib/blob/codex/becker-crime-example/MathEconLibExamples/SingleParameter/BeckerCrime.lean)
  ([PR #95 — under review](https://github.com/matheconlib/matheconlib/pull/95)):
  risk-neutral binary choice, cutoff and deterrence results, and aggregate crime
  under a fixed type distribution.
- [Matching pennies](MathEconLibExamples/GameTheory/MatchingPennies.lean): no pure Nash equilibrium and a unique mixed equilibrium with uniform randomization.

Have you built something with `MathEconLib`? We'd love to hear about it! Please reach out to [`contact@mathecon.dev`](mailto:contact@mathecon.dev) to get in touch.

## Building

```bash
lake exe cache get                           # fetch prebuilt Mathlib oleans (do this first)
lake build                                    # build library, API pins, tests, and examples
```
