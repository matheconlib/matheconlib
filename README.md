# MathEconLib

MathEconLib is an effort to build a shared formal foundation for economics in [Lean 4](https://lean-lang.org/), with the long-term scope of microeconomic theory, macroeconomic theory, and econometrics. Current development focuses on microeconomic theory and its mathematical foundations, building on [Mathlib](https://github.com/leanprover-community/mathlib4).

[Project website](https://mathecon.dev) · [Beginner's manual](docs/BeginnersManual.md) · [Documentation](docs/) · [Contributing](CONTRIBUTING.md)

## Getting started

New to Lean or to this library? [*Lean 4 and `MathEconLib` — A Beginner's Manual*](docs/BeginnersManual.md) covers installation, reading a real library file, and runnable exercises. It assumes mathematical familiarity but no prior Lean or economics knowledge.

### Use MathEconLib in a project

[Install Lean](https://lean-lang.org/install/) and create a Lean project. Match your project's `lean-toolchain` to [the version used by MathEconLib](lean-toolchain), then add this dependency to your `lakefile.toml`:

```toml
[[require]]
name = "matheconlib"
git = "https://github.com/matheconlib/matheconlib"
rev = "main"
```

From your project directory, fetch the dependency and prebuilt Mathlib files:

```bash
lake update
lake exe cache get
```

Import the library in a Lean file:

```lean
import MathEconLib
```

For reproducible projects, replace `main` with a specific commit and use the toolchain from that revision.

### Build this repository

After installing Lean, run:

```bash
git clone https://github.com/matheconlib/matheconlib.git
cd matheconlib
lake exe cache get
lake build
```

The checkout's `lean-toolchain` selects the Lean version. The default build checks the library, API stability pins, tests, and worked examples.

## Current coverage

The library is organized around shared definitions and results that economic models can reuse. These are broad entry points, rather than an exhaustive module index:

| Area | Selected topics |
| --- | --- |
| Game theory | [Strategic and Bayesian games](MathEconLib/GameTheory/), pure and mixed Nash equilibria |
| Mechanism design and auctions | [Mechanisms](MathEconLib/Mechanism/), [incentive compatibility and payment identities](MathEconLib/BidderProblem/), [revenue equivalence and auction formats](MathEconLib/Auction/) |
| Choice and matching | [Choice functions and substitutability](MathEconLib/Choice/), [matching with contracts and stable outcomes](MathEconLib/Matching/) |
| Pricing | [Single-parameter choice](MathEconLib/SingleParameter/), [value distributions, posted-price optimality, and comparative statics](MathEconLib/ValueDistribution/) |
| Mathematical foundations | [Probability](MathEconLib/Probability/), [order statistics](MathEconLib/Statistics/), and supporting [analysis, order, and fixed-point results](MathEconLib/ForMathlib/) |

Browse the [source tree](MathEconLib/) for individual modules and their statements, or see [the architecture overview](docs/BeginnersManual.md#appendix-b--how-matheconlib-is-organised) for how the pieces fit together.

## Selected examples and applications

- **Game theory: [matching pennies](MathEconLibExamples/GameTheory/MatchingPennies.lean).** A worked example with no pure Nash equilibrium and a unique mixed equilibrium in which both players randomize uniformly.
- **Pricing: [posted prices with uniform buyer values](MathEconLib/ValueDistribution/UniformPricing.lean).** Optimal pricing within the value-support interval and comparative statics, with [concrete checked applications](MathEconLibTest/ValueDistribution/Examples.lean), including the optimal price of `1/2` for uniform values on `[0, 1]` and zero seller continuation value.
- **Price theory: [a Becker-inspired model of crime](https://github.com/matheconlib/matheconlib/pull/95) (pending PR #95).** A stylized risk-neutral choice model treats the expected sanction as a price, deriving a cutoff rule, individual deterrence results, and aggregate crime under a fixed distribution of net gains.

Worked demonstrations live in [`MathEconLibExamples/`](MathEconLibExamples/); reusable developments live in the core library, with API and regression checks in [`MathEconLibTest/`](MathEconLibTest/).

## Contributing

Contributions of definitions, proofs, worked applications, and documentation are welcome. Start with the [design principles](DESIGN.md) and [contribution guidelines](CONTRIBUTING.md), which explain where developments belong and when a design discussion is needed.

Browse [open issues](https://github.com/matheconlib/matheconlib/issues) for ongoing work, or look for a [good first issue](https://github.com/matheconlib/matheconlib/issues?q=is%3Aissue+state%3Aopen+label%3A%22good+first+issue%22).

Have you built something using MathEconLib, or would you like to get involved? Reach out at [contact@mathecon.dev](mailto:contact@mathecon.dev).
