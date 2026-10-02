# MathEconLib

A Lean 4 formalization of fundamental theorems in auction theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Getting Started

New to Lean 4, or to this library?
[*Lean 4 and `MathEconLib` — A Beginner's Manual*](docs/BeginnersManual.md) goes
from installing the toolchain to reading
[`BidderProblem/Basic.lean`](MathEconLib/BidderProblem/Basic.lean) line by line,
with runnable exercises throughout. It assumes no Lean and no auction theory.
Project-owned Lean declarations live under the `MathEconLib` namespace; see
the [public-name mapping](docs/NamespaceMigration.md) for migration guidance.
Shorter names below abbreviate declarations under that namespace.

## Worked Examples (under review)

These examples are on their PR branches and have not yet merged into `main`.

- [Becker-inspired crime choice](https://github.com/AxiomMath/auctionlib/blob/codex/becker-crime-example/MathEconLibExamples/SingleParameter/BeckerCrime.lean)
  ([PR #95 — under review](https://github.com/AxiomMath/auctionlib/pull/95)):
  risk-neutral binary choice, cutoff and deterrence results, and aggregate crime
  under a fixed type distribution.
- [Matching pennies](https://github.com/AxiomMath/auctionlib/blob/examples/matching-pennies/MathEconLibExamples/GameTheory/MatchingPennies.lean)
  ([PR #96 — under review](https://github.com/AxiomMath/auctionlib/pull/96)):
  no pure Nash equilibrium and a unique mixed equilibrium with uniform randomization.

## Mathematical Reference

The auction-theory development is guided by an evolving overview provided by Scott Kominers, [*Auction Theory -- introduction and sketch of potential formalization objectives*](https://www.overleaf.com/project/698329a7c6b8506c1361f68b). The overview includes both completed and prospective objectives; this README describes the material currently implemented in Lean.

The extension from auctions to posted pricing and other single-parameter
problems is described in
[*Pricing Foundations: Mathematical Model and Architecture*](docs/PricingArchitecture.md).

## Architecture

The project-wide principles guiding library design are recorded in
[`DESIGN.md`](DESIGN.md).

The library has three main layers, separating the rules of a mechanism from its probabilistic environment and the resulting interim optimization problem:

```
MathEconLib.Mechanism I A O  — outcome rule + signed transfers over dependent action profiles
MathEconLib.Auction Ω n      — real-bid rules + measurable allocation + type environment on (Ω, ℙ)
MathEconLib.BidderProblem    — one bidder's interim view (winProb, cost, strategy)
```

The reusable deterministic core
[`SingleParameterProblem Action`](MathEconLib/SingleParameter/Basic.lean)
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

The bidder-problem interface retains its mathematical assumptions and conclusions.
`BidderProblem.toSingleParameterProblem` supplies a lossless compatibility
bridge, so existing auction results can reuse the general theorems.

**`Auction → BidderProblem`**: `Auction.toBidderProblem` constructs the interim problem faced by bidder `i` when opponents use a strategy `σ`. For the direct mechanism (`σ = id`), BIC on the auction supplies `HasTypeDeviationIC` on the bidder problem, which in turn unlocks the envelope theorem, Myerson's lemma, and payment equivalence.

`BidderProblem` is the current name for the layer called `ReducedForm` in earlier versions of the library.

## Formalized Results

### Single-Parameter Problems (`SingleParameter/`)

[`SingleParameterProblem Action`](MathEconLib/SingleParameter/Basic.lean)
describes a deterministic quasilinear choice problem with a real-valued type
and an arbitrary action type, subject to the affine-in-type payoff restriction
described above.

| File | Contents |
|------|----------|
| [`SingleParameter/Basic.lean`](MathEconLib/SingleParameter/Basic.lean) | Type interval, allocation, payment, strategy, payoff, induced allocation `q`, utility `U`, strategy replacement, and canonical reduction |
| [`SingleParameter/IC.lean`](MathEconLib/SingleParameter/IC.lean) | Envelope, type-deviation, and universal IC; their implication chain; reduced-form bridges; individual rationality and lowest-type normalization |
| [`SingleParameter/EnvelopeIC.lean`](MathEconLib/SingleParameter/EnvelopeIC.lean) | Monotone allocation, Lipschitz and a.e. differentiable utility, the envelope integral representation, and utility nonnegativity |
| [`SingleParameter/Payment.lean`](MathEconLib/SingleParameter/Payment.lean) | Payment identity, payment uniqueness across action types, and the sufficiency of monotonicity plus the payment identity for type-deviation IC |
| [`SingleParameter/PostedPrice.lean`](MathEconLib/SingleParameter/PostedPrice.lean) | A fixed posted price with real-valued types, the two actions `buy` and `doNotBuy`, universal IC, monotone demand, and individual rationality |

Compile-time checks that the generic posted-price path and the existing
`BidderProblem` path expose the intended APIs live in the separate
[`MathEconLibTest/SingleParameter/Compatibility.lean`](MathEconLibTest/SingleParameter/Compatibility.lean)
test library.

### Value Distributions and Pricing (`ValueDistribution/`)

`ValueDistribution` is a transparent abbreviation for mathlib's
`ProbabilityMeasure ℝ`. The layer adds economic vocabulary and connects a
separately supplied value distribution to the deterministic
`SingleParameterProblem` API; it does not introduce a second probability or
integration theory.

| File | Contents |
|------|----------|
| [`ValueDistribution/Basic.lean`](MathEconLib/ValueDistribution/Basic.lean) | Real-valued probability distributions, random-variable pushforwards, and optional bounded support |
| [`ValueDistribution/Demand.lean`](MathEconLib/ValueDistribution/Demand.lean) | Closed-upper-tail posted-price demand, monotonicity, and atom-sensitive CDF identities |
| [`ValueDistribution/Density.lean`](MathEconLib/ValueDistribution/Density.lean) | Canonical real density and change of measure under absolute continuity |
| [`ValueDistribution/VirtualValue.lean`](MathEconLib/ValueDistribution/VirtualValue.lean) | Division-free virtual-surplus weight and secondary virtual value |
| [`ValueDistribution/TailIntegral.lean`](MathEconLib/ValueDistribution/TailIntegral.lean) | Density-free tail-integral identity, including atomic distributions |
| [`ValueDistribution/SingleParameter.lean`](MathEconLib/ValueDistribution/SingleParameter.lean) | Expected allocation, expected payment, seller profit, and reduced-form preservation |
| [`ValueDistribution/ExpectedPayment.lean`](MathEconLib/ValueDistribution/ExpectedPayment.lean) | Density-free expected-payment representation and density and CDF corollaries |
| [`ValueDistribution/SellerProfit.lean`](MathEconLib/ValueDistribution/SellerProfit.lean) | Expected-allocation density formula and seller-profit virtual-surplus representations |
| [`ValueDistribution/PostedPrice.lean`](MathEconLib/ValueDistribution/PostedPrice.lean) | Posted-price demand, payment, profit, and acquisition-cost invariance of price optimality |
| [`ValueDistribution/PostedPriceOptimality.lean`](MathEconLib/ValueDistribution/PostedPriceOptimality.lean) | Cutoff-integral seller profit and sufficient global and boundary optimality conditions among posted prices |
| [`ValueDistribution/PostedPriceFirstOrder.lean`](MathEconLib/ValueDistribution/PostedPriceFirstOrder.lean) | Pointwise seller-profit differentiation, the division-free necessary condition at an interior local optimum, and nonzero-density virtual-value corollaries |
| [`ValueDistribution/Uniform.lean`](MathEconLib/ValueDistribution/Uniform.lean) | Reusable uniform laws on real intervals, with support, density, demand, and CDF results |
| [`ValueDistribution/UniformPricing.lean`](MathEconLib/ValueDistribution/UniformPricing.lean) | Uniform profit and virtual-surplus formulas, unique optimum within the value interval, interior first-order condition, and comparative statics |

Compile-time pins, representative distributions, and end-to-end pricing checks
live respectively in
[`MathEconLibTest/ValueDistribution/Compatibility.lean`](MathEconLibTest/ValueDistribution/Compatibility.lean),
[`MathEconLibTest/ValueDistribution/Examples.lean`](MathEconLibTest/ValueDistribution/Examples.lean),
and
[`MathEconLibTest/Pricing/Compatibility.lean`](MathEconLibTest/Pricing/Compatibility.lean).

### Mechanism (`Mechanism/`)

[`MathEconLib.Mechanism I A O`](MathEconLib/Mechanism/Core/Mechanism.lean) assigns an outcome and signed transfers to a dependent action profile. Positive transfers are money received by agents; payments are negative transfers. Import [`MathEconLib.Mechanism`](MathEconLib/Mechanism.lean) for the family API.

| File | Contents |
|------|----------|
| [`Mechanism/Core/Profile.lean`](MathEconLib/Mechanism/Core/Profile.lean) | Dependent action and type profiles |
| [`Mechanism/Core/Mechanism.lean`](MathEconLib/Mechanism/Core/Mechanism.lean) | Generic carrier, direct mechanisms, payments, and revenue |
| [`Mechanism/Core/Comap.lean`](MathEconLib/Mechanism/Core/Comap.lean) | Induced mechanisms and identity/composition laws |
| [`Mechanism/Core/Environment.lean`](MathEconLib/Mechanism/Core/Environment.lean) | Quasilinear environments, private values, utility, and welfare |
| [`Mechanism/Core/SolutionConcepts.lean`](MathEconLib/Mechanism/Core/SolutionConcepts.lean) | DSIC, ex-post IR, welfare efficiency, budget balance, and no deficit |
| [`Mechanism/Core/Strategic.lean`](MathEconLib/Mechanism/Core/Strategic.lean) | Utility games, DSIC as truthful dominance, and truthful Nash equilibrium |
| [`Mechanism/Core/Bayesian.lean`](MathEconLib/Mechanism/Core/Bayesian.lean) | Induced Bayesian games, fixed-type agreement, and action-change agreement |
| [`Mechanism/Auctions/Allocation.lean`](MathEconLib/Mechanism/Auctions/Allocation.lean) | `IsUnitIntervalAllocation` coordinate bounds and `UsesStrictHighestBidAllocation` |
| [`Mechanism/Auctions/AllPurchase/Spec.lean`](MathEconLib/Mechanism/Auctions/AllPurchase/Spec.lean) | Explicit `AllPurchaseSpec` price/scarcity data and the `IsAllPurchase` existence predicate |

`IsUnitIntervalAllocation` bounds each coordinate in `[0, 1]`; aggregate feasibility depends on the outcome space and allocation rule. Welfare efficiency compares outcomes using a valuation environment. The strict-highest-bid rule instead describes allocations from bids, awarding nothing on ties.

Checked examples in [`MathEconLibTest/Mechanism/Core.lean`](MathEconLibTest/Mechanism/Core.lean) use the umbrella import, including a truthful posted-price mechanism, concrete all-purchase payments, and a mechanism with infinitely many agents.

[`MathEconLibTest/Mechanism/Games.lean`](MathEconLibTest/Mechanism/Games.lean) pins the induced-game contracts. The utility game keeps the full true profile fixed while reports vary. DSIC requires truthful reports to be dominant against all opponents' reports; truthful Nash equilibrium alone compares against truthful opponents.

`M.inducedBayesianGame E` evaluates `E.utility M` at each action and true type profile. Its `toStrategicGame θ` is exactly `E.utilityGame M θ`. Inducing either game commutes with `Mechanism.comap`, including action maps that restrict the available reports or identify several actions. These constructions require no prior or private-values assumption.

### Bidder Problem (`BidderProblem/`)

[`BidderProblem`](MathEconLib/BidderProblem/Basic.lean) captures a bidder's interim view with quasi-linear payoff $\pi(v, b) = v \cdot \text{winProb}(b) - \text{cost}(b)$.

Three IC levels form a typeclass chain:

$$\texttt{HasUniversalIC} \Rightarrow \texttt{HasTypeDeviationIC} \Rightarrow \texttt{HasEnvelopeIC}$$

| File | Contents |
|------|----------|
| [`BidderProblem/Basic.lean`](MathEconLib/BidderProblem/Basic.lean) | `BidderProblem`, `payoff`, `q`, `U`, `IsRegular`, and the lossless conversion to `SingleParameterProblem ℝ` |
| [`BidderProblem/EnvelopeIC.lean`](MathEconLib/BidderProblem/EnvelopeIC.lean) | `HasEnvelopeIC`, its general compatibility bridge, and the original bidder envelope API backed by the general theorems |
| [`BidderProblem/TypeDeviationIC.lean`](MathEconLib/BidderProblem/TypeDeviationIC.lean) | `HasTypeDeviationIC`, its general compatibility bridge, payment identity and uniqueness, `allPayBid`, `netPaymentIdentity`, and Myerson sufficiency |
| [`BidderProblem/UniversalIC.lean`](MathEconLib/BidderProblem/UniversalIC.lean) | `HasUniversalIC` over a feasible bid set and bridges to both the bidder and general IC hierarchies |

### Auction (`Auction/`)

[`Auction Ω n`](MathEconLib/Auction/Basic.lean) combines real-bid mechanism rules with measurable allocation coordinates and the probabilistic environment. The generic mechanism itself has no measurability requirement.

Interim quantities use Mathlib’s totalized Bochner integral, which equals zero when its integrand is not integrable. Arbitrary strategies need not be measurable. Measurable strategies together with `IsUnitIntervalAllocation` ensure allocation integrability, including truthful reporting; payment integrability requires separate hypotheses.

| File | Contents |
|------|----------|
| [`Auction/Basic.lean`](MathEconLib/Auction/Basic.lean) | `Auction`, interim quantities `q`/`p`/`U` and `q_strat`/`p_strat`, IR notions, `BIC`, `toBidderProblem`, `payment_formula`, and `payment_equivalence` |
| [`Auction/Typeclasses.lean`](MathEconLib/Auction/Typeclasses.lean) | Composable assumptions on independent, identical, bounded, dense, and atomless types; `IsSymmetricIPV`; common type bounds and CDF |
| [`Auction/ValueDistribution.lean`](MathEconLib/Auction/ValueDistribution.lean) | Additive pushforward bridge from each bidder's type random variable to a real-valued value distribution |
| [`Auction/IdenticalTypes.lean`](MathEconLib/Auction/IdenticalTypes.lean) | Expectation identities requiring identical type distributions |
| [`Auction/SymmetricIPV.lean`](MathEconLib/Auction/SymmetricIPV.lean) | `bidThreshold`, `q_eq_pow`, `q_strat_eq_cdf_pow`, and the bridge to order statistics |
| [`Auction/RevenueEquivalence.lean`](MathEconLib/Auction/RevenueEquivalence.lean) | `payment_formula_efficient`, `total_revenue` (= $\mathbb{E}[S_2]$), `revenue_equivalence` |
| [`Auction/StrictMonotonicity.lean`](MathEconLib/Auction/StrictMonotonicity.lean) | `HasPosDensity`, strict monotonicity of an equilibrium strategy, and `no_ties` |

### All-Purchase Auctions (`Auction/AllPurchase/`)

The all-purchase development specializes the general framework to auctions in which every bidder purchases editions while the highest bid receives the allocation.

| File | Contents |
|------|----------|
| [`Auction/AllPurchase/Basic.lean`](MathEconLib/Auction/AllPurchase/Basic.lean) | The distribution-based all-pay benchmark bid `Auction.allPayBid` |
| [`Auction/AllPurchase/LinearScarcity.lean`](MathEconLib/Auction/AllPurchase/LinearScarcity.lean) | `QuadraticCostProblem`, `LinearCostProblem`, `InteriorRegimeProblem`, `IsBoundaryRegime`, `LinearScarcityAuction`, and `toQuadraticCostProblem` |
| [`Auction/AllPurchase/ExplicitSolutions.lean`](MathEconLib/Auction/AllPurchase/ExplicitSolutions.lean) | Constant-scarcity, boundary-regime, and interior-regime equilibrium strategy formulas at bidder-problem and auction levels |
| [`Auction/AllPurchase/RevenueDecomposition.lean`](MathEconLib/Auction/AllPurchase/RevenueDecomposition.lean) | Seller gross-revenue decomposition and, under zero lowest-type utility, a bundled-versus-standalone profit-difference identity |
| [`Auction/AllPurchase/OptimalPricing.lean`](MathEconLib/Auction/AllPurchase/OptimalPricing.lean) | Unique unconstrained maximizer of the defined quadratic profit formula for `α > 0` and `n ≥ 1`, plus an algebraic interior-regime condition |
| [`Auction/AllPurchase/UniformDistribution.lean`](MathEconLib/Auction/AllPurchase/UniformDistribution.lean) | Closed form for the all-pay benchmark bid under a uniform type distribution |
| [`Auction/AllPurchase/WelfareDecomposition.lean`](MathEconLib/Auction/AllPurchase/WelfareDecomposition.lean) | Edition-welfare benchmarks and an upper bound for `α > 0`, algebraic welfare-gap and moment identities, and an expected edition-welfare formula under integrability assumptions |

The pricing file proves maximization and uniqueness for a specified quadratic
profit formula. Connecting that formula to an auction's equilibrium quantity
and actual seller profit remains work in progress. The welfare file proves
benchmark bounds, algebraic gap identities, and an expected edition-welfare
formula when aggregate quantity and its square are integrable. The
equilibrium-based Cournot and contest-loss decomposition remains work in
progress in [#46](https://github.com/AxiomMath/auctionlib/issues/46).

### Affiliation (`Auction/Affiliation/`)

| File | Contents |
|------|----------|
| [`Auction/Affiliation/Basic.lean`](MathEconLib/Auction/Affiliation/Basic.lean) | Affiliated densities, product factorization, signal/value environments, private values, and independent and affiliated signals |
| [`Auction/Affiliation/LogSupermodular.lean`](MathEconLib/Auction/Affiliation/LogSupermodular.lean) | Equivalence between affiliation and log-supermodularity for strictly positive densities |
| [`Auction/Affiliation/FiniteCondExp.lean`](MathEconLib/Auction/Affiliation/FiniteCondExp.lean) | Finite weighted conditional averages and a reusable affiliation comparison for lattice-ordered conditioning events |
| [`Auction/Affiliation/MonotoneCondExp.lean`](MathEconLib/Auction/Affiliation/MonotoneCondExp.lean) | Monotonicity of conditional expectations for affiliated distributions on finite sublattices |
| [`Auction/Affiliation/WinnersCurse.lean`](MathEconLib/Auction/Affiliation/WinnersCurse.lean) | The winner's-curse inequality for affiliated distributions on finite sublattices |

The continuous conditional-expectation and winner's-curse results, together with later applications such as the Linkage Principle, are not yet formalized.

### Game Theory (`GameTheory/`)

| File | Contents |
|------|----------|
| [`GameTheory/Equilibrium/Problem.lean`](MathEconLib/GameTheory/Equilibrium/Problem.lean) | Shared admissible-deviation equilibrium and forward/backward transport |
| [`GameTheory/Strategic/Basic.lean`](MathEconLib/GameTheory/Strategic/Basic.lean) | Payoff-based games, dominance, and pure/strict/strong Nash equilibria |
| [`GameTheory/Strategic/Outcome.lean`](MathEconLib/GameTheory/Strategic/Outcome.lean) | Outcome games, payoff structures, probability-measure mixing, and expected utility |
| [`GameTheory/Strategic/Mixed.lean`](MathEconLib/GameTheory/Strategic/Mixed.lean) | Independent probability-measure mixed strategies and mixed Nash equilibrium |
| [`GameTheory/Strategic/Mixed/Finite.lean`](MathEconLib/GameTheory/Strategic/Mixed/Finite.lean) | Finite probability weights, finite-sum payoffs, and agreement with probability-measure mixing |
| [`GameTheory/Strategic/Existence.lean`](MathEconLib/GameTheory/Strategic/Existence.lean) | Pure Nash existence for quasiconcave payoffs on compact convex action spaces and mixed Nash existence |
| [`GameTheory/Strategic/Bayesian/Finite.lean`](MathEconLib/GameTheory/Strategic/Bayesian/Finite.lean) | Finite-type pure BNE, null-type conventions, and expanded-game Nash |
| [`GameTheory/Strategic/Bayesian/FiniteMeasurable.lean`](MathEconLib/GameTheory/Strategic/Bayesian/FiniteMeasurable.lean) | Finite and measurable equilibrium agreement |
| [`GameTheory/Strategic/Bayesian/Measurable/PureBNE.lean`](MathEconLib/GameTheory/Strategic/Bayesian/Measurable/PureBNE.lean) | Measurable whole-strategy deviations and integrable ex-ante BNE |
| [`GameTheory/Strategic/Bayesian/Measurable/InterimConverse.lean`](MathEconLib/GameTheory/Strategic/Bayesian/Measurable/InterimConverse.lean) | Explicit conditional beliefs and the guarded interim/ex-ante equivalence |

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
this condition. For bounded measurable games, `StrategicGame.Bounded` supplies the
integrability hypotheses of `isMixedNash_iff_isNash`.

The Bayesian game carrier takes players, types, actions, and payoff values as explicit parameters. Priors are supplied separately. Finite BNE constrains positive-probability types, and the finite Bayesian equivalences hold for partially ordered real modules whose order respects addition and nonnegative scaling. Measurable BNE includes incumbent integrability and, for real payoffs, has an almost-everywhere interim characterization under the stated measurability and conditional-integrability assumptions. Mechanism utility already supplies the induced Bayesian game; connecting auction priors, interim utility, and pointwise auction IC remains separate integration work.

`StrategicGame.comapActions` and `BayesianGame.comapActions` evaluate payoffs at translated actions, with identity and composition laws, and `BayesianGame.toStrategicGame θ` fixes the full true type profile. Fixing types commutes with action translation. [`MathEconLibTest/GameTheory/ActionMaps.lean`](MathEconLibTest/GameTheory/ActionMaps.lean) pins these signatures with independent carrier universes and arbitrary payoff values.

### Key Theorems

The linked Lean statements specify each result's definitions and hypotheses.

| Result | Location |
|--------|----------|
| Envelope theorem: 1-Lipschitz utility, $U' = q$ a.e., and integral representation on the type interval under `HasEnvelopeIC` | [`BidderProblem/EnvelopeIC.lean`](MathEconLib/BidderProblem/EnvelopeIC.lean) |
| Myerson's lemma: monotone allocation, payment identity, and payment uniqueness under type-deviation IC; the converse follows from monotonicity and the payment identity | [`BidderProblem/TypeDeviationIC.lean`](MathEconLib/BidderProblem/TypeDeviationIC.lean) |
| General payment equivalence for BIC auctions with allocation coordinates in `[0, 1]`, matching type bounds, interim allocation, and lowest-type utility | [`Auction/Basic.lean`](MathEconLib/Auction/Basic.lean) |
| Truthful-opponent winning probability $q(i,s)=F(s)^{n-1}$ under strict-highest-bid allocation and independent, identically distributed, atomless types | [`Auction/SymmetricIPV.lean`](MathEconLib/Auction/SymmetricIPV.lean) |
| Revenue equivalence for symmetric IPV BIC auctions with at least two bidders, allocation coordinates in `[0, 1]`, matching type bounds, interim allocations and type distributions, zero lowest-type utility, and the stated payment measurability/integrability assumptions | [`Auction/RevenueEquivalence.lean`](MathEconLib/Auction/RevenueEquivalence.lean) |
| Expected revenue $=\mathbb{E}[S_2]$ for symmetric IPV auctions with at least two bidders, strict-highest-bid allocation, BIC, and zero lowest-type utility | [`Auction/RevenueEquivalence.lean`](MathEconLib/Auction/RevenueEquivalence.lean) |
| Strict monotonicity on the type interval with at least two bidders, strict-highest-bid allocation, the stated type assumptions, positive density, a measurable regular strategy, nonnegative lowest type, and universal IC over nonnegative bids | [`Auction/StrictMonotonicity.lean`](MathEconLib/Auction/StrictMonotonicity.lean) |
| All-purchase revenue decomposition under the stated type, strategy, IC, and integrability assumptions; zero lowest-type utility gives a bundled-versus-standalone profit-difference identity | [`Auction/AllPurchase/RevenueDecomposition.lean`](MathEconLib/Auction/AllPurchase/RevenueDecomposition.lean) |
| Unique maximizer of the defined quadratic profit formula for `α > 0` and `n ≥ 1` | [`Auction/AllPurchase/OptimalPricing.lean`](MathEconLib/Auction/AllPurchase/OptimalPricing.lean) |
| Edition-welfare bound for `α > 0`, algebraic welfare-gap identities, and an expected edition-welfare formula when aggregate quantity and its square are integrable | [`Auction/AllPurchase/WelfareDecomposition.lean`](MathEconLib/Auction/AllPurchase/WelfareDecomposition.lean) |
| Winner's-curse inequality on finite sublattices with affiliated positive weights, monotone nonnegative values, and a nonempty winning event | [`Auction/Affiliation/WinnersCurse.lean`](MathEconLib/Auction/Affiliation/WinnersCurse.lean) |
| Pure Nash existence for finite-player games under compact/convex action-space and continuous/quasiconcave payoff assumptions; mixed existence for finite games and compact metrizable games with continuous payoffs | [`GameTheory/Strategic/Existence.lean`](MathEconLib/GameTheory/Strategic/Existence.lean) |

### Auxiliary

| File | Contents |
|------|----------|
| [`Statistics/OrderStatistics.lean`](MathEconLib/Statistics/OrderStatistics.lean) | CDF/PDF of order statistics, `expected_second_highest` |
| [`ForMathlib/AbsolutelyContinuous.lean`](MathEconLib/ForMathlib/AbsolutelyContinuous.lean) | AC function raised to a power, CDF of AC measure |
| [`ForMathlib/Kakutani.lean`](MathEconLib/ForMathlib/Kakutani.lean) | Kakutani--Glicksberg--Fan fixed-point theorem used by the Nash-existence development |
| [`ForMathlib/Schauder.lean`](MathEconLib/ForMathlib/Schauder.lean) | Schauder fixed-point theorem |

## Building

```bash
lake exe cache get                           # fetch prebuilt Mathlib oleans (do this first)
bash scripts/update-imports.sh               # regenerate and verify library and test imports
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
- [x] Uniform posted-price optimality and comparative statics of interval endpoints and continuation value
- [x] General `Mechanism` + `Auction` + `BidderProblem` framework
- [x] Envelope theorem, Myerson's lemma, and revenue equivalence
- [x] All-purchase equilibrium characterization, explicit solutions, and revenue decomposition
- [x] Quadratic-profit maximization and edition-welfare benchmark and moment identities
- [x] Normal-form game foundations and pure/mixed Nash existence under the stated action-space and payoff assumptions
- [x] Affiliation definitions, log-supermodularity, finite monotone conditional expectations, and the finite winner's-curse inequality

Further work includes:

- [ ] Auction-level derivation of the interior-regime profit formula ([#46](https://github.com/AxiomMath/auctionlib/issues/46))
- [ ] Equilibrium-based welfare decomposition and separately justified loss-nonnegativity results ([#46](https://github.com/AxiomMath/auctionlib/issues/46))
- [ ] Full Riley--Zeckhauser comparison between posted prices and general selling rules
- [ ] Posted-price comparative statics beyond the uniform family
- [ ] Continuous affiliation results, including the continuous winner's-curse inequality, and later applications such as the Linkage Principle
- [ ] Remaining game-theoretic concepts and their integration with the auction layer
- [ ] Extensive-form and obviously strategy-proof mechanisms
- [ ] Exploratory multi-unit and simultaneous ascending auction models
