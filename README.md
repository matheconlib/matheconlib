# MathEconLib

A Lean 4 formalization of fundamental theorems in economic theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Getting Started

New to Lean 4, or to this library?
[*Lean 4 and `MathEconLib` — A Beginner's Manual*](docs/BeginnersManual.md) goes
from installing the toolchain to reading
[`BidderProblem/Basic.lean`](MathEconLib/BidderProblem/Basic.lean) line by line,
with runnable exercises throughout. It assumes no Lean and no auction theory.
Project-owned Lean declarations live under the `MathEconLib` namespace; see
the [public-name mapping](docs/NamespaceMigration.md) for migration guidance.
Shorter names below abbreviate declarations under that namespace.

## Worked Examples

- [Becker-inspired crime choice](https://github.com/AxiomMath/auctionlib/blob/codex/becker-crime-example/MathEconLibExamples/SingleParameter/BeckerCrime.lean)
  ([PR #95 — under review](https://github.com/AxiomMath/auctionlib/pull/95)):
  risk-neutral binary choice, cutoff and deterrence results, and aggregate crime
  under a fixed type distribution.
- [Matching pennies](MathEconLibExamples/GameTheory/MatchingPennies.lean): no pure Nash equilibrium and a unique mixed equilibrium with uniform randomization.

## Mathematical Reference

The primary textbook reference for standard auction results is Vijay Krishna,
*Auction Theory*, 2nd edition (Academic Press, 2010). The
[auction reference map](docs/AuctionReferences.md) gives verified chapter, section, and
result references, explains their relationship to the Lean statements, and records
the provenance of the all-purchase analysis. The Lean statements specify the precise
assumptions and scope of each formalized result.

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
| [`Mechanism/Auctions/Allocation.lean`](MathEconLib/Mechanism/Auctions/Allocation.lean) | `IsUnitIntervalAllocation` coordinate bounds and `UsesStrictHighestBidAllocation` |
| [`Mechanism/Auctions/AllPurchase/Spec.lean`](MathEconLib/Mechanism/Auctions/AllPurchase/Spec.lean) | Explicit `AllPurchaseSpec` price/scarcity data and the `IsAllPurchase` existence predicate |

`IsUnitIntervalAllocation` bounds each coordinate in `[0, 1]`; aggregate feasibility depends on the outcome space and allocation rule. Welfare efficiency compares outcomes using a valuation environment. The strict-highest-bid rule instead describes allocations from bids, awarding nothing on ties.

Checked examples in [`MathEconLibTest/Mechanism/Core.lean`](MathEconLibTest/Mechanism/Core.lean) use the umbrella import, including a truthful posted-price mechanism, concrete all-purchase payments, and a mechanism with infinitely many agents.

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

Scott Duke Kominers observed this format in NFT sales and developed the economic analysis
formalized here. He identified [this sale announcement by @tiffatronn](https://x.com/tiffatronn/status/1928904850022265170)
as an example of the format. An economic theory research write-up is pending; the
[Lean development](MathEconLib/Auction/AllPurchase/) is the current reference for the analysis.
The sale announcement supplies provenance for the motivating format; the formal model and
its assumptions are specified in Lean.

| File | Contents |
|------|----------|
| [`Auction/AllPurchase/Basic.lean`](MathEconLib/Auction/AllPurchase/Basic.lean) | The distribution-based all-pay benchmark bid `Auction.allPayBid` |
| [`Auction/AllPurchase/LinearScarcity.lean`](MathEconLib/Auction/AllPurchase/LinearScarcity.lean) | `QuadraticCostProblem`, `LinearCostProblem`, `InteriorRegimeProblem`, `IsBoundaryRegime`, `LinearScarcityAuction`, and `toQuadraticCostProblem` |
| [`Auction/AllPurchase/ExplicitSolutions.lean`](MathEconLib/Auction/AllPurchase/ExplicitSolutions.lean) | Constant-scarcity, boundary-regime, and interior-regime equilibrium strategy formulas at bidder-problem and auction levels |
| [`Auction/AllPurchase/RevenueDecomposition.lean`](MathEconLib/Auction/AllPurchase/RevenueDecomposition.lean) | Seller gross-revenue decomposition and, under zero lowest-type utility, a bundled-versus-standalone profit-difference identity |
| [`Auction/AllPurchase/OptimalPricing.lean`](MathEconLib/Auction/AllPurchase/OptimalPricing.lean) | Distribution-based all-pay moment, interior equilibrium quantity and actual profit identities, and the interior quadratic profit bound |
| [`Auction/AllPurchase/UniformDistribution.lean`](MathEconLib/Auction/AllPurchase/UniformDistribution.lean) | Closed form for the all-pay benchmark bid under a uniform type distribution |
| [`Auction/AllPurchase/WelfareDecomposition.lean`](MathEconLib/Auction/AllPurchase/WelfareDecomposition.lean) | Actual expected-edition-welfare decomposition under square integrability, a feasible Cournot best-response certificate, variance penalty, and separately justified welfare-gap signs |

The pricing file derives expected purchases and actual seller profit for a supplied interior
auction with independent, identical, bounded, atomless types, a measurable strictly increasing
strategy with integrable purchases, type-deviation incentive compatibility, and the stated
lowest-type utility. Its moment uses the distribution-based all-pay bid. The resulting quadratic
profit bound is attained exactly when the posted price equals the candidate interior price;
this does not prove equilibrium existence at other prices or compare other regimes.
[A complete uniform example with two bidders](MathEconLibExamples/AllPurchase/UniformTwoBidder.lean)
checks all assumptions, including deviations to every real bid, and obtains profit `8/3` at price `2`.
The welfare decomposition uses actual expected edition welfare for any square-integrable
aggregate purchase quantity. The editions-only Cournot profile is a feasible best response
when the posted price does not exceed the scarcity intercept. Its welfare gap is nonnegative;
the contest gap needs additional quantity conditions. Welfare here excludes the contest prize.
[A concrete Cournot application](MathEconLibExamples/AllPurchase/Welfare.lean) constructs the
auction, applies the decomposition, and obtains the welfare gap `25/36`.
The uniform example also applies the decomposition to the privately optimal prize-aware strategy
`β(v) = 1/6 + v/2`. Expected aggregate purchases are `4/3`, with variance `1/6`, and expected edition
welfare is `37/18`. The first-best edition-welfare gap is `7/36 = 25/36 - 1/2`: in this example,
the prize raises edition welfare by `1/2` relative to the editions-only Cournot benchmark.
The contest gap is therefore negative; nonnegativity requires additional assumptions. The prize
raises expected aggregate purchases, although types below `1/3` purchase less than `1/3`.

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

The Bayesian game carrier takes players, types, actions, and payoff values as explicit parameters.
Priors are supplied separately. Finite BNE constrains positive-probability types, and the finite
Bayesian equivalences hold for partially ordered real modules whose order respects addition and
nonnegative scaling. Measurable BNE includes incumbent integrability and, for real payoffs, has an
almost-everywhere interim characterization under the stated measurability and
conditional-integrability assumptions. Pointwise auction IC and induced mechanism games remain
separate integration work.

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
| Interior equilibrium quantity and actual bundled-profit identities under the stated type, strategy, IC, integrability, and baseline-utility assumptions; unique attainment of the algebraic interior profit bound | [`Auction/AllPurchase/OptimalPricing.lean`](MathEconLib/Auction/AllPurchase/OptimalPricing.lean) |
| Expected-edition-welfare decomposition and variance penalty under square-integrable purchases; feasible Cournot best responses and conditional contest-gap nonnegativity | [`Auction/AllPurchase/WelfareDecomposition.lean`](MathEconLib/Auction/AllPurchase/WelfareDecomposition.lean) |
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
- [x] Interior equilibrium quantity and actual seller profit, with the quadratic optimum and a concrete uniform equilibrium
- [x] Expected-edition-welfare decomposition, Cournot best responses, and variance penalty
- [x] Normal-form game foundations and pure/mixed Nash existence under the stated action-space and payoff assumptions
- [x] Affiliation definitions, log-supermodularity, finite monotone conditional expectations, and the finite winner's-curse inequality

Further work includes:

- [ ] Equilibrium existence across prices and global all-purchase pricing across regimes
- [ ] Full Riley--Zeckhauser comparison between posted prices and general selling rules
- [ ] Posted-price comparative statics beyond the uniform family
- [ ] Continuous affiliation results, including the continuous winner's-curse inequality, and later applications such as the Linkage Principle
- [ ] Remaining game-theoretic concepts and their integration with the auction layer
- [ ] Extensive-form and obviously strategy-proof mechanisms
- [ ] Exploratory multi-unit and simultaneous ascending auction models
