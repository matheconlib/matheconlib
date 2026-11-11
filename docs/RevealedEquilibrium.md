# Finite revealed equilibrium

The equilibrium module characterizes finite observations of prices, individual
incomes, and aggregate resources that can be supported by one utility function
per consumer. Each consumer uses the same utility at every observation.
Consumption is nonnegative, each consumer maximizes utility on the observed
income budget, and the joint allocation clears every market.

## Source and statement scope

The exact source checked is Donald J. Brown and Rosa L. Matzkin's
[August 1995 Cowles discussion paper 1109](https://cowles.yale.edu/sites/default/files/files/pub/d11/d1109.pdf),
*Testable Restrictions on the Equilibrium Manifold*. The published citation is
Brown and Matzkin (1996), Econometrica **64**(6), 1249–1262,
[DOI: 10.2307/2171830](https://doi.org/10.2307/2171830). The theorem numbering and
statement verification here refer to the checked 1995 version.
Theorem 2, printed p. 7, states the equivalence between equilibrium rationalization
and a joint solution to consumer Afriat inequalities (2.1), positive multipliers
and nonnegative consumption (2.2), individual budget equalities (2.3), and market
clearing (2.4). Its proof on printed p. 8 applies Afriat separately to each
consumer while retaining the market-clearing allocation.

Section 2 of the checked source assumes strictly positive individual endowments and
normalized positive prices. This income/resource formulation uses strictly positive
prices without normalization and admits nonnegative aggregate boundary cases,
including the rationalizable example’s zero resource coordinates, so its boundary
scope is broader than that source setup.

The source describes its utilities as continuous, concave, and monotone. The
formal regular-utility predicate explicitly requires **strict** monotonicity:
componentwise weak improvement with at least one strict improvement raises
utility. This fixes the nonsatiation content needed by the converse. Weak
monotonicity alone would allow constant utilities and would not imply the
positive-multiplier characterization. The independent locally nonsatiated
formulation states its premise on the nonnegative orthant explicitly and starts
with weak budget inequalities; budget exhaustion is then proved.

The constructed regular utilities extend to the full real bundle space, while
maximization is restricted to nonnegative bundles. For finite nonempty
observations and strictly positive prices, regular rationalization is equivalent
to joint Afriat feasibility. With at least one commodity, locally nonsatiated
rationalization is also equivalent to that condition. The algebraic GARP–Afriat
equivalence needs only finite observations and includes empty data.

## Public contracts

The public import is `MathEconLib.RevealedPreference`.

| Predicate | Mathematical content |
| --- | --- |
| `AllocationFeasible D x` | Nonnegative consumption, exhausted individual budgets, and clearing for one joint allocation array |
| `UtilityMaximizes D x u` | Each consumer's choices maximize the same utility across observations on nonnegative income budgets |
| `HasAfriatAllocation D` | A feasible allocation, utility levels, and positive multipliers satisfying every consumer's Afriat inequalities |
| `HasGARPAllocation D` | One feasible allocation array satisfying every consumer's GARP |
| `HasOrdinalAllocation D` | A finite ordinal rank profile and a jointly feasible allocation satisfying its weak and strict expenditure inequalities |
| `GeneralizedAxiomOfRevealedEquilibrium D` | A finite ordinal rank profile whose completely eliminated inequalities in observed data hold |
| `HasRegularEquilibriumRationalization D` | A feasible allocation supported by continuous, concave, strictly increasing utilities |
| `HasLocallyNonsatiatedEquilibriumRationalization D` | Nonnegative clearing allocations that are affordable utility maximizers for locally nonsatiated utilities |

`hasRegularEquilibriumRationalization_iff_hasAfriatAllocation` is the finite
regular-utility certificate equivalence.
`hasLocallyNonsatiatedEquilibriumRationalization_iff_hasAfriatAllocation` supplies
the ordinary locally nonsatiated formulation. `AllocationFeasible.budget_adding_up`
derives the aggregate income identity from individual exhaustion and clearing.

## Finite ordinal linear formulation

`EquilibriumAxiom` assigns each consumer and observation a rank in
`Fin (Fintype.card T + 1)`. For a fixed rank profile, a bundle assigned a higher
rank than observation `t` must cost strictly more than the consumer's income at
prices `t`; a bundle assigned an equal rank must cost at least that income.
These inequalities use the same nonnegative, budget-exhausting, market-clearing
allocation array.

`hasGARPAllocation_iff_hasOrdinalAllocation` proves that this finite disjunction
of weak and strict linear feasibility systems is equivalent to joint GARP. It
allows ties and empty observation sets. The regular-equilibrium equivalence
additionally uses positive prices and nonempty observations. This formulation
eliminates continuous utility levels and multipliers, including the bilinear
multiplier–consumption products in Afriat inequalities. This intermediate
formulation retains latent consumption variables.

## Observable generalized axiom

`EquilibriumElimination` encodes each fixed-rank system in one variable vector
indexed by consumer, observation, and commodity. Nonnegative consumption produces
weak rows; each budget and clearing equality produces two opposite weak rows;
strict rank comparisons produce strict expenditure rows. The encoding theorem
preserves the same joint allocation across every household and observation.

`EquilibriumAlternative` then applies finite Fourier–Motzkin elimination. Every
positive-coefficient lower bound is compared with every negative-coefficient
upper bound. The combined row is strict if either bound is strict. Zero-coefficient
rows persist, and divisions use coefficients whose signs ensure they are nonzero.
After all consumption coordinates are eliminated, only weak or strict comparisons
of functions of the observed data remain.

`GeneralizedAxiomOfRevealedEquilibrium D` asserts that one of the finitely many
rank profiles passes these eliminated comparisons. Its definition has finite
rank and row quantification, with no quantification over continuous latent
consumption, utility levels, or multipliers. This is a descriptive name for the
present formulation; it makes no claim of priority or uniquely established usage.

`hasGARPAllocation_iff_generalizedAxiomOfRevealedEquilibrium` proves exact
equivalence without sign assumptions or nonempty observations. For positive
prices and finite nonempty observations, the regular and increasing utility
equivalences follow. The locally nonsatiated equivalence additionally requires
at least one commodity. All rationalizations use ordinary utility maximization.

The elimination operates mathematically on arbitrary real coefficients. Its
Lean definition is noncomputable, including coefficient-sign decisions and
finite index choices. It provides a finite exact characterization, not an
implemented fast solver or a complexity guarantee. It does not implement
general Tarski–Seidenberg elimination or normalize the resulting expressions
into a specified polynomial formula. The separate economic dual condition in
`EquilibriumAxiom` is proved necessary; the full observable equivalence uses
Fourier–Motzkin elimination and does not assume a converse for that dual condition.

## Checked applications and limits

`MathEconLibExamples.RevealedEquilibrium` supplies two exact illustrative markets,
each with two consumers, two goods, and two observations. These are constructed
examples, not empirical inputs or examples attributed to the source paper.

The rationalizable market has prices `(1,2)` and `(2,1)`, income `2` per consumer,
and resources `(4,0)` and `(0,4)`. Each consumer buys `(2,0)` and `(0,2)`.
Constant utility levels `2` and multipliers `1` satisfy the joint certificate.
Applying the named equivalences proves regular and locally nonsatiated
equilibrium rationalization and satisfaction of the observable generalized axiom.

The refutable market has prices `(2,1)` and `(1,2)`, income `9` per consumer, and
resources `(8,2)` and `(2,8)`. Equal sharing proves budget-exhausting,
market-clearing feasibility at every observation. For any feasible allocation,
consumer zero's expenditure on the other observation's bundle is at most `15/2`,
strictly below income `9`, in both directions. This forces a strict
two-observation revealed-preference cycle. Hence no feasible allocation supports
GARP, an Afriat certificate, increasing utilities, or locally nonsatiated utilities.
The observable generalized axiom therefore fails for these same data.

Tests cover empty observations and zero goods. Zero goods admit the regular
certificate formulation at zero income, but no utility on the singleton
consumption domain is locally nonsatiated. This explains the positive
commodity-count premise in the locally nonsatiated equivalence. Linear-elimination
tests distinguish coincident closed bounds from incompatible strict endpoints,
check open bounds with a positive gap, and cover zero rows and empty row families.

The paper introduces WARE after Theorem 2 on printed p. 8 using a two-observation,
two-consumer specialization. Its particular WARE formula, smooth utility
reconstruction, strict concavity, and demand uniqueness are outside this
development. The generalized axiom here is derived through the explicit ordinal
encoding and finite linear elimination described above.

The conclusions concern the supplied formal data and stated premises. They do
not establish calibration to a real economy, predictive improvement, equilibrium
existence at unobserved endowments, or an executable solver.
