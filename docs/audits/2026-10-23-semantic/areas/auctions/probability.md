> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Auction probability bridge and symmetric IPV audit

Audited source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`.

Scope: `MathEconLib/Auction/ValueDistribution.lean` and
`MathEconLib/Auction/SymmetricIPV.lean`. Read-only source audit. Four major
definitions and all fifteen accompanying named results/helpers were inspected.
There is no confirmed local semantic defect. An independent agent separately
reviewed all definitions/results in `SymmetricIPV.lean` and reached the same
conclusion. No fresh Lean compilation was used for this scoped audit.

## Pass 1: declaration inventory

| Declaration | Source line | Disposition |
|---|---:|---|
| `Auction.valueDistribution` | `ValueDistribution.lean:41` | Correct law/pushforward definition |
| `Auction.toMeasure_valueDistribution` | `ValueDistribution.lean:49` | Exact pushforward identity |
| `Auction.valueDistribution_absolutelyContinuous` | `ValueDistribution.lean:60` | Correct density bridge |
| `Auction.valueDistribution_isSupportedOnInterval` | `ValueDistribution.lean:70` | Correct almost-everywhere concentration bridge |
| `Auction.valueDistribution_eq_of_identicalTypes` | `ValueDistribution.lean:82` | Correct identical-law bridge |
| `Auction.cdf_valueDistribution_eq_commonCDF` | `ValueDistribution.lean:91` | Correct CDF bridge |
| `bidThreshold` | `SymmetricIPV.lean:53` | Correct clipped strict-sublevel supremum |
| `bidThreshold.set_nonempty` | `SymmetricIPV.lean:60` | Correct inserted-endpoint helper |
| `bidThreshold.set_bddAbove` | `SymmetricIPV.lean:63` | Correct when `lo ≤ hi` |
| `bidThreshold.mem_Icc` | `SymmetricIPV.lean:70` | Correct when `lo ≤ hi` |
| `bidThreshold.above` | `SymmetricIPV.lean:78` | Correct upper bound for accepted types |
| `bidThreshold.below` | `SymmetricIPV.lean:82` | Correct strict acceptance below threshold under monotonicity |
| `bidThreshold.le_of_not_lt` | `SymmetricIPV.lean:90` | Correct contrapositive |
| `Auction.q_eq_pow` | `SymmetricIPV.lean:109` | Correct under strict allocation, iid atomless types |
| `Auction.lowestType_le_highestType` | `SymmetricIPV.lean:155` | Correct nonempty-support argument |
| `Auction.measure_sigma_lt_eq` | `SymmetricIPV.lean:165` | Correct atomless sandwich |
| `Auction.q_strat_eq_cdf_pow` | `SymmetricIPV.lean:206` | Correct with explicitly measurable weakly increasing strategy |
| `Auction.toOrderStatisticsSetup` | `SymmetricIPV.lean:249` | Correct law-preserving bundling |
| `Auction.S₂` | `SymmetricIPV.lean:259` | Correct ascending zero-based second-highest order statistic |

## Pass 2: intended concepts and equivalence

### `Auction.valueDistribution`

Standard concept: the marginal probability law of real-valued bidder value
`θᵢ`, namely `μᵢ(B) = ℙ({ω : θᵢ(ω) ∈ B})` for Borel `B`.

The definition supplies the auction probability measure, `θᵢ`, and its
measurability to `ValueDistribution.ofRandomVariable`; that definition is
`ProbabilityMeasure.map` (`ValueDistribution/Basic.lean:43–47`).
`toMeasure_valueDistribution` makes the exact equality with `Measure.map`
explicit. This yields both directions of equality with the conventional law:
all Borel probabilities agree, and Borel probabilities determine the measure.
No accidental continuity, independence, identical-law, or support restriction
is present. Discrete, mixed, unbounded, and negative-valued laws are admitted,
as the real-valued concept permits. At `n=0` there is no bidder `i : Fin 0`;
there is no fabricated marginal.

The support theorem requests pointwise bounded realized types and concludes
almost-everywhere distributional concentration. It does not claim the reverse:
null-set modifications can break pointwise boundedness while preserving the
law. Similarly the identical-law theorem does not claim to characterize the
stronger `HasIdenticalTypes` class, whose fields also constrain declared bounds.

### `bidThreshold`

Standard concept: a clipped generalized inverse of a weakly increasing bid
strategy, using the **strict** bid sublevel. Its deliberate empty-set convention
is the lower endpoint. It is not asserted to be an ordinary two-sided inverse.

Let `lo ≤ hi`, let `σ` be weakly increasing on `[lo,hi]`, and write
`t = sup({lo} ∪ {v ∈ [lo,hi] : σ(v)<b})`. The helpers prove exactly the two
directions needed for its intended probability semantics:

1. If `v ∈ [lo,hi]` and `σ(v)<b`, then `v≤t` (`above`).
2. If `v ∈ [lo,hi]` and `v<t`, then `σ(v)<b` (`below`). To check this independently,
   choose an accepted `w>v` from the supremum property; `w=lo` is impossible
   because `v≥lo`; monotonicity gives `σ(v)≤σ(w)<b`.

Thus acceptance and the threshold half-line differ at most at `t` on the type
interval. Under an atomless type law, both have probability `F(t)`. Empty and
full sublevels give `t=lo` and `t=hi`; support and atomlessness imply `F(lo)=0`
and `F(hi)=1`. When `lo>hi`, the set reduces to `{lo}`; the interval membership
and probabilistic theorems correctly do not apply. No defect is induced by the
total definition outside their hypotheses.

### `Auction.toOrderStatisticsSetup`

Standard concept: the same iid measurable real random variables, each absolutely
continuous with respect to Lebesgue measure, packaged for order-statistic
results. The structure copies `A.θ`, measurability, independence, identical
distributions, and the supplied PDFs field by field. Both interpretations have
the identical random variables and identical joint law; it introduces no new
normalization or independence assumption beyond the signature.

### `Auction.S₂`

Standard concept: sort the `n` realized values in ascending order, counting
multiplicity, and take position `n−1` in the usual one-based convention.
`Statistics/OrderStatistics.lean:74–75` sorts the multiset of all bidder-indexed
values; `OrderStatisticsSetup.val` (same file, line 178) applies that operation at each state.
`S₂` takes zero-based index `n−2`, so it is exactly the conventional
second-highest sample value in both directions. At `n=2` it is the minimum;
at `n=3` it is the median. Repeated highest values are retained, so samples
`(0,1,1)` have second-highest value `1`, correctly.

The independent/identical/density assumptions are stronger than needed to
define a deterministic second-highest value; they are explicit API restrictions,
not false outputs. One could generalize `S₂` to all auctions with `n≥2` by
applying `orderStatistics` directly and reserve distributional hypotheses for
theorems. No correction is required to the present definition under its stated
assumptions.

## Pass 3: hostile witness search

All examples below use independent `Uniform[0,1]` values and strict-highest
allocation, with one opponent unless otherwise stated. Each was independently
recomputed from the accepted-type set rather than relying on the probability
formula being audited.

| Attempted failure | Exact accepted opponent-type set, up to endpoints | Threshold and true winning probability | Verdict |
|---|---|---|---|
| Constant `σ≡0`, bid `b=0` | Empty | `t=0`, probability `0=F(0)` | Tie plateau correctly rejected |
| Constant `σ≡0`, bid `b=1` | Entire interval | `t=1`, probability `1=F(1)` | Full sublevel correct |
| `σ(v)=v` below `1/2`, `σ(v)=1/2` above it; bid `b=1/2` | `[0,1/2)` | `t=1/2`, probability `1/2` | Entire flat upper plateau excluded |
| Same strategy, bid `b=3/4` | Entire interval | `t=1`, probability `1` | Crossing plateau correct |
| `σ(v)=v` below `1/2`, `σ(v)=v+1` above it; bid `b=3/4` | `[0,1/2)` | `t=1/2`, probability `1/2` | Bid outside strategy image correct |
| Step `σ(v)=0` below `1/2`, `σ(v)=1` above it; bid `b=1` | `[0,1/2)` | `t=1/2`, probability `1/2` | Positive bid atom causes no error |
| Truthful bids, bid `b<0` / `b>1` | Empty / full | Probability `0` / `1` | Out-of-support bids correct |
| One bidder `n=1` | No opponent restrictions | Probability `1`; `F(t)^0=1`, including `0^0` | Empty-product case correct |
| Realized sample `(0,1,1)` for `S₂` | Sorted multiset `(0,1,1)` | Index `3−2=1` gives `1` | Multiplicity correct |
| Discrete bidder law, e.g. `P(θ=0)=P(θ=1)=1/2` | Pushforward atoms at `0,1` | Same masses | `valueDistribution` does not exclude atomic laws |

Distinction needed for these checks: atomless **values** need not produce
atomless **bids** under a weakly increasing strategy. The formulas nevertheless
remain correct because `UsesStrictHighestBidAllocation`
(`Mechanism/Auctions/Allocation.lean:61–64`) awards zero allocation to all
highest-bid ties. For `σ≡0`, `b=0`, and two bidders, random tie breaking would
give winning probability `1/2`, but this is outside the explicitly stated
allocation rule. It is not a counterexample to the current theorem.

## Pass 4: independent verification and dependency caveats

An independent reviewer reread `SymmetricIPV.lean`, `Auction.Basic`,
`Auction.Typeclasses`, the strict allocation predicate, and ascending
`orderStatistics`. The reviewer independently obtained the threshold sandwich,
checked constant/flat/jumping strategies and `n=1`, and checked `n−2` indexing
with multiplicity. Verdict: no defect under the exact hypotheses. These are
analytic semantic checks; no claim is made that bounded examples prove a
general theorem.

Imported class caveat, delegated to the `Typeclasses.lean` owner:
`HasAtomlessTypes` (`Auction/Typeclasses.lean:47–48`) only constrains bidder `0`
without requiring identical type laws. The scoped probability formulas and the
CDF boundary argument use this class together with `HasIdenticalTypes`, so the
missing all-bidder quantifier does not invalidate them. It may still be a defect
in the standalone class; it is not double-counted as a local finding here.

Primary concept references consulted:

- NIST, [Order Statistics](https://www.itl.nist.gov/div898/software/dataplot/refman2/auxillar/os.htm):
  sample observations ordered from smallest to largest, one statistic per observation.
- S. Dasgupta and R. G. Hansen,
  [Auctions in Corporate Finance](https://mba.tuck.dartmouth.edu/bespeneckbo/cfhandbook/VOLUME_1/CH3-AUCTIONS/ECKBO-CH3-AUCTIONS.pdf),
  section 2.1: distribution of the maximum of `N−1` independent common-law
  values is `F(v)^(N−1)`. The generalized-threshold extension was checked
  directly by the sandwich proof above.
