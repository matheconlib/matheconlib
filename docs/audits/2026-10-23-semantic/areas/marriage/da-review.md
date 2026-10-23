> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Classical marriage deferred acceptance: semantic review

Reviewed source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`.
Source files were read completely; no library source was changed.

**Verdict:** No substantive semantic defect found in the four assigned files.
All 31 inventoried definition-like declarations are mapped below. The
counterexample searches found useful boundaries of stronger, unstated claims;
the actual definitions and theorems make those boundaries explicit.

## Intended concepts and assumptions

The classical concept is finite one-to-one deferred acceptance with strict
preferences, an outside option, and possibly unacceptable partners. In the
original procedure, recipients compare new proposals with their incumbent
holding; rejected proposers advance down their lists. Its output is stable
and optimal for the proposing side. The formal repeated-proposal convention
represents an incumbent holding by having its proposer repeat the same offer.
These are the same state transitions after omitting redundant messages.
[Gale and Shapley (1962), §§2–5](https://rohitvaish.in/data/Papers/%5BGale,%20Shapley%5D%20College%20Admissions%20and%20the%20Stability%20of%20Marriage.pdf).

The generalized concept is iteration of the two-sided acceptance operator on
offer states, ordered by inclusion in the first coordinate and reverse
inclusion in the second. Contracts carried by a state are its coordinate
intersection. The source operator agrees with the displayed operator and
fixed-point interpretation in
[Hatfield and Kominers, §4, Lemma 1 and Theorem 1](https://scottkom.com/assets/articles/Hatfield_Kominers_Contract_Design.pdf).

The market supplies `LinearOrder (Option W)` for every man and
`LinearOrder (Option M)` for every woman (`Preferences.lean:39–43`). Larger
elements are preferred; `none` is singlehood. These are strict rankings, so
there is no tie between distinct partners or between a partner and singlehood.
Both populations have `Fintype` instances throughout the reviewed algorithms.
Executable refinements additionally require `DecidableEq` on both types.
Unequal population sizes and empty populations are allowed. No result here
purports to handle indifferences or infinite populations.

## Complete definition map

Line numbers below are exact declaration starts under
`MathEconLib/Matching/Classical/Marriage/`.

| File and line | Declaration | Standard concept and equivalence assessment |
| --- | --- | --- |
| `DeferredAcceptance.lean:48` | `gsProposals` | Each man's unique favorite unrejected acceptable partner. Equality to the maximum of the unrejected partner menu plus `none` gives both implications; selecting `none` gives no proposal. |
| `DeferredAcceptance.lean:52` | `gsHeld` | Each recipient's unique best acceptable current proposal. The conjunction requires a genuine proposal and the woman's maximizing choice. This excludes both a fabricated holding and an unwanted proposer. |
| `DeferredAcceptance.lean:57` | `gsStep` | Rejection history union exactly the current unheld proposals. No pair is rejected twice as a new pair, and no held proposal is newly rejected. |
| `DeferredAcceptance.lean:61` | `gsRejected` | Iteration of simultaneous rejection updates starting from empty history. This initialization is essential to subsequent stability and optimality statements. |
| `DeferredAcceptance.lean:230` | `gsMatchingAt` | The partial matching induced by a terminal proposal state. The terminal hypothesis makes the men's proposals and women's holdings inverse partial maps. It promises a matching for arbitrary fixed histories, with stability asserted separately only for reachable ones. |
| `DeferredAcceptance.lean:331` | `galeShapleyRoundBound` | Uniform sufficient fuel `card (M × W)` for rejection updates. It is explicitly not a bound on redundant messages or running time. Every nonterminal update adds a pair, so this bound holds without monotonicity in arbitrary histories. |
| `DeferredAcceptance.lean:338` | `galeShapley` | Man-proposing Gale–Shapley output, obtained from the reached terminal history at sufficient fuel. Correct proposer-optimal stable matching. |
| `DeferredAcceptance.lean:396` | `womanGaleShapley` | Woman-proposing Gale–Shapley output. Exchanging market sides and reversing the resulting partial equivalence gives the intended original-side matching. |
| `DeferredAcceptanceComputable.lean:46` | `partnersMFinset` | The partner projection of a finite contract menu incident to a specified man. Filtering before projection excludes other men's partners; membership is exactly `(m,w) ∈ Y`. |
| `DeferredAcceptanceComputable.lean:50` | `partnersWFinset` | Symmetric incident-partner projection for a specified woman; membership is exactly `(m,w) ∈ Y`. |
| `DeferredAcceptanceComputable.lean:85` | `menuMFinset` | Finite offered partner menu augmented by the outside option. No acceptability assumption is imposed on menu membership itself. |
| `DeferredAcceptanceComputable.lean:91` | `menuWFinset` | Symmetric outside-option-augmented menu for a woman. |
| `DeferredAcceptanceComputable.lean:106` | `bestMFinset` | Maximum of the supplied man's finite option menu under his own order; exactly the semantic selector `bestM`. |
| `DeferredAcceptanceComputable.lean:110` | `bestWFinset` | Maximum of the supplied woman's finite option menu under her own order; exactly `bestW`. |
| `DeferredAcceptanceComputable.lean:157` | `gsProposalsFinset` | Finite realization of `gsProposals`. `univ \\ R` enumerates precisely unrejected pairs, and the equality filter selects precisely each man's maximizing real partner. |
| `DeferredAcceptanceComputable.lean:162` | `gsHoldProposalsFinset` | Recipient choice from an arbitrary supplied proposal set. It can retain multiple contracts for a man if supplied arbitrary multi-offer data; its intended input for actual rounds has at most one offer per man. No general matching claim is made for arbitrary `P`. |
| `DeferredAcceptanceComputable.lean:166` | `gsHeldFinset` | Recipient holdings for actual single-offer-per-man proposals; exactly the semantic `gsHeld`. |
| `DeferredAcceptanceComputable.lean:170` | `gsStepFinset` | Finite rejection update; exactly `gsStep` after coercing finite sets to sets. |
| `DeferredAcceptanceComputable.lean:175` | `gsRejectedFinset` | Finite iteration of rejection updates from empty history; state-by-state equality with `gsRejected`. |
| `DeferredAcceptanceComputable.lean:225` | `galeShapleyFinsetWithFuel` | Provisional holdings evaluated at rejection state after `n` updates. Explicitly permits stopping before stabilization, so it does not claim stability for insufficient fuel. |
| `DeferredAcceptanceComputable.lean:235` | `galeShapleyFinset` | Final finite graph after sufficient rejection-update fuel; exactly the man-optimal matching graph. |
| `DeferredAcceptanceComputable.lean:255` | `galeShapleyComputable` | Executable man-proposing DA as a partial equivalence. Both maps use the same terminal state; the erased inverse proof certifies the intended graph. |
| `DeferredAcceptanceComputable.lean:346` | `womanGaleShapleyComputable` | Executable woman-proposing DA via side exchange and reversal; exactly the semantic woman-proposing output. |
| `FixedPointConvergence.lean:48` | `manProposingInitialState` | Top generalized acceptance state: all pairs available to men, none to women. Men are the sellers in the embedding; the second coordinate is dualized, so this is indeed top. |
| `FixedPointConvergence.lean:53` | `deferredAcceptanceState` | The generalized operator's `n`th iterate from top; not asserted equal to the classical rejection state at the same index. |
| `FixedPointConvergence.lean:58` | `deferredAcceptanceOutcome` | Coordinate-intersection contract set at the generalized `n`th state. Intermediate sets need not be feasible matchings; terminal feasibility/stability follows from fixed-point results. |
| `FixedPointConvergence.lean:66` | `deferredAcceptance` | Named specification of the man-optimal generalized endpoint. It is explicitly documented as an endpoint, not as an iteration procedure; eventual realization is proved separately. |
| `FixedPointConvergence.lean:127` | `womanProposingInitialState` | Bottom generalized acceptance state: no pairs available to men, all pairs available to women. |
| `FixedPointConvergence.lean:132` | `womanProposingDeferredAcceptanceState` | The generalized operator's `n`th iterate from bottom, with the intended woman-proposing extremum. |
| `FixedPointConvergence.lean:137` | `womanProposingDeferredAcceptanceOutcome` | Coordinate-intersection contract set at the bottom-origin generalized state. The same intermediate-state qualification applies. |
| `FixedPointConvergence.lean:145` | `womanProposingDeferredAcceptance` | Named specification of the woman-optimal generalized endpoint; eventual attainment by iteration is proved. |

`DeferredAcceptanceFixedPoints.lean` has no definition-like declarations. Its
entire contents were reviewed as the second correctness route. In particular,
`gsMatchingAt_accepts_only_graph` (line 45),
`isFixedPt_stateOf_graphOf_gsMatchingAt` (line 72), and
`stateOf_graphOf_gsMatchingAt_eq_gfp` (line 107) correctly require reached
terminal histories. Generalized fixed-point stability and extremality are then
transferred to the classical endpoint and to its side-exchanged analogue.

## Equivalence reasoning and false-positive/false-negative search

The finite menus contain exactly the offered partners and `none`; the selector
is the unique maximum in the agent's supplied linear order. A real partner is
selected if and only if it is available, preferred to `none`, and preferred to
every other available partner. Thus neither a missed acceptable best partner
nor an invented or unacceptable selection can occur.

The apparent absence of a separate incumbent-holding coordinate is harmless.
If `(m,w)` is held, it is unrejected and remains available after the next
update. The new menu is a subset of the previous one and still contains the
previous maximum, so the same man proposes to the same woman again. Hence the
next recipient comparison includes the previous incumbent plus all newly
arriving proposers, exactly as in ordinary simultaneous DA. Rejected men move
to their next remaining acceptable choice. These two implications identify
every reachable formal round with the usual economic round after suppressing
incumbents' redundant messages.

For a reached terminal state, any putative blocking pair is either unrejected
or rejected. An unrejected partner cannot improve on the man's maximizing
proposal. A rejected proposer is strictly below the woman's final holding.
Individual rationality follows from menu inclusion of `none`. This proves the
formal endpoint satisfies the conventional stability concept. Conversely, the
first-rejection argument ensures no stable-matching pair is ever rejected;
every man's assignment in any conventional stable matching remains in his
final menu. The terminal matching therefore dominates every stable matching
for men, and uniqueness under strict preferences gives the intended endpoint
in both directions. Side exchange gives the symmetric conclusion for women.

The executable refinement uses exactly the same projection, maximum, rejection
complement, filter, union, and iteration operations on finite sets. The
coercion theorems inspect every state, rather than merely asserting equal final
outputs. Their hypotheses are sufficient to transport the same semantics.

The generalized route uses the operator
`(A,B) ↦ (womanAcceptsWithInsert(B), manAcceptsWithInsert(A))` from
`Contracts/StableFixedPoints.lean:60–103`. The men-as-sellers embedding and the
reversed second-coordinate order have the right orientation. Top and bottom
iterations select respectively man-optimal and woman-optimal endpoints. The
code carefully compares endpoints and eventual attainment, without making the
false assertion that generalized and classical intermediate rounds coincide.

## Explicitly verified rejected alarms

These are counterexamples to plausible stronger claims, **not defects in the
stated API**. Each was checked directly and reproduced in
`da-boundary-check.py`; `da-boundary-result.json` records success.

1. **Arbitrary terminal histories need not yield stable matchings.** One man
   `a` and one woman `x`, each preferring the other to being single. Set
   `R = {(a,x)}`. Then proposals and holdings are empty, `gsStep R = R`, and
   `gsMatchingAt R` is the empty matching, blocked by `(a,x)`. This does not
   refute the library: the constructor at `DeferredAcceptance.lean:230` promises
   a matching, while stability at line 276 requires `R = gsRejected n` from
   empty history. The actual empty-origin history never rejects `(a,x)`.

2. **Insufficient fuel can return an unstable holding.** One man `a`, women
   `x,y`; `a` ranks `x > y > none`, `x` ranks `none > a`, and `y` ranks
   `a > none`. At fuel zero, `a` proposes to `x`, who rejects him, so the
   returned holding is empty and `(a,y)` blocks it. After one update he
   proposes to `y` and is held. `galeShapleyFinsetWithFuel` at
   `DeferredAcceptanceComputable.lean:222–226` explicitly permits premature
   termination; `galeShapleyFinset` uses proved sufficient fuel.

3. **`gsStep` is not monotone on arbitrary histories.** Two men `a,b`, one
   woman `x`. Each man ranks `x > none`; `x` ranks `b > a > none`.
   For `R = ∅` and `S = {(b,x)}`, `R ⊆ S`, but
   `gsStep R = {(a,x)}` and `gsStep S = {(b,x)}`. The first set is not a
   subset of the second. Termination at `DeferredAcceptance.lean:261–270` and
   `331–335` correctly relies only on inflationarity, so this is no gap.

4. **Intermediate generalized outcomes need not be matchings.** Use the same
   two-men/one-woman preferences from item 3. At the first generalized iterate
   from `(univ,∅)`, each woman-side insertion test accepts its singleton, and
   each man accepts his only partner. Both coordinates therefore contain
   `{(a,x),(b,x)}`, and their intersection is not one-to-one. The definition
   at `FixedPointConvergence.lean:58` returns a set of contracts; only eventual
   terminal outcomes are claimed stable, at lines 96–123. No intermediate
   matching claim is made.

No proposed source correction is warranted for these examples. In particular,
adding stability to arbitrary terminal histories or to arbitrary fuel outputs
would be an incorrect strengthening.

## Independent finite evidence

The parent marriage checker `check_finite.py` was inspected and independently
rerun: all 1,353 strict profiles for population sizes 0 through 2 passed,
including 9,229 formal/conventional stability comparisons, 2,706 DA comparisons
across both proposal directions, and 5,420 extremality comparisons. Its
independent conventional algorithm consumes preference lists of free men;
it does not reuse the rejection recurrence.

A separate hostile reviewer read the two classical/executable files and
produced `da-hostile-check.py` and `da-hostile-result.json`. It checks 250,183
strict profiles, including every one of the 124,416 profiles for each of
`2×3` and `3×2`, with the outside option at every possible rank. Literal
rejection-set recurrence agrees with a separate free-proposer queue/list
algorithm, gives a stable partial matching, and weakly dominates every
enumerated stable partial matching for the proposing side. Four positive
controls exercise blocking detection, unacceptable assignment detection,
recipient rejection in favor of singlehood, and two stable matchings with
different proposer welfare. The script was inspected and rerun by this review
owner as well.

These are exact checks of the encoded finite instances. They do not execute
the Lean functions, establish compilation, or prove claims for unenumerated
population sizes. Source-level arguments and explicit theorem premises, not
bounded enumeration, support the general semantic assessment.

## Four-pass review record and limitations

1. **Coverage:** Read all 1,342 lines across the four files; map every one of
   the 31 inventoried definition-like declarations. Read dependencies defining
   partner menus, optional maxima, generalized operator, and finite-update
   bound where necessary to interpret each declaration.
2. **Expert reread:** Check direction of preference, outside-option behavior,
   both market orientations, menu incidence, reached versus arbitrary states,
   finite update bound, stable matching first-rejection argument, and the
   generalized operator against primary sources.
3. **Hostile refutation:** Explicit boundary examples above; independent hostile
   source review; independent queue/list algorithm and enumerated partial
   matching oracles. No reportable witness survives the stated premises.
4. **Polish:** Reconcile all 31 declaration names/locations with inventory;
   distinguish rejected alarms from findings; state computation and dependency
   limits. No further substantive issue found in this pass.

No new Lean compilation or kernel verification was performed by this review.
The generalized contract theory and marriage foundations receive separate area
reviews; this note checks their use here, not every proof in those dependencies.
The conclusion is scoped to strict finite one-to-one marriage DA as stated.
