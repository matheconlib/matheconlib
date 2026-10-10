# References for matching with contracts

This map records the primary-source comparisons completed for PR #103 on
10 October 2026. References prefer published versions. Page numbers are printed
page numbers, not PDF page indices. Choice declarations belong to
`MathEconLib.Choice.ChoiceFunction`; market declarations belong to
`MathEconLib.Matching.Market`. Names below omit these prefixes where clear.

## Hatfield–Kominers (2025): HKSurvey2025

John William Hatfield and Scott Duke Kominers, *The theory of matching with
contracts*, Chapter 5, Handbook of the Economics of Matching **2** (2025),
409–487. [Published chapter](https://doi.org/10.1016/bs.hesmat.2025.10.005).

The published 79-page chapter supplied for this review was checked directly.
The paired references `2.1/3.1` and `2.2/3.2` identify the many-to-one and
many-to-many versions in this same chapter. They are not alternative edition
numbers. Theorem 2.1 uses bullets, so cite its first or second bullet rather
than suggesting that the printed statement labels them “(i)” and “(ii).”

### Choice definitions and completions

| Lean declaration or construction | Checked published locator |
| --- | --- |
| `ChoiceFunction`; `ofSetLinearOrder` | §2.1.1, choice functions and preference-induced choice, p. 412 |
| `Consistent` | Standing IRC assumption and footnote 10, p. 413 |
| `Substitutable.not_mem_insert_insert` | Definition 2.1, p. 414 |
| `Substitutable`; `substitutable_iff_forall_insert_insert` | Definition 2.1 and the following arbitrary-added-set formulation, p. 414 |
| `rejected`; `substitutable_iff_monotone_rejected` | Rejection-function discussion following Definition 2.1, p. 414 |
| `SizeMonotone` | Definition 2.2, p. 415 |
| `UnitDemand`; its substitutability and size-monotonicity implications under IRC | §2.1.1, p. 413; observation after Definition 2.2, p. 415 |
| `pathIndependent_iff_substitutable_and_consistent` | Footnote 16, p. 414 |
| `IsCompletionOf` | §6.1, unnumbered completion definition immediately before Definition 6.1, p. 471 |
| `SubstitutablyCompletable`; `BuyersSubstitutablyCompletable` | Definition 6.1, p. 471 |
| `HasConsistentSubstitutableCompletion`; `BuyersHaveConsistentSubstitutableCompletions` | Standing IRC convention, p. 413, and the hypotheses underlying Theorem 6.1, p. 471 |
| `MathEconLibTest/Choice/CompletionCounterexamples.lean` | Buyer-choice component of Example 6.1, p. 469; completion on p. 471, repeated on p. 472 |
| Finite unilateral-to-completion implication | Footnote 88, p. 470, attributing the implication to Zhang (2016) and Kadam (2017) |

The chapter has finite buyers, sellers and contract terms (p. 412), and assumes
IRC throughout (p. 413). Lean's arbitrary-type definitions are more general:
set-form IRC is stronger than single-deletion IRC on infinite menus, and the
single-addition characterization of substitutability needs the stated finite
domain hypothesis. `SizeMonotone` compares finite menus. Unit demand alone does
not supply the two regularity implications cited above.

The survey defines an agent's rejection set as `Yᵢ ∖ Cᵢ(Y)`; generic Lean
choice uses `Y ∖ C(Y)`. These agree literally on menus of the agent's own
contracts. The arbitrary represented-family construction `ofBundleOrder`,
including its empty fallback, goes beyond the displayed preference-induced
choice formula.

For Example 6.1, Lean's `a, b, c` correspond to the survey's `x′, x, y`.
The checked construction is the buyer's three-contract choice rule and its
completion; the survey's full market also has another buyer and contract
`ŷ`. The infinite-menu example in `Choice/Counterexamples.lean` is a Lean
counterexample beyond the survey's finite setting, not an example from the
survey.

Completion does not mean pointwise enlargement. Definition 6.1's displayed
formula does not separately impose IRC; the chapter's standing convention
must still be accounted for. Lean therefore keeps bare substitutable
completability separate from the existence of one completion satisfying both
substitutability and IRC. The contracts development currently supplies those
hypotheses and choice-level implications, not the market-existence reduction
of Theorem 6.1.

The survey discusses unilateral and bilateral substitutability on p. 470 but
does not give numbered definitions of them. Use the checked HK2010 locators
below. Footnote 88 is a published cross-reference for the finite completion
implication, not a source for Lean's additional infinite-domain or enlargement
claims.

### Stability, fixed points and counting

| Lean declaration or construction | Checked published locator |
| --- | --- |
| `Market`, incidence maps and supported choices | §2.1.1, pp. 412–413; many-to-many extension §3.1.1, pp. 437–438 |
| `IndRational`, `Blocks`, `Stable`, `PairwiseStable` | Definitions 2.3 and 2.4, p. 416; many-to-many extension §3.1.4, p. 439 |
| `Stable.pairwiseStable` | Theorem 3.1, first bullet, p. 440; many-to-one version: Theorem 2.1, first bullet, p. 417 |
| `PairwiseStable.stable_of_substitutable`; stability equivalence | Theorem 3.1, second bullet, p. 440; many-to-one version: Theorem 2.1, second bullet, p. 417 |
| `SellerChosen`, `BuyerChosen` | §2.3.1, unnumbered definitions, p. 420 |
| `toSellers`, `toBuyers`, `daFun` | §2.3.1.1, displayed generalized deferred acceptance operator, p. 421 |
| `stateOf`, `outcomeOf`, fixed-point/stability correspondence and `stableEquivFixedPoints` | Lemma 2.1, p. 424, proof pp. 422–424; many-to-many extension discussed in §3.2, p. 440 |
| `exists_stable`, `StableOutcomes`, and optimal/pessimal endpoints | Theorem 3.2, p. 440; many-to-one version: Theorem 2.2, p. 420, proof pp. 421–425 |
| `FixedPointStates`, monotonicity and extremal fixed points | Tarski's fixed-point theorem in §2.2, p. 419; application on p. 425 |
| Finite top/bottom iteration | Observation 1, pp. 419–420; matching application on p. 425 |
| `ruralHospitals` and buyer/seller cardinality corollaries | §3.2 and Theorem 3.3, p. 440, subject to the printed-wording caveat below; many-to-one version: Theorem 2.3, p. 426 |

Theorem 3.1 is the appropriate many-to-many citation. Its equivalence is proved
in Lean without IRC or finiteness; the third bullet of Theorem 2.1, about the
core, is not part of that formalization. Lemma 2.1 is numbered only in the
many-to-one section; §3.2 extends the argument without assigning another lemma
number. Footnote 24, p. 421, attributes the particular operator displayed there
to Azevedo and Hatfield (2018).

The raw fixed-point lattice requires substitutability alone. Its stable-outcome
interpretation and the full correspondence use substitutability and set-form
IRC, without finiteness. Individual lemmas can need less:
`outcomeOf_stateOf_of_stable` needs neither, and `indRational_outcomeOf`
needs IRC but not substitutability. No aggregate-demand assumption is needed
for the lattice or stable existence. Nor does the lattice statement say that
ambient unions and intersections of fixed points are always fixed points.
In the survey's terminology, Lean's `p ≤ q` means that `q` is seller-superior
to `p`.

The public `ruralHospitals` theorem assumes a finite contract type,
substitutability and aggregate demand; it derives consistency. It asserts
invariance of each agent's contract count, not equality of partner sets.
The stronger intermediate counting lemma only requires the compared outcomes
to be finite, but is not an unrestricted infinite-market rural hospitals
theorem. These results concern two-sided bilateral contracts, not the chapter's
later general trading networks.

**Published wording caveat.** Theorem 3.3 on p. 440 begins “Under many-to-one
matching with contracts,” although it is in §3.2 and the immediately preceding
paragraph explicitly generalizes the result to many-to-many. This wording was
visually checked in the published PDF and appears to be a typographical
carry-over. Cite §3.2 together with Theorem 3.3 and retain this caveat until
checked against the original published article; do not silently change the
printed hypothesis.

### Replacing the earlier completion reference

The published survey's §6.1, Definition 6.1 and Example 6.1 now provide the
checked references for the completion definitions and example formerly mapped
to the May 2016 *Hidden Substitutes* manuscript. The survey's bibliography
(p. 482) lists *Hidden Substitutes* as a 2020 working paper. Its published
EC 2015 extended abstract is not being treated as a verified replacement for
the detailed manuscript. No additional version of that manuscript is needed
for the definition and example checks above.

## Hatfield–Kojima (2010): HK2010

John William Hatfield and Fuhito Kojima, *Substitutes and stability for matching
with contracts*, Journal of Economic Theory **145** (2010), 1704–1723.
[Published article](https://doi.org/10.1016/j.jet.2010.01.007) ·
[Published article PDF](https://kylewoodward.com/blog-data/pdfs/references/hatfield%2Bkojima-journal-of-economic-theory-2010A.pdf).

| Declaration | Checked published locator |
| --- | --- |
| `Substitutable.not_mem_insert_insert` | Definition 2, p. 1708 |
| `BilaterallySubstitutable` | Definition 3, p. 1709 |
| `UnilaterallySubstitutable` | Definition 5, p. 1715 |
| `SizeMonotone`, on finite types | Definition 7, p. 1718 |

The paper's rejected contract `z` is Lean's `x`; its added contract `x` is
Lean's `z`. The weak predicates match under this renaming, without a
distinct-counterparties assumption.

Finiteness alone does not give the larger-menu unilateral implication for
abstract choice functions. The Lean bridge uses IRC, counterparty feasibility
and finite-valuedness. Footnote 17, p. 1715, concerns the paper's finite,
preference-induced model.

## Litvakov (1985): published upper-approximation formula

B. M. Litvakov, *Approximation of choice functions with a bounded set of
presentations*, Avtomatika i Telemekhanika (1985), no. 2, 124–129
(Russian original); English translation, Automation and Remote Control **46**
(1985), 248–252.
[Publication record](https://www.mathnet.ru/eng/at6893) ·
[Published Russian original](https://www.mathnet.ru/php/getFT.phtml?jrnid=at&paperid=6893&what=fullt).

Theorem 5, table row H, printed p. 127 of the Russian original, gives the upper
approximation as the union of `C(Z)` over available `Z ⊇ Y`, intersected with
`Y`. Taking the menu domain to be the full powerset gives exactly
`substituteHull C Y = {x ∈ Y | ∃ Z ⊇ Y, x ∈ C Z}`.
The locator belongs to the Russian original; English pagination has not been
checked. This verifies the formula attribution, not every historical
infinite-domain claim or Lean's separate IRC/completion theorems.

## Published articles still needed for exact locator checks

| Published reference | What remains to check |
| --- | --- |
| John William Hatfield and Scott Duke Kominers, *Contract design and stability in many-to-many matching*, Games and Economic Behavior **101** (2017), 78–97. [DOI](https://doi.org/10.1016/j.geb.2016.01.002) | Highest priority: published definition/proposition/lemma numbers for stability, the fixed-point correspondence and the lattice, and the original rural hospitals statement. Earlier source comments use the February 2016 manuscript key `HKContractDesign2016`; its page and theorem numbers have not been transferred to the published article. |
| Jun Zhang, *On sufficient conditions for the existence of stable matchings with contracts*, Economics Letters **145** (2016), 230–234. [DOI](https://doi.org/10.1016/j.econlet.2016.06.029) | Check the published Lemma 2, Proposition 2 and §5 against the unilateral-to-completion and repair citations. The survey verifies the broad attribution, not those individual locators. |
| Bernard Monjardet and Vololonirina Raderanirina, *Lattices of choice functions and consensus problems*, Social Choice and Welfare **23** (2004), 349–382. [DOI](https://doi.org/10.1007/s00355-003-0251-9) | Lower priority: check the precise choice-lattice/closure discussion behind the existing background citation. No numbered theorem from this paper is presently claimed in the source. |

Published full text is already available for HK2010, the 2025 survey and
Litvakov's Russian original. The English translation of Litvakov is optional
if an English-page locator is preferred. Published metadata has been checked
for the three articles in the table, but their published full-text locators
remain pending. Earlier manuscript locators are not presented as published
ones.

## Other published background references

The following works are cited by name in the choice layer. These entries fix
published bibliographic identities; they do not claim a new audit of numbered
statements or require additional PDFs for the citation corrections above.

| Reference | Published version |
| --- | --- |
| M. A. Aizerman and A. V. Malishevski (1981), *General theory of best variants choice: Some aspects* | IEEE Transactions on Automatic Control **26**(5), 1030–1040. [DOI](https://doi.org/10.1109/TAC.1981.1102777) |
| Christopher P. Chambers and M. Bumin Yenmez (2017), *Choice and Matching* | American Economic Journal: Microeconomics **9**(3), 126–147. [DOI](https://doi.org/10.1257/mic.20150236) |
| Charles R. Plott (1973), *Path Independence, Rationality, and Social Choice* | Econometrica **41**(6), 1075–1091. [DOI](https://doi.org/10.2307/1914037) |
| Orhan Aygün and Tayfun Sönmez (2013), *Matching with Contracts: Comment* | American Economic Review **103**(5), 2050–2051. [DOI](https://doi.org/10.1257/aer.103.5.2050) |
| Ahmet Alkan and David Gale (2003), *Stable schedule matching under revealed preference* | Journal of Economic Theory **112**(2), 289–306. [DOI](https://doi.org/10.1016/S0022-0531(03)00096-6) |

Plott's article is in issue 6; the survey bibliography's issue 1 is incorrect.
The Aizerman–Malishevski volume, issue and pages were cross-checked against the
published chapter and bibliographic references; the complete IEEE metadata
page was inaccessible. These background entries are distinct from the
full-text statement checks above.
