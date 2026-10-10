# References for matching with contracts

This map records the primary-source comparisons completed for PR #103 on
10 October 2026. Page numbers are printed page numbers. Choice declarations
belong to `MathEconLib.Choice.ChoiceFunction`; market declarations belong to
`MathEconLib.Matching.Market`. Names below omit these prefixes where clear.

## Hatfield–Kojima (2010): HK2010

John William Hatfield and Fuhito Kojima, *Substitutes and stability for matching
with contracts*, Journal of Economic Theory **145** (2010), 1704–1723.
[DOI](https://doi.org/10.1016/j.jet.2010.01.007) ·
[Published article PDF](https://kylewoodward.com/blog-data/pdfs/references/hatfield%2Bkojima-journal-of-economic-theory-2010A.pdf).

| Declaration | Checked locator |
| --- | --- |
| `Substitutable.not_mem_insert_insert` | Definition 2, p. 1708 |
| `BilaterallySubstitutable` | Definition 3, p. 1709 |
| `UnilaterallySubstitutable` | Definition 5, p. 1715 |
| `SizeMonotone`, on finite types | Definition 7, p. 1718 |

The paper's rejected contract `z` is Lean's `x`; its added contract `x` is
Lean's `z`. The weak predicates match under this renaming, without a
distinct-counterparties assumption.

Lean's `Substitutable` quantifies over arbitrary supersets. Its equivalence
with the single-addition condition is proved on finite types. The weak
predicates retain single-addition quantification on arbitrary types.
Finiteness alone does not give the larger-menu unilateral implication for
abstract choice functions: the Lean bridge uses IRC, counterparty feasibility,
and finite-valuedness. Footnote 17, p. 1715, concerns the paper's finite,
preference-induced model. `SizeMonotone` imposes cardinality comparisons only
on finite menus.

## Hatfield–Kominers: Hidden Substitutes

John William Hatfield and Scott Duke Kominers, *Hidden Substitutes*, author
manuscript dated **May 16, 2016**.
[Author PDF](https://www.scottkom.com/assets/articles/Hatfield_Kominers_Hidden_Substitutes.pdf).

| Declaration or example | Checked locator |
| --- | --- |
| `IsCompletionOf` | §3, unnumbered definition, pp. 8–9 |
| `SubstitutablyCompletable` | §3, p. 10 |
| `HasConsistentSubstitutableCompletion`, as an existence hypothesis | Theorem 1, p. 11 |
| `MathEconLibTest/Choice/CompletionCounterexamples.lean` | §1, p. 2; §3, p. 9, equation (1) |

The manuscript starts with many-to-one original choices; Lean exposes the
completion formula for arbitrary choice functions. Neither completion nor
substitutable completability includes IRC. The stronger predicate requires
one completion satisfying both properties. A completion need not enlarge
choices pointwise; results using enlargement state it separately.

## Hatfield–Kominers: HKContractDesign2016

John William Hatfield and Scott Duke Kominers, *Contract Design and Stability
in Many-to-Many Matching*, author manuscript dated **February 11, 2016**.
[Author PDF](https://scottkom.com/assets/articles/Hatfield_Kominers_Contract_Design.pdf).
The journal article appeared in Games and Economic Behavior **101** (2017),
78–97. All locators here refer to the dated manuscript.

| Declaration or construction | Checked locator |
| --- | --- |
| `IndRational`, `Blocks`, `Stable`, `PairwiseStable` | Definition 2 and discussion, pp. 4–5 |
| `Stable.pairwiseStable`, `PairwiseStable.stable_of_substitutable` | Proposition 2, p. 5 |
| `daFun`; correspondence through `stateOf` and `outcomeOf` | §4, Lemma 1, p. 11 |
| `exists_stable`; stable-outcome lattice in `Contracts/Order.lean` | §4, Theorem 1, p. 11 |

The acceptance-from-an-added-contract operator agrees with the construction
in §4, mapping doctors to sellers and hospitals to buyers. The Lean results
extend the setting to arbitrary contract types and expose IRC separately;
footnote 8, p. 4, discusses IRC for primitive choice functions. Stability
equivalence needs neither IRC nor finiteness in Lean. The fixed-point
correspondence and stable-outcome existence use substitutability and IRC.

## The 2025 survey: scope of verification

Hatfield–Kominers, *The theory of matching with contracts*, Handbook of the
Economics of Matching **2** (2025), Chapter 5, 409–487,
[DOI](https://doi.org/10.1016/bs.hesmat.2025.10.005).
The [SSRN entry](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=5369037)
identifies a separate 118-page manuscript dated **July 14, 2025**.

Bibliographic identity was checked. Exact definition and theorem numbering
remains **unverified**: publisher and SSRN full-text retrieval returned HTTP
403. The source comments use the checked references above in place of the
previous paired theorem numbers `2.1(ii)/3.1` and `2.2/3.2` and numbered
survey definitions. The survey remains a background reference; no
cross-edition numbering equivalence is asserted.

This map covers the citations specifically checked for the review. It does
not certify every historical reference in the development, including the
citations to Litvakov, Monjardet–Raderanirina, or Zhang.
