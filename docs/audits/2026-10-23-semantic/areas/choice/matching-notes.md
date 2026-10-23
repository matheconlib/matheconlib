> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Choice/Matching semantic audit

Scope: `MathEconLib/Choice/Matching/{Preferences,WeakSubstitutability,Completion,Relationships}.lean`.
Audit date: 2026-10-23. Read-only review of library source; supporting finite check is in `matching/finite_check.py`.

## Outcome

No confirmed semantic defect in the nine definitions below. Both false-positive and false-negative directions were checked by unfolding the predicates, comparing the declared domains and checking the explicitly documented extensions beyond the finite economic models.

| Definition and source lines | Intended concept | Assessment |
| --- | --- | --- |
| `Fresh`, WeakSubstitutability.lean:49–50 | The counterparty of contract `x` does not occur among contracts in baseline menu `Y` | Exact: `∀ y ∈ Y, p(y) ≠ p(x)` iff `p(x) ∉ p '' Y`. No injectivity, finiteness or market assumption needed. |
| `UnilaterallySubstitutable`, WeakSubstitutability.lean:55–57 | Hatfield–Kojima single-addition unilateral substitutability | Exact under the paper-to-Lean renaming of rejected `z` to Lean `x` and added `x` to Lean `z`. Only the rejected contract's counterparty must be absent from the baseline menu. |
| `BilaterallySubstitutable`, WeakSubstitutability.lean:63–66 | Hatfield–Kojima single-addition bilateral substitutability | Exact: both counterparties must be absent from the baseline menu; the two counterparties need not be distinct. |
| `IsCompletionOf`, Completion.lean:53–55 | Completion of a many-to-one choice rule | Exact displayed completion formula: each completed choice either equals the original choice or contains distinct contracts with a common counterparty. The receiver is the original choice, with the completion passed last; this orientation is documented. Pointwise enlargement is not part of this concept. Source admits arbitrary original choices as an explicitly stated extension of the economic domain. |
| `SubstitutablyCompletable`, Completion.lean:62–63 | Existence of a substitutable completion | Exact bare formula. It intentionally does not include the survey's standing IRC convention; both module and declaration docstrings say this explicitly. |
| `HasConsistentSubstitutableCompletion`, Completion.lean:69–71 | Existence of one completion that is both substitutable and IRC | Exact existential conjunction with the same witness, avoiding the weaker and inappropriate separate-witness condition. Original-rule IRC is a separate assumption in results that need it. |
| `FeasibleBundle`, Preferences.lean:84–85 | Bundle with at most one contract per counterparty | Exact: injectivity of `counterparty` restricted to the bundle is equivalent to the pairwise condition. Includes the empty set and makes no unstated finiteness or quota restriction. |
| `feasibleBundleEmbedding`, Preferences.lean:88–93 | Inclusion of feasible bundles into all sets of contracts | Exact underlying-set embedding; subtype proof irrelevance creates no extra mathematical bundle distinctions. |
| `ofFeasibleBundleOrder`, Preferences.lean:100–104 | Choose the greatest available counterparty-feasible bundle under a linear preference | Exact specialization of `ofBundleOrder`. Availability is containment in the menu. On finite menus a greatest bundle exists because the empty bundle is available. On arbitrary infinite menus, the empty fallback when no greatest exists is explicitly part of the API, not a claim of attained preference maximization. Indifference is excluded intentionally by the linear-order input. |

`Relationships.lean` introduces no definitions. Its main equivalences explicitly assume IRC, feasibility and finite-valuedness; the completion converse additionally uses pointwise enlargement. The proofs were read for their economic interpretation, in particular to ensure they do not silently identify ordinary completion with enlargement. No such identification occurs.

## Independent source check

An independent reviewer checked the published Hatfield–Kojima article: [Substitutes and stability for matching with contracts](https://kylewoodward.com/blog-data/pdfs/references/hatfield%2Bkojima-journal-of-economic-theory-2010A.pdf), Definitions 3 and 5, printed pp. 1709 and 1715. The predicates match literally after the above variable renaming. Neither source formula requires distinct counterparties. The paper assumes finite contracts and preference-induced feasible choices (§2, p. 1707); the library correctly does not infer the paper's larger-menu equivalence on arbitrary abstract choices from finiteness alone.

An independent reviewer also visually checked the published Zhang (2016), Definition 6, printed p. 232, [On sufficient conditions for the existence of stable matchings with contracts](https://doi.org/10.1016/j.econlet.2016.06.029). The definition exactly matches `IsCompletionOf` and `SubstitutablyCompletable`; neither enlargement nor IRC is part of its formula. Its Table 1 explicitly supplies a completion that drops an original chosen contract, and the text immediately following Definition 6 treats completion IRC as an additional stable-existence hypothesis. The repository also maps the same formula to Hatfield–Kominers (2025), §6.1, p. 471, in `docs/MatchingReferences.md`; the current reviewer could not independently reopen that survey's full text because the publisher denied access. The definition/formula comparison is independently supported by the accessible published Zhang source; the survey-specific standing-IRC page locator remains a repository-recorded prior check.

## Independent computational cross-check

`python3 docs/audits/2026-10-23-semantic/areas/choice/matching/finite_check.py`

The script enumerates all 4,096 contracting choice functions on three labeled contracts, for all five equivalence partitions of the contracts into counterparties. The encoding assigns a submask to each menu; it directly implements the displayed set predicates. It checks:

- unilateral implies bilateral substitutability;
- substitute hull is substitutable and enlarges the original choices;
- original IRC implies hull IRC;
- hull counterparty-image preservation implies unilateral substitutability without additional assumptions;
- under IRC and counterparty feasibility, unilateral substitutability is equivalent both to hull image preservation and to the hull being a completion.

All checks pass. Counts of feasible IRC unilateral choice tables for the five counterparty partitions are 16, 28, 28, 28 and 35. These are checks of the exact finite encoding and are not offered as proofs of the general theorems.

## Rejected defect candidates

- Requiring `p(x) ≠ p(z)` in bilateral substitutability would add an unwarranted restriction and permit false positives relative to HK2010. The current definition correctly omits it.
- Requiring ordinary completions to enlarge all original choices would exclude legitimate completions. The library already formally checks the three-contract published example in `MathEconLibTest/Choice/CompletionCounterexamples.lean`.
- Removing finite-valuedness from the unilateral-to-completion result is not justified on infinite domains. The same test file records the identity-counterparty infinite-or-empty choice example; the theorem retains finite-valuedness.
- Empty choice on an infinite menu lacking a greatest bundle is a documented totalization of the constructor, not a hidden assumption that preferences attain their maximum.

No correction or newly reported counterexample is proposed for this scope.
