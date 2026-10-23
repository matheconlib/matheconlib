> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Matching contracts: many-to-one restrictions and completion transfer

Scope: `MathEconLib/Matching/Contracts/ManyToOne.lean`,
`WeakSubstitutes.lean`, and `Completion.lean`.

## Definition coverage

| Definition | Source | Intended concept and equivalence assessment |
| --- | --- | --- |
| `SellersUnitDemand` | `ManyToOne.lean:42` | Every seller selects at most one contract from every menu. Exact pointwise specialization of `ChoiceFunction.UnitDemand`; it asserts a cardinality restriction, with rationality/IRC separate. Both directions follow by unfolding. |
| `BuyersCounterpartyFeasible` | `ManyToOne.lean:46–47` | Every hospital's chosen bundle contains at most one contract with each doctor. Injectivity of the seller map on that bundle is exactly this restriction in both directions. No buyer quota is asserted. |
| `ManyToOneFeasible` | `ManyToOne.lean:50` | An allocation gives each doctor at most one contract. `Set.InjOn seller A` says any two contracts in `A` with the same seller coincide; this is equivalent to every seller fiber having cardinality at most one, without a finiteness requirement. |
| `ofSellerPreferences` | `ManyToOne.lean:76–89` | Doctors maximize a strict order on own contracts plus unemployment, with higher alternatives better. Restricting to a seller's subtype and mapping back selects exactly that doctor's best acceptable contract whenever it exists; otherwise the result is empty. This matches the stated constructor, including its documented infinite-menu convention at 74–75. |
| `BuyersUnilaterallySubstitutable` | `WeakSubstitutes.lean:60–61` | Hospital unilateral substitutes with freshness measured by the doctor map. Exactly the choice-level condition for every buyer, with the sides correctly assigned. |
| `BuyersBilaterallySubstitutable` | `WeakSubstitutes.lean:65–66` | Hospital bilateral substitutes with the same doctor convention. Exact universal specialization. Neither source condition requires the two newly considered contracts to involve distinct doctors. |
| `BuyersSubstitutablyCompletable` | `WeakSubstitutes.lean:72–73` | Every hospital admits a substitutable completion. Exact specialization of the bare completion formula; IRC is deliberately excluded and the difference from the cited source's standing IRC assumption is explicit at 68–71. |
| `BuyersHaveConsistentSubstitutableCompletions` | `WeakSubstitutes.lean:77–78` | Every buyer admits one completion jointly satisfying substitutes and IRC. Correct quantifier order: the same witness satisfies both conditions. |
| `withBuyerCompletions` | `Completion.lean:63–72` | Substitute completed buyer choices for original choices, retain seller choices and contract endpoints. The constructor does exactly that. Buyer support follows from singleton agreement of completions and substitutability; no unproved support assumption is smuggled in. |

## Primary-source comparison

Hatfield–Kojima (2010), Definition 3 (p. 1709) and Definition 5 (p. 1715),
use exactly the bilateral/unilateral freshness tests delegated to by these wrappers.
The seller/doctor and buyer/hospital translation is correct. Their allocation
definition (p. 1707) also agrees with `ManyToOneFeasible`.

Source: [published article PDF](https://kylewoodward.com/blog-data/pdfs/references/hatfield%2Bkojima-journal-of-economic-theory-2010A.pdf).

Zhang (2016), Definition 6, supplies the same completion formula as the imported
`Choice.Matching.Completion`: a completed choice either agrees with the original
or selects two distinct contracts involving the same worker. In particular,
pointwise inclusion of original choices is not part of that formula.

Source: [publisher page and definition excerpt](https://www.sciencedirect.com/science/article/abs/pii/S0165176516302336).

## Counterexample search and rejected concerns

No substantive defect established in this scope.

* An arbitrary at-most-one selection rule need not maximize a preference order.
  This is not a false positive for `SellersUnitDemand`, which expressly records
  only the cardinality restriction and exposes IRC separately.
* On an infinite menu with no best acceptable contract, the preference constructor
  rejects all contracts. Example: one seller, contracts indexed by natural
  numbers, unemployment below every contract, and larger indices preferred.
  Every contract has a preferred available successor, so the maximal-contract
  comprehension is empty. This is a documented extension convention, and IRC
  is proved only under finiteness; it is not an unqualified claim of rational
  maximization on arbitrary infinite menus.
* A completion need not pointwise enlarge the original choices. The existence
  and transfer arguments do not impose or use that incorrect extra requirement.

## Transfer theorem check

`stable_of_withBuyerCompletions` (`Completion.lean:92–134`) keeps both original
IRC and IRC of the same substitutable completion explicit. A completed stable
outcome is seller-feasible by unit demand, so completion agreement transfers
individual rationality. On the menu of contracts sellers would individually
accept, completed buyer choice is exactly the outcome: an additional chosen
contract would form a singleton block by substitutes, and IRC preserves the
existing outcome. Its feasibility forces original/completed agreement there.
Original IRC then excludes any original blocking set. This argument supports
the one-way transfer stated, without an unsupported claim that stable sets
coincide.

## Four-pass record

1. **Concept extraction and source comparison:** inventoried all nine
   definitions and identified the economic concept each represents. Checked
   the primary-source bilateral/unilateral formulas and doctor feasibility.
2. **False-positive search:** tested whether cardinality restrictions secretly
   assert rationality, whether hospital/doctor sides were reversed, whether
   arbitrary completed choices can violate support, and whether the completion
   transfer wrongly assumes enlargement. None is a defect under the stated
   definitions and hypotheses.
3. **False-negative and boundary search:** checked empty menus/types, multiple
   contracts for one doctor, buyers with arbitrary capacities, rejected
   contracts, outside-option placement, and infinite menus without a maximum.
   The only limiting behavior identified is the explicitly documented
   infinite-menu fallback. Strict orders accurately match the stated strict
   preference concept; no claim to represent indifference is made.
4. **Independent verification:** a separate hostile reviewer independently
   checked `ManyToOne.lean` and the completion transfer proof and reached the
   same no-defect result. That reviewer also exhaustively enumerated 4,096
   contracting choice maps on three contracts, identifying 246 IRC originals
   and 35 IRC/substitutable completions; tests across seller partitions,
   strict unit-demand IRC seller profiles, and outcomes passed 63,856
   completion-transfer cases for one buyer and the three canonical seller
   partition shapes `(0,0,0)`, `(0,0,1)`, and `(0,1,2)`. Reproduce with
   `python3 docs/audits/2026-10-23-semantic/areas/contracts/verify_completion_transfer.py`.
   The script was independently inspected for correspondence with the formal
   contraction, IRC, substitutes, completion, individual-rationality, and
   blocking formulas. This bounded computation supports only its exact finite
   encoding; the general transfer conclusion rests separately on the proof
   audit above.
