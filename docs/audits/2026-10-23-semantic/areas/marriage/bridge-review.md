> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Classical marriage: contracts bridge, extrema, stable order, lone wolf

Source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`.

Read-only source audit of:

- `MathEconLib/Matching/Classical/Marriage/ToContracts.lean` (717 lines).
- `MathEconLib/Matching/Classical/Marriage/Optimality.lean` (307 lines).
- `MathEconLib/Matching/Classical/Marriage/StableOrder.lean` (212 lines).
- `MathEconLib/Matching/Classical/Marriage/LoneWolf.lean` (107 lines).
- `MathEconLib/Matching/Classical/Marriage/Existence.lean` (39 lines).

Dependencies inspected where their interpretation matters: `Marriage/Preferences.lean`,
`Marriage/Basic.lean`, `ForMathlib/Data/PartialMatching.lean`, `Contracts/Basic.lean`,
and the carrier/order dictionary in `Contracts/StableOrder.lean`. General contracts
theorems also receive a separate audit by their owning workstream.

**Verdict: no reportable semantic defect found in this assignment.** Both false-positive
and false-negative directions were checked. There is no suspected counterexample
being advanced as a defect, so no proposed source correction is necessary.

## Intended concepts and assumptions

The classical concept is one-to-one, two-sided matching under strict preferences,
with an outside option and possibly unequal or empty populations. Optimality means
that every member of the specified side weakly prefers the selected stable matching
to every other stable matching, the original universal optimum criterion in
[Gale and Shapley (1962), pp. 10–12](https://iqua.ece.toronto.edu/baochun/ece1771f/papers/Gale-Shapley-1962.pdf).
The unmatched-set invariance is the one-to-one specialization of the rural-hospitals
property in [Roth (1986)](https://nickarnosti.com/IE5080/Session5/Roth_1986.pdf).

`MarriageMarket.prefM/prefW` supply `LinearOrder (Option partner)`
(`Preferences.lean:39–43`). Hence distinct partners cannot tie with each other
or with `none`; larger is preferred, and `none` need not be worst.
The audit does not interpret the definitions as covering weak preferences with ties.
Optimal matching constructions and the complete lattice have finite population
instances (`Optimality.lean:28`, `StableOrder.lean:64`). `Existence` and `LoneWolf`
require `[Finite M] [Finite W]`. Unrestricted definitions do not promise finite-market
conclusions on infinite markets.

## Definition inventory and both-direction assessment

All 15 definition/structure declarations in the assigned inventory are included
below; the anonymous complete-lattice instance, omitted by the simple inventory
scanner, is also reviewed. Paths in this table are relative to
`MathEconLib/Matching/Classical/Marriage/`.

| Declaration, exact source location | Standard concept | Formal ↔ intended assessment |
|---|---|---|
| `toContractsMarket`, `ToContracts.lean:39–45` | Encode each potential man–woman partnership as a contract; women buy, men sell | Exactly `X = M × W`, buyer `snd`, seller `fst`, own-partner choice on each side. No extra contract terms, omitted pair, or reversed economic side. Locality is established at lines 61–84. |
| `partnerMOf`, `ToContracts.lean:367–369` | Extract an optional partner from a relation's row | `relationValue` returns none exactly for an empty row and otherwise selects a row member. On subsingleton rows, it returns `some w` exactly when `(m,w) ∈ A` (lines 378–382). On arbitrary multivalued inputs it is an arbitrary selector, which is explicit in the underlying helper and is not used to claim uniqueness. |
| `partnerWOf`, `ToContracts.lean:373–375` | Same extraction for a relation's column | Same argument, with column uniqueness required by lines 385–389. Both row and column correctness directions are guarded. |
| `matchingOfIndRational`, `ToContracts.lean:393–396` | Recover the unique one-to-one matching from an IR unit-demand contract outcome | IR forces each row and column to be a subsingleton (lines 335–362); `PEquiv.ofRelation` therefore gives precisely the relation. The graph identity at lines 404–407 proves both inclusion directions and prevents an omitted or added partnership. |
| `matchingOfStable`, `ToContracts.lean:399–401` | Recover a stable classical matching from a stable contracts outcome | Applies the previous operation to stability's IR component. Exact graph recovery is lines 410–413; classical stability is lines 415–420; reconstructing a stable matching's graph recovers that matching at lines 422–426. |
| `manOptimalMatching`, `Optimality.lean:45–49` | Unique man-optimal stable matching | Seller optimum transported through the exact graph bridge. Stability at lines 60–65 and all-men weak preference against every stable matching at lines 67–79 establish intended membership. Conversely every intrinsically man-optimal matching equals it at lines 246–251. |
| `womanOptimalMatching`, `Optimality.lean:96–99` | Unique woman-optimal stable matching | Symmetric reasoning; stability and pointwise optimality at lines 107–121, exact converse/characterization at lines 253–258. |
| `manPessimalMatching`, `Optimality.lean:191–192` | Stable matching worst for every man among stable matchings | Chosen from the independent universal `IsManPessimal` specification, not defined by cross-side name alone. Membership at lines 198–200, exact converse at lines 260–265. Coincidence with woman optimum is proved at lines 222–226. |
| `womanPessimalMatching`, `Optimality.lean:195–196` | Stable matching worst for every woman among stable matchings | Membership at lines 202–204, exact converse at lines 267–272. Coincidence with man optimum is proved at lines 228–232. |
| `StableMatching`, `StableOrder.lean:32–34` | Stable matchings as a carrier | Contains exactly a `PEquiv` and its stability proof; it imposes no extra preference or completeness restriction. Extensionality at lines 40–45 removes apparent multiplicity from proof packaging. |
| `StableMatching.symmEquiv`, `StableOrder.lean:48–59` | Exchange the market sides | Maps to inverse partial matching and uses the exact stability symmetry; involution supplies both carrier directions. No finiteness assumption here. |
| `StableMatching.graphEquiv`, `StableOrder.lean:67–75` | Stable classical matchings ↔ stable contract graphs | Forward stability is the graph dictionary; inverse is `matchingOfStable`. Both inverse identities are explicit, ruling out extra or missing outcomes. Finite population instances precede this declaration. |
| `StableMatching.fixedPointEquiv`, `StableOrder.lean:79–85` | Stable classical matchings ↔ canonical stable fixed points | Composition of the preceding equivalence with `stableEquivFixedPoints`. It is a bijection, not just a map from stable matchings to an auxiliary state set. |
| `StableMatching` complete-lattice instance, `StableOrder.lean:88–110` | Lattice of stable matchings ordered by unanimous men's improvement | Transports a genuine fixed-point lattice through a carrier equivalence. The economic order is exactly men's weak preference with the arguments reversed (lines 129–135), equivalently women's weak preference with the arguments unreversed (lines 138–144). Its supremum is a supremum in the fixed-point lattice, not an unjustified ambient union. |
| `StableMatching.fixedPointOrderIso`, `StableOrder.lean:113–118` | Identification with the fixed-point lattice preserving order | Uses the same carrier equivalence and the transported order; the relation iff is definitionally exact. The economic interpretation is separately proved at lines 129–144, so transport does not silently change the intended order. |
| `StableMatching.symmOrderIso`, `StableOrder.lean:175–188` | Exchange sides and reverse stable-matching order | Correctly targets `(mkt.symm.StableMatching)ᵒᵈ`. The two directions follow from the men/women preference dictionaries; no orientation mismatch. |

## Bridge equivalences checked analytically

1. **IR in both directions.** A partial matching's graph contains at most one own
   contract per agent. Choosing that entire singleton is equivalent to preferring
   that partner to `none`; choosing the empty side corresponds to being unmatched.
   This gives `individuallyRational_iff_indRational_graphOf`
   (`ToContracts.lean:202–206`). The forward theorem currently assumes finite
   populations; the reverse theorem at lines 162–200 does not. Neither claims an
   unqualified equivalence for unrestricted infinite contract outcomes.
2. **Blocking in both directions.** Against an IR graph, accepting a new pair
   from its insertion means strictly preferring the new partner to the current
   assignment: weak maximum plus distinctness becomes strict under the linear
   order. Conversely a strict improvement over an IR assignment is acceptable
   relative to `none` and best in that two-partner menu. This is established
   separately for men/women at lines 213–276. Thus the singleton-blocking
   equivalence (lines 279–307) has precisely the right hypotheses. The induced
   choices are substitutable, so blocking by any contract set reduces to singleton
   blocking. `isStableMatching_iff_stable_graphOf` (lines 311–330) follows without
   conflating pairwise with arbitrary blocking on an unrestricted choice domain.
3. **Preference versus choice in both directions.** For graphs of `μ,ν`, a man's
   own union menu contains at most the two assignments plus the ever-available
   outside option. He chooses precisely `μ`'s side iff `μ` is IR for him and he
   weakly prefers `μ` to `ν`. Hence the exact dictionary is
   `SellerChosen graph(μ) graph(ν) ↔ IR_M(μ) ∧ MenWeaklyPrefer μ ν`
   (lines 651–656). The buyer dictionary is the symmetric formula
   (lines 660–665). IR of `ν` is unnecessary and is not required by the strongest
   dictionaries; the retained compatibility wrappers may carry it harmlessly.
4. **Order, extrema, and bounds.** `μ ≤ ν` means men weakly prefer `ν` to `μ`,
   so top is man optimum/woman pessimum and bottom is woman optimum/man pessimum
   (`StableOrder.lean:147–172`). The join and meet economic universal properties
   at lines 191–206 follow with the correct argument order. Optimality's comparison
   domain is every stable matching, rather than every arbitrary matching or merely
   a Pareto maximal stable matching.

## Theorem-only files

`Existence.lean` contains no definition declaration. `exists_stableMatching`
(`29–35`) transfers a stable contracts outcome through the exact reconstruction;
its intended conclusion is stable partial matching existence for finite strict
markets, including unequal and empty populations. Its statement matches that
conclusion.

`LoneWolf.lean` contains no definition declaration. The six graph-fiber interfaces
(`sellerSide_graphOf_eq_empty`, `sellerSide_graphOf_eq_singleton`,
`ncard_sellerSide_graphOf_eq_zero_iff`, `buyerSide_graphOf_eq_empty`,
`buyerSide_graphOf_eq_singleton`, `ncard_buyerSide_graphOf_eq_zero_iff`, lines 33–67)
are the empty/singleton fiber identities for a partial bijection. In particular,
the cardinal-zero tests never misclassify an infinite fiber: these graph fibers
are always empty or singletons. `eq_none_iff_of_stable` (`70–79`) compares two
stable matchings in the same finite market and states precisely invariance of
unmatched men. `isSome_iff_of_stable` (`83–87`) is its equivalent matched form;
`eq_none_symm_iff_of_stable` (`90–95`) and `isSome_symm_iff_of_stable` (`98–103`)
are the corresponding statements for women. None claims invariance of an
individual's actual partner.

## Adversarial alarms rejected

- **Missing IR in the choice/preference dictionary:** the minimal attempted
  counterexample is one man, one woman, with the man ranking `none > w` and
  `μ = ν = {(m,w)}`. `MenWeaklyPrefer μ μ` is true while his choice from the
  union is empty, so `SellerChosen graph(μ) graph(μ)` is false. This would refute
  an unconditional iff, but the actual iff at lines 651–656 includes `IR_M μ`,
  which is false. The alleged defect is already excluded explicitly.
- **Multivalued contract outcomes reconstructed as marriage matchings:** with one
  man and two women, `A = {(m,w₀),(m,w₁)}` is not IR: the man's strict unit-demand
  choice cannot equal that two-element row. Reconstruction requires IR and its
  injectivity obligations are proved. There is no admitted false positive.
- **Infinite menus without a best partner:** optional-order choice can be empty
  there, but the preference module explicitly documents this at lines 18–22.
  The contracts IRC theorem (`ToContracts.lean:86`) and stable existence/order
  constructions retain finite population hypotheses. No finite-theorem promise
  is being improperly extended.
- **Reversed economic order or cross-side extrema:** tested with the smallest
  two-stable-matching instance: men rank `w₀>w₁>none`, `w₁>w₀>none`; women rank
  `m₁>m₀>none`, `m₀>m₁>none`. The straight matching is man-optimal and the crossed
  matching woman-optimal; the crossed matching is below the straight one. This
  agrees with all stated order and extremum conventions.
- **Vacuous optimum outside the stable set / duplicate fixed-point representatives:**
  each intrinsic optimum specification contains stability, and both carrier
  equivalences prove both inverse identities. Neither alarm survives unfolding.

## Independent evidence and four-pass status

Pass 1 inventoried all assigned definitions and extracted domains/hypotheses.
Pass 2 reread definitions against IR, blocking, one-to-one feasibility, universal
side optimality, economic order, and unmatched-set invariance. Pass 3 tried the
hostile examples above and delegated an independent analytic order/extrema review
to `/root/audit_marriage/bridge_review/order_hostile`. That reviewer independently
found no candidate defect and checked the underlying fixed-point carrier/order
dictionary. Pass 4 reconciled the inventory, exact lines, rejected alarms, and
finite evidence; that same independent reviewer inspected and reran the checker.

Reproducible finite check:

```sh
python3 docs/audits/2026-10-23-semantic/areas/marriage/bridge-enumeration.py
```

Do not use Python `-O`, which disables its assertions. Output is retained in
`bridge-enumeration.json`. The exact enumeration covers every strict profile with
`0 ≤ |M|,|W| ≤ 2`, including every position of `none`: 1,353 markets, 20,941
contract-outcome instances, 63,957 ordered matching comparisons, 1,359 ordered
stable pairs, and 1,367 stable triples. It checks both IR/stability bridge
directions, IR-outcome feasibility, singleton blocking, exact side-choice
dictionaries, side opposition, nonempty stable sets, unique opposite extrema,
join/meet universal properties, and invariance of unmatched agents. All passed.

This is independent integer/set evidence for those exact finite instances. It
does not execute Lean, test the actual fixed-point representative construction,
or establish a general theorem from bounded computation. No Lean compilation
claim is made by this workstream; no suspected defect required a Lean witness.
