> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Contracts: stable order, rural hospitals, finite convergence

Audited source: `MathEconLib/Matching/Contracts/StableOrder.lean`, `RuralHospitals.lean`, `FixedPointConvergence.lean`. Supporting definitions in `Basic.lean` and `StableFixedPoints.lean` were read to interpret the interface; their primary audits belong to the parent workstream. No source changes were made.

Verdict: no confirmed semantic defect in this assigned scope. Both representational directions were checked, not merely internal theorem truth. There is no counterexample to report from this scope.

## Major definition dictionary

| Location in StableOrder.lean | Formal definition | Standard intended concept and bidirectional assessment |
|---|---|---|
| 319–320 | `Market.FixedPointStates` | Knaster–Tarski fixed-point complete lattice of the generalized deferred-acceptance monotone operator on seller offers ordered by inclusion and buyer offers ordered by reverse inclusion. Exact fixed-point subtype; no IRC is claimed at this raw interface. |
| 326–328 | `Market.StableOutcomes` | Fixed-point representation of the stable-outcome lattice under substitutability and IRC. It is an abbreviation of the raw carrier, with IRC as an interface proof parameter. The two inverse laws at 438–444 establish exactly one carried state for every stable contract set and no carried state representing an unstable set. The documentation expressly says the proof parameter does not change the carrier. |
| 339; 345 | `FixedPointStates.state`, `.outcome` | State projection and its realized contract set, respectively. The latter is the intersection of the two offer coordinates. Correct as a raw state accessor; its documentation does not assert stability without IRC. |
| 360–362 | `Market.ofStable` | Canonical embedding of a stable outcome into the fixed-point lattice. It uses the canonical acceptance state `(toSellers A, toBuyers A)`. The inverse equalities at 443–444 preclude collapsing distinct stable sets or introducing spurious represented outcomes. |
| 379–380; 387–388 | `StableOutcomes.state`, `.outcome` | Wrappers around the same two projections, whose stability and inverse-state characterization are supplied at 401–416. Correct under their supplied regularity assumptions. |
| 438–444 | `Market.stableEquivFixedPoints` | Bijection between stable contract sets and deferred-acceptance fixed points. The two maps and inverse proofs express the intended equivalence in both directions. It is deliberately an `Equiv`; no unsupported primitive-preference order instance is asserted. |
| 459–460 | `Market.sellerOptimalOutcome` | Seller-optimal and buyer-pessimal stable endpoint in the unanimous choice order. Correct: top/greatest fixed point, with seller optimality and buyer pessimism proved at 485–494 using both order-dictionary implications. |
| 463–464 | `Market.buyerOptimalOutcome` | Buyer-optimal and seller-pessimal stable endpoint. Correct: bottom/least fixed point, with the dual choice comparisons at 496–504. |

`RuralHospitals.lean` and `FixedPointConvergence.lean` introduce no independent definitions, structures, or abbreviations; they specialize and package the preceding concepts as theorems.

## Theorem interpretation and edge checks

- `StableOrder.lean:231–247` proves both directions of the order dictionary. If `p ≤ q`, sellers choose `outcome(q)` from the union and buyers choose `outcome(p)`; conversely either unanimous choice statement implies the state comparison. Reverse inclusion on the buyer coordinate is used consistently. The interpretation is a choice order. Arbitrary primitive preference comparisons are expressly excluded at 50–64 and 434–437, so absence of a many-demand welfare bridge is not a defect.
- `StableOrder.lean:506–542` distinguishes fixed-point lattice joins/meets from ambient coordinatewise joins/meets. Its equalities require the ambient operation itself to be fixed, so no unjustified closure assumption is hidden in the lattice interface.
- `RuralHospitals.lean:65–125` is the finite counting squeeze for opposite choice comparisons. Both outcomes are explicitly finite; natural-valued `Set.ncard` is never used as if it were a cardinal measure of arbitrary infinite outcomes. Buyers and sellers have opposite weak inequalities, and equality of total contract counts forces equality for every fiber.
- `RuralHospitals.lean:133–169` adds substitutability and finite contract type, obtains extremal stable comparators, and proves agent-by-agent contract-count invariance. This is the standard many-to-many contract-count rural hospitals statement. It does not claim identity of partners, quantities, or the stronger underfilled-hospital conclusion of the special responsive many-to-one model. Agent types themselves need not be finite because only finitely many contract endpoints occur.
- `FixedPointConvergence.lean:46–101` states finite stopping-time existence from `(univ, ∅)` and `(∅, univ)`, reaching greatest and least fixed points, respectively. Finite `X` makes the product of powersets finite. Substitutability supplies monotonicity; IRC is required only by the stable-outcome interpretation. No bound, executable algorithm, or arbitrary-initial-state convergence is claimed.
- Empty contract domains and choices rejecting every contract cause no false positive or negative: there is one stable empty outcome and one canonical fixed-point state. Irrelevant extra agents have empty fibers and contribute zero counts.

## Primary-source comparison

The [Hatfield–Kominers author manuscript](https://scottkom.com/assets/articles/Hatfield_Kominers_Contract_Design.pdf) was opened and checked. Lemma 1 (manuscript p. 11) states the unique fixed-point correspondence. Theorem 1 and its following paragraph give a lattice and opposing extremal outcomes. Theorem 4 (Appendix B, manuscript p. 25) gives invariant contract counts under substitutability and aggregate demand. The Lean interface explicitly records the distinction between primitive preferences in that model and its own choice-order formulation. No primary-source claim is being used to replace checking the actual formal definitions.

## Independent bounded computational checks

The retained Python program below enumerates every partition of up to three contracts into buyer and seller fibers (up to relabeling), every local choice map on every fiber, and filters exact contraction substitutability and set IRC. Under IRC the market's locality property is already proved in `Basic.lean:175–178`, so this local encoding represents every finite market satisfying the audited stable-outcome assumptions up to irrelevant agent labels. The program separately checks actual multi-contract blocking, fixed states, inverse correspondence, order in both directions, iteration from both extrema, and all individual contract counts when aggregate demand holds.

| Contracts | Local substitutable market instances (finite-convergence checks) | Substitutable + IRC instances (bijection checks) | Fixed-point pair order checks | Aggregate-demand instances (count checks) |
|---|---:|---:|---:|---:|
| 0 | 1 | 1 | 1 | 1 |
| 1 | 4 | 4 | 4 | 4 |
| 2 | 169 | 100 | 106 | 100 |
| 3 | 77,284 | 6,241 | 7,387 | 5,776 |

All assertions passed. These are bounded checks of the explicit encoding, not proofs for arbitrary domains. The non-IRC convergence sweep is restricted to local choice maps; the formal convergence theorem itself does not require locality.

A separately spawned hostile reviewer independently implemented a second enumeration using restricted-growth-string partitions, with no reuse of this program, and independently obtained exactly the same positive-contract counts (6,345 IRC markets, 7,497 fixed-point pair comparisons, 5,880 aggregate-demand markets). That reviewer also found no semantic defect in the assigned source. The second program ran as an unsaved heredoc; the reproducible program below retains the first check in full.

To reproduce: extract the following Python block and run with Python 3.9 or later. It uses only the standard library.

```python
from itertools import product

def subs(x): return [y for y in range(x+1) if y & ~x == 0]
def parts(mask):
    if not mask: return [()]
    bit=mask & -mask
    return [(g,)+p for g in subs(mask) if g & bit for p in parts(mask ^ g)]
def local_choices(group):
    menus=subs(group)
    out=[]
    for cs in product(*(subs(m) for m in menus)):
        c=dict(zip(menus,cs))
        sub=all(c[v]&w & ~c[w] == 0 for v in menus for w in subs(v))
        if not sub: continue
        cons=all(c[w]==c[v] for v in menus for w in subs(v) if c[v] & ~w == 0)
        load=all(bin(c[w]).count("1")<=bin(c[v]).count("1") for v in menus for w in subs(v))
        out.append((c,cons,load))
    return out

for n in range(4):
    full=(1<<n)-1; menus=range(full+1); states=list(product(menus,repeat=2))
    groups=parts(full); models={}
    for partition in groups:
        agents=[]
        for g in partition: agents.append(local_choices(g))
        models[partition]=[]
        for choices in product(*agents):
            C=tuple(sum(c[m & g] for g,(c,_,_) in zip(partition,choices)) for m in menus)
            models[partition].append((C,all(c for _,c,_ in choices),all(l for _,_,l in choices)))
    checked=stable_checks=order_checks=loadchecks=0
    for bp,sp in product(groups,repeat=2):
      for (B,bc,bl),(S,sc,sl) in product(models[bp],models[sp]):
        checked+=1
        accB=tuple(sum(1<<i for i in range(n) if B[m | (1<<i)] & (1<<i)) for m in menus)
        accS=tuple(sum(1<<i for i in range(n) if S[m | (1<<i)] & (1<<i)) for m in menus)
        F=lambda p:(accB[p[1]],accS[p[0]])
        le=lambda p,q:(p[0] & ~q[0] == 0 and q[1] & ~p[1] == 0)
        fixed=[p for p in states if F(p)==p]
        for initial,greater in [((full,0),True),((0,full),False)]:
            p=initial
            for t in range(len(states)+1):
                q=F(p)
                if q==p: break
                p=q
            else: raise AssertionError(('nonconvergence',n,bp,sp,B,S))
            assert (all(le(q,p) for q in fixed) if greater else all(le(p,q) for q in fixed))
        if not (bc and sc): continue
        stable=[]
        for a in menus:
            ir=(B[a]==a and S[a]==a)
            blocks=any(z & ~B[a|z] == 0 and z & ~S[a|z] == 0 for z in subs(full^a) if z)
            if ir and not blocks: stable.append(a)
        outcomes=[p[0]&p[1] for p in fixed]
        assert len(outcomes)==len(set(outcomes)) and set(outcomes)==set(stable)
        assert all(F((a,a)) in fixed and (accB[a]&accS[a])==a for a in stable)
        stable_checks+=1
        for p,q in product(fixed,repeat=2):
            a=p[0]&p[1]; d=q[0]&q[1]
            # q is seller-chosen over p, p is buyer-chosen over q.
            assert le(p,q)==(S[a|d]==d)==(B[a|d]==a)
            order_checks+=1
        if bl and sl:
            assert all(bin(a&g).count("1")==bin(d&g).count("1") for a,d in product(stable,repeat=2) for g in bp+sp)
            loadchecks+=1
    print({'n':n,'market_instances':checked,'irc_bijection_checks':stable_checks,'order_pair_checks':order_checks,'rural_hospitals_instances':loadchecks})
```
