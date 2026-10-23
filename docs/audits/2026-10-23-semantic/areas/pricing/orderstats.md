> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Order statistics semantic audit

Audited source: `MathEconLib/Statistics/OrderStatistics.lean`, lines 1–740, at commit `1d9f8cc233cdaeee0364b51befb84feea657a4da`.
Source SHA-256: `6b718684239516ecc7299d2ff19214ea037a01fec5c553eec1ec769532a89709`.

**Conclusion:** no substantive definition-level semantic defect found in this file. All three mathematical definitions and the supporting instances were reviewed in both directions against their stated scopes. Ties, empty samples, singleton samples, atoms, endpoint exponents, almost-everywhere densities, and totalized expectation/derivative operations were examined. There are no independently verified counterexamples to report for this file. A minor mixed-indexing sentence is recorded separately below and is not a substantive finding.

## Definition coverage and bidirectional interpretation

| Source | Declaration | Intended concept | False-positive / false-negative analysis |
|---|---|---|---|
| 74–75 | `orderStatistics` | The `(k+1)`th smallest observation in a finite indexed sample, retaining repeated observations. Domain: any linear order; `v : Fin n → α`, `k : Fin n`. | Exact. `Finset.univ.val` contains each index once; **multiset** `map v` preserves equal values at distinct indices; sorting is nondecreasing and `.get k` selects rank `k+1`. Every formal value has the standard rank, and every standard rank of this sample is returned. No distinctness assumption is required. |
| 155–166 | `OrderStatisticsSetup` | A finite family of measurable mutually independent identically distributed real random variables whose common law is absolutely continuous with respect to Lebesgue measure. | Exact under the explicit common-density restriction. `iIndepFun` gives mutual independence, not merely pairwise independence; `IdentDistrib` imposes equality of pushforward laws. `HasPDF` supplies a.e. measurability, Lebesgue decomposition, and absolute continuity. On real Lebesgue space and for a probability law, the decomposition exists, so a standard measurable iid family with an absolutely continuous law supplies these fields. Conversely, the fields imply precisely these properties. The density need only be shared a.e., as it should be. |
| 174–175 | probability-law instance for each `S.X i` | Pushforward of a probability measure by a measurable random variable is a probability measure. | Exact, using the explicitly supplied measurability. Prevents interpreting `cdf` of a nonprobability or failed measurable pushforward here. |
| 178–179 | `OrderStatisticsSetup.val` | Samplewise order statistic random variable `ω ↦ X_(k+1)(ω)`. | Exact by unfolding `orderStatistics`; there is no alternate sorting or law-based representative that could change it on individual sample points. All standard samplewise values are retained, including zero-probability tied samples. |
| 222–225 | `hasPDF_val` | Absolute continuity of the law of each selected order statistic. | Correct: a selected sample value lying in a Lebesgue-null set implies one of the finitely many original sample values lies there; the finite union has probability zero. Independence and identical laws are unnecessary for this particular implication but do not invalidate it. |
| 227–229 | probability-law instance for `S.val k` | Order-statistic pushforward is a probability law. | Exact because `measurable_val` establishes measurability. |
| imported; used at 281–285, 379–382, 505–509 | `ProbabilityTheory.cdf`, `MeasureTheory.pdf` | Right-continuous CDF `P(X≤x)`; Radon–Nikodym density of the pushforward. | No local or private replacement is defined in this file. The file explicitly rewrites the CDF to the `Iic x` event (383–386). `pdf_val` asserts a.e. equality, the correct equivalence relation for densities. There is no hidden strict-CDF convention or pointwise-derivative definition of a PDF. |

A direct bidirectional rank characterization, already stated at lines 101–103, is

`orderStatistics v k ≤ x ↔ k+1 ≤ #{i : v i ≤ x}`.

This is a complete concept-level characterization: if a proposed value `y` had exactly these threshold comparisons for every `x`, then `y` equals the sorted value by antisymmetry, using `x=y` and `x=orderStatistics v k`. Thus the definition cannot silently implement a different rank despite passing monotonicity or membership checks alone.

Reference conventions: the ordered sample including ties is `y₁≤⋯≤yₙ` in [Penn State STAT 414, §13.3](https://online.stat.psu.edu/stat414/Lesson13). The standard continuous-iid density with 1-based rank `r` is `n!/((r−1)!(n−r)!) F^(r−1)(1−F)^(n−r)f`, consistent with `r=k+1`, in [University of Washington STAT 512, Lecture 9](https://faculty.washington.edu/yenchic/20A_stat512/Lec9_Order.html). The imported density terminology is documented in [mathlib, Probability.Density](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Density.html).

## Supporting theorem audit

| Source | Result | Semantic assessment |
|---|---|---|
| 78–81; 84–90 | `orderStatistics_mono`, `orderStatistics_mem_range` | Correct necessary properties; multiplicity is additionally justified by the construction and rank equivalence, so these weaker statements are not mistaken for a complete definition. |
| 101–144 | `orderStatistics_le_iff` | Correct weak-threshold counting equivalence, including ties. `≤` occurs on both sides. |
| 182–188; 195–205 | count-event and rank measurability | Match finite sums of measurable threshold indicators and the CDF generating family. No missing measurability assumption. |
| 207–219 | `map_val_absolutelyContinuous` | Correct finite-null-union argument, as detailed above. |
| 236–275 | `expected_val_eq_sub_integral_cdf` | Correct bounded-variable layer-cake formula `E[Y]=b−∫ₐᵇF_Y`. It explicitly assumes `a≤b` and all samples a.s. in `[a,b]`; the proof establishes the rank's integrability. Negative `a` is allowed. |
| 279–316 | fixed threshold-pattern probability | Correct by mutual independence, common law, and complement probabilities. Exponents count `T` and its complement. |
| 321–371 | `prob_count_eq` | Correct binomial PMF; for `l>n`, the event is empty and `choose n l=0`. Natural subtraction `n−l` then causes no false mass. |
| 378–401 | `cdf_val` | Correct binomial-tail CDF with lower rank `k+1`; minimum is `1−(1−F)^n`, maximum is `F^n`. Atoms would not invalidate this identity, but are outside the bundled common-density setup. |
| 405–479 | `hasDerivAt_binomial_tail_sum` | Correct polynomial derivative for every real `p`; validity is not restricted to `0<p<1`. With `k<n`, `n−1−k` is the intended nonnegative exponent, not an accidentally truncated negative exponent. |
| 488–498 | `identDistrib_val` | Correct law invariance for two families of the same size and rank. The cross-family hypothesis over every `i,j` is redundant under within-family iid, but equivalent to equality of any one pair of marginal laws when `k : Fin n` exists. |
| 504–534 | `pdf_val` | Correct coefficient, exponents, and base density, a.e. Derivation uses a.e. differentiability and finite Radon–Nikodym derivatives, so no pointwise differentiability assumption is silently omitted. |
| 546–569 | `integral_cdf_pow` | Correct integration by parts for `m≥1` and `F(a)=0`; the excluded `m=0` would have a nonzero lower boundary term. `s<a` is permitted because interval integrals are oriented and `F` vanishes to the left of `a`. |
| 579–623 | `expected_val` | Correct bounded-support density formula. Explicit boundedness is not a missing hypothesis: `F(a)=0`, `F(b)=1`, and equality of marginal laws imply `a<X_i≤b` a.s. Hence the rank and all displayed integrands are integrable. |
| 632–732 | `expected_second_highest` | Correct with 1-based rank `n−1`, hence 0-based index `n−2`, requiring `n≥2`. Fubini uses an established integrable majorant. The conversion `P(X≥ψ)=1−F(ψ)` is justified by absolute continuity, explicitly deleting singleton mass at lines 709–718. This is the probability identity used in revenue equivalence, not by itself a statement that arbitrary auction mechanisms have equivalent revenue. |

## Counterexample searches and edge-case disposition

1. **Ties and repeated minima:** for `(0,0,1)`, rank `k=1` is `0`, not `1`. The multiset construction returns `0`, so it does not discard repeated observations. This is a probe of the candidate defect, not a counterexample to the implementation.
2. **No sample:** when `n=0`, the setup's fields can be vacuous, representing the standard empty iid family. There is no `k : Fin 0` or `i₀ : Fin 0`; neither `val` nor the formulas can be called with an invalid rank or nonexistent marginal. No arbitrary default observation is introduced.
3. **Singleton:** for `n=1,k=0`, CDF tail is `F`, density multiplier is `1!/(0!0!) F^0(1−F)^0=1`, and the rank is exactly the sole sample.
4. **CDF endpoints:** Lean's `0^0=1` is correct for the binomial convention. At `F=0` every tail term has positive `F` exponent; at `F=1` only `l=n` survives. No endpoint exception or division by `F` occurs.
5. **Atoms:** a Dirac or Bernoulli law cannot supply `HasPDF ... volume`, because a positive-mass singleton is Lebesgue-null. This is an explicit scope restriction rather than a false negative for the advertised common-density setup. The deterministic definition still allows tied/discrete sample values; binomial CDF algebra was independently checked on atomic examples to test the weak/strict threshold convention.
6. **Nonsmooth densities:** differentiability is needed only Lebesgue-a.e. in `pdf_val`; discontinuous PDFs and piecewise-linear continuous CDFs remain admissible. A singular continuous law is excluded by absolute continuity even though it has a continuous CDF; no equation between these concepts is asserted.
7. **Totalized real integrals and derivatives:** boundedness is explicit or follows from the CDF endpoints in expectation theorems. Local density integrands are bounded factors times an integrable PDF. The a.e. derivative statements use `HasDerivAt` rather than interpreting default `deriv=0` as differentiability. `pdf.toReal` may ignore infinite values on a null set only; `rnDeriv_lt_top` is explicitly invoked at 520–522.
8. **Degenerate interval:** `a=b` is consistent with the bounded layer-cake theorem (`Y=a` a.s.; integral zero). It is incompatible with simultaneously `F(a)=0` and `F(b)=1`, so it cannot supply an unwanted example to the endpoint-based density or second-highest theorems.
9. **Negative support:** neither density expectations nor integration by parts require nonnegative values; translated laws with `a=−2,b=1` were checked exactly.

## Independently executed exact checks

The Python code below uses exact rational arithmetic and independent finite enumeration/polynomial arithmetic, without importing or reimplementing the Lean proofs' tactic steps. It checks the semantic equations encoded here; it is not evidence that every family or every real input has been computationally enumerated. The conceptual equivalences above supply the unbounded mathematical argument.

An exact finite calculation completed during the original audit. It is supplemental evidence, not a proof of the general moment statements.
Script SHA-256: `da2a90cc4e4bb5b07e0650b0cf3eaa4660b95dc13732908e2b01d762f119b3b2`.

Output:

```text
sorted/count equivalence checks: 30075
atomic-law binomial/CDF endpoint checks: 144
exact polynomial derivative/density/moment checks: 78
second-highest exact translated/nonuniform law checks: 165
all exact checks passed
```

The first family enumerates all samples of lengths 1–6 from `{−1,0,1}`, all ranks and thresholds `{−2,−1,0,1,2}`. The second directly enumerates Bernoulli product measures for sample sizes 1–8 with probabilities `0,1/3,1/2,1`. The third checks exact polynomial identity for the binomial-tail derivative, density normalization, and means for every rank with `n≤12`. The fourth checks the second-highest expectation using continuous laws `F(x)=((x−a)/d)^r` on `[a,a+d]`, `2≤n≤12`, `1≤r≤5`, and `(a,d)=(0,1),(-2,3),(2,1/2)`.

No Lean compilation was claimed: at the time of this subaudit, `.lake/packages/mathlib` contained only `.git`, with no mathlib sources/build artifacts in this worktree. This does not affect the exact-arithmetic results or source-level semantic analysis.

## Documentation-only observation, excluded from substantive findings

At source line 578, the sentence says `X_(0)` is the minimum immediately after displaying `E[X_(k+1)]` at line 576. This mixes 0-based formal indices with the 1-based mathematical `X_(r)` convention established at 69–73. Proposed clarification: “`k` is 0-indexed: `k=0` selects `X_(1)`, the minimum, and `k=n−1` selects `X_(n)`, the maximum.” No formal result or definition needs correction.

## Reproducible exact-check code

```python
from fractions import Fraction as Q
from itertools import product
from math import comb, factorial


def add(p,q):
    a=[Q(0)]*max(len(p),len(q))
    for i,c in enumerate(p): a[i]+=c
    for i,c in enumerate(q): a[i]+=c
    return trim(a)
def trim(p):
    while len(p)>1 and p[-1]==0: p.pop()
    return p
def mul(p,q):
    a=[Q(0)]*(len(p)+len(q)-1)
    for i,c in enumerate(p):
        for j,d in enumerate(q): a[i+j]+=c*d
    return trim(a)
def scale(p,c): return trim([c*x for x in p])
def power(p,n):
    a=[Q(1)]
    for _ in range(n): a=mul(a,p)
    return a
def deriv(p): return trim([i*c for i,c in enumerate(p)][1:] or [Q(0)])
def integral(p): return sum(c/Q(i+1) for i,c in enumerate(p))
def anti(p): return [Q(0)]+[c/Q(i+1) for i,c in enumerate(p)]

thresholds=(-2,-1,0,1,2)
counts=0
for n in range(1,7):
    for v in product((-1,0,1),repeat=n):
        y=sorted(v)
        for k in range(n):
            for x in thresholds:
                assert (y[k]<=x)==(k+1<=sum(z<=x for z in v))
                counts+=1
assert sorted((0,0,1))[1]==0
assert sorted((1,-1))[0]==-1
print('sorted/count equivalence checks:', counts)

probs=0
for n in range(1,9):
    for p in (Q(0),Q(1,3),Q(1,2),Q(1)):
        atoms={v:p**sum(v)*(1-p)**(n-sum(v)) for v in product((0,1),repeat=n)}
        assert sum(atoms.values())==1
        # Here Bernoulli 0 mass is p, so put values 0 for successful Iic(0) indicators.
        for k in range(n):
            actual=sum(w for v,w in atoms.items() if sorted(tuple(1-i for i in v))[k]<=0)
            target=sum(Q(comb(n,l))*p**l*(1-p)**(n-l) for l in range(k+1,n+1))
            assert actual==target
            probs+=1
print('atomic-law binomial/CDF endpoint checks:', probs)

symbolic=0
for n in range(1,13):
    for k in range(n):
        cdf=[Q(0)]
        for l in range(k+1,n+1):
            cdf=add(cdf,scale(mul(power([0,1],l),power([1,-1],n-l)),Q(comb(n,l))))
        C=Q(factorial(n),factorial(k)*factorial(n-1-k))
        density=scale(mul(power([0,1],k),power([1,-1],n-1-k)),C)
        assert deriv(cdf)==density
        assert integral(density)==1
        assert integral(mul([0,1],density))==Q(k+1,n+1)
        assert 1-integral(cdf)==Q(k+1,n+1)
        symbolic+=1
print('exact polynomial derivative/density/moment checks:', symbolic)

second=0
for n in range(2,13):
    for r in range(1,6):
        for a,d in ((Q(0),Q(1)),(Q(-2),Q(3)),(Q(2),Q(1,2))):
            t=[0,1]; x=[a,d]; F=power(t,r); ft=scale(power(t,r-1),Q(r))
            density=scale(mul(mul(power(F,n-2),add([1],scale(F,-1))),ft),Q(n*(n-1)))
            left=integral(mul(x,density))
            # Inner dx = d dt. Outer probability density in t is ft.
            inner=scale(anti(power(F,n-1)),d)
            integrand=add(mul(x,power(F,n-1)),scale(inner,-1))
            right=n*integral(mul(integrand,ft))
            assert left==right
            second+=1
print('second-highest exact translated/nonuniform law checks:',second)
print('all exact checks passed')
```
