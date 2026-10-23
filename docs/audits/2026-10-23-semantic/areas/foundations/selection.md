> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Semantic audit: selections, uniformization and fixed points

Source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`.
Source files were read without edits. This note covers:

- `MathEconLib/ForMathlib/ApproximateSelection.lean` (324 lines).
- `MathEconLib/ForMathlib/Kakutani.lean` (220 lines).
- `MathEconLib/ForMathlib/Schauder.lean` (4294 lines; detailed delegated review in `selection-schauder.md`).
- `MathEconLib/ForMathlib/MeasureTheory/AnalyticUniformization.lean` (374 lines).
- `MathEconLib/ForMathlib/MeasureTheory/VonNeumannSelection.lean` (125 lines).
- `MathEconLib/ForMathlib/MeasureTheory/AnalyticNullMeasurable.lean` (289 lines).

Result: no substantive conceptual defect found in these six files. One independently checked
low-priority documentation/API-strength mismatch is retained below. This conclusion is a semantic
source audit, not a claim that these modules were compiled in this checkout. Mathlib packages and
built project oleans were absent when inspected; no Lean-check success is claimed.

## Pass 1: concept inventory

All 13 definition-like entries assigned to this leaf are accounted for. Nine Schauder entries have
full bidirectional analysis in the companion note. Public `IsApproxSelection` was absent from the
first inventory generation and is included explicitly here.

| File and exact declaration line | Intended concept | Semantic verdict / assumptions |
| --- | --- | --- |
| ApproximateSelection:45 `IsApproxSelection` | Uniform graph approximation of a correspondence | Exactly `∀x, ∃x', (x,x')∈U ∧ ∃y∈F(x'), ∃w∈W, f(x)=y+w`. It does not by itself assert continuity, entourage membership of U, or neighborhood membership of W; main existence theorems supply them separately. |
| AnalyticUniformization:58 `listCylinder` | Basic finite-prefix cylinder in Baire space | Exactly sequences agreeing with the given list on indices below its length. `getD`'s default is inaccessible at those indices. |
| AnalyticUniformization:105 `leftmostPrefix` | Greedy lexicographically least feasible finite prefix | At each stage append the least natural number with a compatible extension in K. Requires nonempty K to interpret as a feasible prefix. |
| AnalyticUniformization:113 `leftmostBranch` | Infinite lexicographically least branch selected by feasible prefixes | For nonempty closed K, exactly its lexicographically least element; nonempty K ensures each least value exists, closedness ensures the limiting branch remains in K. Definitions are total outside those hypotheses, but no membership theorem is claimed there. |
| Schauder:55 `isDominant` | Scarf dominance/no common strict improvement | Exact component of the standard Scarf combinatorial construction; see companion note. |
| Schauder:62 `scarfAdjRel` | Room/door adjacency | Finite pair insertion/erasure relation; see companion note. |
| Schauder:78 `IsScarfVtx` | Scarf graph vertex | Dominant pair with the specified color discrepancy; see companion note. |
| Schauder:1088 `ordMin` | Minimum of a nonempty finite set under a specified linear order | Requires an explicit proof that the input is nonempty; see companion note. |
| Schauder:2199 `μ'` | Pair/order-specific chosen minimum | Requires an explicit nonemptiness proof and is definitionally the same minimum construction; see companion note. |
| Schauder:2203 `admSet` | Admissible insertion set for Scarf graph | Coordinate-order comparison against the retained minima; see companion note. |
| Schauder:3092 `DiscreteSimplex` | Rational grid in the standard simplex | Nonnegative coordinates summing to one and integral after multiplication by l; theorems needing an actual finite lattice assume `0 < l`; see companion note. |
| Schauder:3120 `discreteSimplex_encode` | Injective encoding of simplex-grid points by bounded integer coordinates | Uses `hl : 0 < l`; see companion note. |
| Schauder:3156 `rotateCoord` | Coordinate permutation putting i first | A permutation, with the intended lexicographic consequence; see companion note. |

The public named results implement standard sufficient theorems, rather than definitions of all
maps possessing a fixed point or a measurable selector. The converse of a fixed-point existence
statement is not an intended equivalence and its sufficient assumptions are not false negatives.

## Pass 2: both directions and theorem assumptions

### Approximate selection and star refinement

Unfolding `IsApproxSelection` at ApproximateSelection:45–48 and Minkowski addition gives the explicit
graph-approximation formula in the inventory table in both directions. In a normed additive group,
`f(x)∈F(x')+ball(0,ε)` iff there is y in F(x') with `dist(f(x),y)<ε`: in one direction write
`f(x)=y+w`, in the other put `w=f(x)-y`. For nonempty F(x'), this is equivalent to
`infDist(f(x),F(x'))<ε`. The helper at :133–142 uses the necessary nonemptiness, and all values are
required nonempty by the metric existence theorem at :312–324. There is no mistaken inference
from the special convention for distance to an empty set.

The upper-hemicontinuity API at :67–77 is the standard inverse-open-superset characterization:
for open V, `{x | F(x)⊆V}` is open. Either direction follows from the neighborhood definition.
Helpers :80–129 choose a symmetric entourage with controlled composition, construct an open
cover, and apply a subordinate partition of unity. The nonzero-support argument uses a sum equal
to one. Helpers :146–211 perform shrinking/local finiteness/star-refinement assembly.

For a cover S, the star condition at :222–223 is equivalent to: for every k₂,
`⋃{S(k₁) : S(k₁)∩S(k₂)≠∅} ⊆ C(π(k₂))`. This is the standard star-refinement inclusion. Empty
indexed members do not change it. The separate advertised all-members-nonempty property is absent;
see the observation below.

The existence theorems :241–284, :292–304 and :312–324 ask for a paracompact Hausdorff uniform
domain (automatic for the metric specialization), nonempty convex values, and zero-neighborhood
error in the codomain. Convexity is used for the partition-of-unity average. The first theorem
requires the given neighborhood to be open and convex; the locally convex version refines an
arbitrary zero-neighborhood by an open convex one. The output includes `Continuous f` and preservation
of a specified convex set containing all F values. These are the intended Cellina-style continuous
graph approximations, not exact continuous selection, which upper hemicontinuity alone would not
ensure. The metric formulation permits a nearby input x', as required for graph approximation.

### Kakutani–Glicksberg–Fan

Kakutani:35–47 states only that compact-valued upper-hemicontinuity in a Hausdorff target implies
a closed graph; no converse under arbitrary noncompact codomain is asserted. Its separation
argument correctly includes the possible empty value. The final theorem :209–220 explicitly
requires a nonempty compact convex k, a Hausdorff locally convex real topological vector space,
upper-hemicontinuity, nonempty compact convex F values, and `F(x)⊆k`. Its conclusion `∃x, ↑x∈F(x)`
is exactly correspondence fixed-point existence. Under compact Hausdorff k, compact values are
equivalent to relatively closed values, matching the common alternate formulation.

The private bridge :53–72 constructs an approximate fixed point using continuous approximate
selection plus Schauder. Helpers :77–163 index by genuine entourages and zero-neighborhoods and
use reverse inclusion (`atBot`), so errors tend to zero rather than grow. Compact extraction
:166–203 maintains a nonbottom filter; hence closed-graph membership at the common limit is not
vacuous. The use of general filters handles nonmetrizable k; no unspoken sequential compactness
assumption is imposed.

### Baire cylinders and leftmost branch

At AnalyticUniformization:58 the quantifier is precisely `k < t.length`, not an inclusive upper
bound. This makes the empty cylinder all Baire space and appending one value imposes just the next
coordinate (:63–100). Prefix consistency, length and feasibility are proved at :117–207. For
nonempty K, every greedy prefix meets K, proving that no lexicographically smaller K-element was
missed. Conversely any lexicographic minimum has exactly these recursively chosen coordinates.
For closed K, choosing one extending K-element for each prefix converges coordinatewise to the
branch, proving membership (:210–226). Closedness is essential and is explicitly present.

### Analytic uniformization, Luzin and measurable improvement

AnalyticUniformization:231–356 is Jankov–von Neumann uniformization for analytic R in a product
of Polish spaces with their Borel structures. All source sections are required nonempty. The
output graph lies in R **everywhere**, and measurability is explicitly with respect to the
sigma-algebra generated by analytic source sets, not Borel measurability. The Borel special case
at :362–370 retains that larger source sigma-algebra. The proof uses a continuous surjection of
Baire space onto R, closed fibers of the projected map, and the leftmost branch; cylinder-contact
sets are analytic, and finite prefixes are Boolean combinations of them. Empty X is handled
explicitly; no unnecessary nonempty action assumption is introduced when X is empty.

AnalyticNullMeasurable:53–100 is the bounded-coordinate diagonal compactness lemma. It uses a
compact product of finite coordinate sets, extracts a subsequence, and removes truncation only
once its index exceeds each fixed coordinate. It needs only the displayed metric codomain.
Auxiliaries :104–251 derive inner compact approximations in outer measure under a finite measure
and turn them into completion measurability. In particular monotone continuity for outer measures
induced by measures is legitimate; the intermediate images need not already be measurable.
Luzin's result :255–263 assumes a Polish Borel source and finite Borel measure and concludes
`NullMeasurableSet`, exactly completion measurability. Closure under complements and countable
unions proves the analytic-generated-sigma-algebra version :268–276; preimages give the function
version :280–286. None asserts the false general claim that analytic sets are Borel.

VonNeumannSelection:54–68 uses standard Borel X,A and a finite source measure. It first obtains
an everywhere analytic-measurable uniformization, then takes a Borel-measurable representative
of the completion-measurable map, preserving graph membership almost everywhere. Its quantifier
order permits the representative to depend on the measure, as it must. The improving-selection
result :72–121 assumes nonempty A, joint payoff measurability, measurable threshold and positive
outer measure of the improvement projection. Analytic/null measurability gives a measurable
positive-measure subset S₀. The enlarged relation allows arbitrary actions outside S₀; graph
membership on S₀ forces actual strict improvement. No exact maximizer, integrability or attainment
assumption is mistakenly inferred. Strict rather than weak inequality is preserved.

## Pass 3: adversarial checks and rejected concerns

- Allowing discontinuous functions in `IsApproxSelection` alone is intentional: its predicate is
  graph proximity and the continuous-selection theorems separately conjoin continuity.
- Allowing x'≠x in approximate selection is the standard graph-approximation notion; demanding
  distance from F(x) instead would incorrectly strengthen upper-hemicontinuous approximation.
- Nonempty closed K has a lexicographic minimum even though Baire space is noncompact: greedy
  prefixes converge in the product topology and closedness suffices. For nonclosed K consisting
  of sequences with at least one nonzero coordinate, the greedy branch is the all-zero sequence
  outside K; this does **not** contradict :210 because that K is not closed.
- For K=∅ the recursive `sInf ∅` convention may yield a total fallback, but all feasibility and
  membership statements require nonempty K. This creates no false selection theorem.
- A Borel relation need not have an everywhere Borel selector. The code avoids this standard
  false-positive pitfall by using analytic-generated measurability everywhere and Borel
  measurability only almost everywhere relative to the specified measure.
- Finite-measure and locally convex assumptions narrow theorem applicability exactly as stated;
  they do not misdefine the underlying economic concepts.
- Scarf order orientation, empty-set dominance convention, zero-denominator grid and omitted simplex
  coordinates were separately checked in the Schauder audit and independent review; see companion.

## Pass 4: independently checked observation and bounded evidence

**Low priority, documentation/API strength only:** ApproximateSelection:213–214 (also file-level
summary :22–23) says `exists_star_refinement` yields a family consisting only of nonempty sets.
Its formal output :215–223 does not include this property.

Minimal explicit witness to the missing implication: let X be the one-point discrete space {⋆},
let the original cover have one member C(⋆)=X, let κ=Bool, put S(false)=X and S(true)=∅, and let π
be constant. The family is open and locally finite, covers X, refines C and satisfies every
star-inclusion (all targets are X). Thus it satisfies the entire formal output while containing
an empty member. This does not refute the actual theorem or any downstream approximate-selection
proof; it demonstrates that clients cannot recover the documented additional property.

Proposed correction: either remove the nonemptiness promise from both comments, or strengthen the
output by `∀ k, (S k).Nonempty` and restrict the index type to `{k // (S k).Nonempty}` after constructing
the refinement. Removing empty indices preserves openness, local finiteness, coverage and all
inclusions. No source patch was applied.

Independent verification: another audit agent checked the singleton model directly and agreed
that it satisfies all displayed conjuncts and violates only the unasserted nonemptiness promise.
The exact finite model is also executed by `selection-check.py`.

Command executed successfully:

```text
python3 docs/audits/2026-10-23-semantic/areas/foundations/selection-check.py
```

Output:

```json
{
  "singleton_star_refinement_formal_conclusion": true,
  "singleton_star_refinement_all_nonempty": false,
  "metric_grid_equivalence_checks": 775,
  "closed_finite_baire_prefix_checks": 2555,
  "scope": "Exact finite witnesses/checks only; no general theorem inferred."
}
```

The metric checks compare strict infimum-distance and Minkowski-ball membership on all nonempty
subsets of the integer grid −2,…,2 for five exact rational radii and five function values. The
Baire checks compare greedy prefixes to lexicographic minimum for every nonempty subset of the
nine two-coordinate branches over {0,1,2}, extended by zero tails. These are sanity checks for
the exact finite instances; the general equivalences above were assessed mathematically, and no
bounded computation is represented as a proof of an infinite theorem.

## Standard-concept references consulted

- [Justin Moore, *MATH 7870: Descriptive Set Theory*, Theorem 49](https://pi.math.cornell.edu/~justin/Limited2Cornell/DST_lecture_notes.pdf):
  analytic relations admit uniformizations measurable for the sigma-algebra generated by analytic
  sets; the stated measure consequence is compatible with the finite-measure specialization here.
- [Bertsekas and Shreve, *Stochastic Optimal Control*, §7.6, Proposition 7.42](https://web.mit.edu/dimitrib/www/SOC_1978.pdf):
  universal measurability and the completion convention, including monotone continuity of outer
  measures induced by measures. The search excerpt exposed the relevant page; opening the full
  large PDF failed, so it was not used as evidence beyond that excerpt.
- [W. Kryszewski / L. Rybiński, *Methods in Multivalued Analysis*, lectures on approximation and selections](https://www.tmna.ncu.pl/static/files/LNNA_08.pdf):
  continuous graph approximations permit nearby inputs; this distinguishes approximate selection
  from exact selection. The library's displayed quantifiers were checked directly.
- [X. Dai, *A Fixed Point Theorem of Markov–Kakutani Type*, p.156](https://math.ubbcluj.ro/~nodeacj/download.php?f=171-da-1450-final.pdf):
  the recalled Kakutani–Fan–Glicksberg theorem has nonempty compact convex domain, locally convex
  Hausdorff ambient space and nonempty closed convex upper-semicontinuous values, matching the
  audited theorem using the compact/closed equivalence inside k.
