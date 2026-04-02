# Code Review: `mechanism-refactor` Branch

**Date:** 2026-04-02
**Branch:** `mechanism-refactor` (vs `main`)
**Scope:** 28 files changed, +2409/−1046 lines

## TODO Summary

- [x] **1.1** Refactor `strictMonotonicity` to use `ReducedForm` (or extend `ReducedForm`)
- [x] **1.2** Redefine `Auction.Efficient` as `A.rules.IsEfficient`
- [ ] **1.3** Replace `q_range` body with delegation to `q_strat_range`
- [ ] **2.1** Rename `ReducedForm.allpayBid` to `allPayBid` for consistency
- [ ] **2.2** Remove duplicate `bundledProfit` (use `sellerProfit`)
- [ ] **3.1** Delete `welfare_variance_penalty` (redundant with `welfare_gap`)
- [ ] **3.3** Consider removing trivial `revenue_boundary_regime`
- [ ] **4.1** Move `expected_sum_erase` out of `SymmetricIPV.lean` to `Basic.lean`
- [ ] **5.1** Narrow `variable` scopes to eliminate 9 linter suppressions
- [ ] **6.1** Delete or `.gitignore` untracked `test.lean`
- [ ] **7.1** Trim docstrings that restate proof internals

---

## 1. Design Flaws

### 1.1 `StrictMonotonicity.lean` bypasses the `ReducedForm` abstraction

> **DONE:** Refactor `strictMonotonicity` (and helpers `winProb_gap`,
> `ic_contradiction`, `no_ties`) to take a `ReducedForm` instead of raw
> `G`, `β`, `C` functions — or extend `ReducedForm` with the fields needed
> for the strict monotonicity argument.

**Location:** `Auctionlib/Auction/StrictMonotonicity.lean:207-244`

The central theorem `strictMonotonicity` takes raw functions `G : ℝ → ℝ`,
`β : ℝ → ℝ`, `C : ℝ → ℝ` as separate parameters, completely sidestepping the
`ReducedForm` structure that every other file in the codebase works through.

This means strict monotonicity results cannot compose with the rest of the
framework (envelope theorem, Myerson's lemma, payment identity) without manual
plumbing at every call site. The helper lemmas `winProb_gap`, `ic_contradiction`,
and `no_ties` all operate on the same raw-function signature.

If `ReducedForm` is the intended abstraction boundary (as the architecture
section of CLAUDE.md states), this theorem should speak in those terms. If it
cannot, that signals `ReducedForm` is missing fields or structure needed for
the strict monotonicity argument.

### 1.2 `Auction.Efficient` duplicates `Mechanism.IsEfficient`

> **TODO:** Redefine `Auction.Efficient` as `def Efficient : Prop :=
> A.rules.IsEfficient` and remove the duplicated body.

**Locations:**
- `Auctionlib/Auction/SymmetricIPV.lean:164-165`
- `Auctionlib/Mechanism/Basic.lean:50-51`

Both define the identical predicate:

```lean
-- Mechanism/Basic.lean:50
def IsEfficient : Prop :=
  ∀ i, M.x i = {f | ∀ j ≠ i, f j < f i}.indicator 1

-- SymmetricIPV.lean:164
def Efficient : Prop :=
  ∀ i, A.rules.x i = {f | ∀ j ≠ i, f j < f i}.indicator 1
```

`Auction.Efficient` should be defined in terms of `Mechanism.IsEfficient`
(i.e., `def Efficient : Prop := A.rules.IsEfficient`), not as a standalone
copy. Currently the two predicates are definitionally equal but there is no
lemma connecting them, so proofs about one cannot directly use results about
the other without `show`/`change` coercions.

### 1.3 `Auction.q_range` is a near-duplicate of `q_strat_range`

> **TODO:** Replace the body of `q_range` with a one-liner delegating to
> `q_strat_range hx measurable_id i s`.

**Location:** `Auctionlib/Auction/Basic.lean:109-126` vs `Basic.lean:86-105`

`q_range` re-proves from scratch what `q_strat_range` with `σ = id` already
gives. The proof bodies are nearly identical (same measurability argument, same
integrability argument, same `integral_mono` + `integral_const` calculation).
Since `q = q_strat id` is proved at line 80 (`q_eq_q_strat_id`), `q_range`
should delegate to `q_strat_range`.

### 1.4 `HasOrderStatWinProb` is a `def`, not a `class`

**Location:** `Auctionlib/Auction/StrictMonotonicity.lean:47-52`

`HasOrderStatWinProb` is defined as a `def` returning `Prop`, but the rest of
the codebase uses typeclasses (`HasIndependentTypes`, `HasIdenticalTypes`,
`HasBoundedTypes`, etc.) for auction environment properties. It is passed as an
explicit hypothesis to `strictMonotonicity`, `no_ties`, and `winProb_gap`.

This is not necessarily wrong (it takes `G` and `β` as parameters, making
typeclass resolution awkward), but it is inconsistent with the rest of the
design and worth noting.

---

## 2. Naming and Consistency Issues

### 2.1 `allPayBid` vs `allpayBid`

> **TODO:** Rename `ReducedForm.allpayBid` to `ReducedForm.allPayBid`
> (and update `allpayBid_lowestType` to `allPayBid_lowestType`).

**Locations:**
- `Auctionlib/Auction/AllPurchase.lean:156` — `Auction.allPayBid` (camelCase "Pay")
- `Auctionlib/ReducedForm/TypeDeviationIC.lean:95` — `ReducedForm.allpayBid` (lowercase "pay")

These represent the same economic concept at different layers. The naming
should be consistent. Mathlib convention would favor `allPayBid` (camelCase
for multi-word identifiers).

### 2.2 `bundledProfit` is identical to `sellerProfit`

> **TODO:** Remove `bundledProfit` and redefine it as
> `abbrev bundledProfit := sellerProfit`, or delete it entirely and update
> `bundled_exceeds_editionsOnly` to use `sellerProfit`.

**Location:** `Auctionlib/Auction/AllPurchase/Revenue.lean`

```lean
-- Line 71
noncomputable def sellerProfit (φ_bar c p α M : ℝ) (n : ℕ) : ℝ :=
  (p - c) * expectedTotalQuantity φ_bar p α M n

-- Line 110
noncomputable def bundledProfit (φ_bar c p α M : ℝ) (n : ℕ) : ℝ :=
  (p - c) * expectedTotalQuantity φ_bar p α M n
```

These are the same function with different names and parameter order (`c p` vs
`c p`— actually identical order too). One should be defined in terms of the
other, or one should be removed.

---

## 3. Redundant / Misleading Code

### 3.1 `welfare_variance_penalty` is redundant with `welfare_gap`

> **TODO:** Delete `welfare_variance_penalty`.

**Location:** `Auctionlib/Auction/AllPurchase/Welfare.lean:136-145`

`welfare_variance_penalty` proves:
```
W(μ) - W(B) = α(B-μ)² - (φ̄-c)(B-μ) + α(B²-μ²) - α(B-μ)²
```

The RHS simplifies (by `ring`) to `-(φ̄-c)(B-μ) + α(B²-μ²)`, which is
exactly what `welfare_gap` at lines 143-145 already states. The theorem name
"variance penalty" is misleading — it does not isolate a variance term. The
elaborated RHS contains `α(B-μ)² - α(B-μ)²`, which cancels to zero, making
the "variance penalty" portion a no-op.

### 3.2 `revenue_decomposition` and `welfare_decomposition` are trivial

**Locations:**
- `Revenue.lean:46-50`: proved by `linarith`
- `Welfare.lean:125-130`: proved by `ring`

Both take fully abstract `ℝ` parameters with no connection to any auction
structure. They are pure arithmetic lemmas (substitution of one equation into
another) dressed up as economic propositions. They do not use any typeclass,
structure, or domain-specific fact.

### 3.3 `revenue_boundary_regime` is similarly trivial

> **TODO:** Consider inlining `revenue_boundary_regime` at call sites or
> removing it. If kept, add a note explaining why the named lemma is useful.

**Location:** `Revenue.lean:53-56`

```lean
theorem revenue_boundary_regime ... (h_net : revenue = allPayRevenue - ↑n * (0 : ℝ) + editionValue) :
    revenue = allPayRevenue + editionValue := by linarith
```

This is `x - n * 0 + y = x + y`, a one-step simplification of the hypothesis.

---

## 4. Misplaced Code

### 4.1 `expected_sum_erase` belongs outside `SymmetricIPV.lean`

> **TODO:** Move `expected_sum_erase` to `Auction/Basic.lean` (where
> `HasIdenticalTypes` is not required via `IsSymmetricIPV`) or to a new
> utility file like `Auction/IdenticalTypes.lean`.

**Location:** `Auctionlib/Auction/SymmetricIPV.lean:213-227`

This theorem only requires `HasIdenticalTypes`:
```lean
theorem expected_sum_erase [HasIdenticalTypes A]
    (f : ℝ → ℝ) (hf_meas : Measurable f) (i : Fin n)
    (hf_int : ∀ j, Integrable (fun ω => f (A.θ j ω)) ℙ) : ...
```

It is a general expectation identity (linearity + symmetry) that has nothing
to do with the "symmetric IPV" bundle (`IsSymmetricIPV`). It is used by
`LinearScarcity.lean` (via `expected_scarcity_linear`), which only needs
`HasIdenticalTypes`.

Placing it in `SymmetricIPV.lean` means any file that needs this lemma must
import the entire symmetric IPV typeclass hierarchy, even if it only requires
identical types.

---

## 5. Linter Suppressions

### 5.1 Excessive `set_option linter.unusedSectionVars false`

> **TODO:** Narrow the `variable` declarations in `SymmetricIPV.lean` and
> `StrictMonotonicity.lean` (e.g., split into subsections with tighter
> assumptions, or use `omit` consistently) so the linter suppressions can
> be removed.

**Locations:**
- `SymmetricIPV.lean`: lines 95, 99, 103
- `StrictMonotonicity.lean`: lines 59, 74, 89, 112, 146, 154, 178

Nine suppressed warnings across two files. This indicates the `variable`
declarations at the top of sections are too broad — they introduce typeclass
assumptions (e.g., `[n.AtLeastTwo]`, `[HasBoundedTypes A]`,
`[HasAtomlessTypes A]`, `[HasPosDensity A]`) that many lemmas in the section
do not actually use.

The `omit` directive is used in some places as a partial workaround
(`omit [n.AtLeastTwo] in`), but this is applied inconsistently.

---

## 6. Uncommitted / Stray Files

### 6.1 Untracked test file

> **TODO:** Delete `Auctionlib/Auction/AllPurchase/test.lean` or add it to
> `.gitignore` before pushing.

**Location:** `Auctionlib/Auction/AllPurchase/test.lean`

This file appears in `git status` as untracked. It should either be added to
`.gitignore`, deleted, or committed — but not left as untracked debris before
pushing.

---

## 7. Verbose Documentation

### 7.1 Docstrings that restate proof internals

> **TODO:** Trim docstrings on `expected_sum_erase`,
> `boundary_regime_strategy_auction`, and the `-- Verify via completed-square
> form` comment in `ExplicitSolutions.lean` to remove proof-internal details.

Several docstrings explain which lemmas are used in the proof rather than
documenting the mathematical content. Examples:

- `expected_sum_erase` (`SymmetricIPV.lean:209-211`):
  > Combines linearity of expectation (`integral_finset_sum`) with
  > identical distribution (`IdentDistrib.map_eq`).

  The lemma names used in a proof are implementation details. They change when
  Mathlib is updated and add no information beyond what the proof term shows.

- `ExplicitSolutions.lean:232-234`: Comment `-- Verify via completed-square form`
  restates what the next line (`netCostLinear_completed_square`) already
  communicates.

- `boundary_regime_strategy_auction` (`ExplicitSolutions.lean:384-386`):
  > The winning probability `q_strat β i` is derived from the mechanism's `x_eq`,
  > and the cost `allPurchaseNetCost` from its `t_eq`.

  This describes how the hypotheses are constructed, not what the theorem says.

### 7.2 Module headers that duplicate CLAUDE.md

The architecture description in CLAUDE.md already documents the typeclass
hierarchy, the three-layer design, and the flow. Several module-level `/-! -/`
headers repeat subsets of this information. This creates a maintenance burden:
changes to the architecture must be reflected in both places.

---

## 8. Structural Observations (Non-Issues, But Notable)

### 8.1 `@[expose] public section` pattern

Every `.lean` file uses the `module` + `@[expose] public section` pattern.
This makes all definitions and lemmas globally visible. If this is intentional
(to avoid qualified access in downstream files), it is consistent. If not, it
means the namespace boundaries declared by `namespace Auction` etc. are
effectively nullified.

### 8.2 Revenue/Welfare files operate on raw `ℝ` parameters

`Welfare.lean` and `Revenue.lean` define welfare/revenue concepts
(`editionWelfare`, `cournotQuantity`, `firstBestQuantity`, `sellerProfit`,
etc.) as plain functions on `ℝ` parameters with no connection to the `Auction`
or `ReducedForm` structures. All theorems in these files are pure algebra.

This is a conscious design choice (algebraic layer separate from the
probabilistic layer), but it means there is no formal bridge connecting, e.g.,
`cournotQuantity φ_bar p α n` to any actual auction's equilibrium quantity.
The economic interpretation exists only in comments.

### 8.3 `IsInteriorRegime` extends `HasQuadraticCost` but `IsBoundaryRegime` does not

**Location:** `LinearScarcity.lean:70` vs `LinearScarcity.lean:63`

`IsInteriorRegime` extends `HasQuadraticCost` (providing `α_coeff`,
`K_param`, `cost_eq` for free), but `IsBoundaryRegime` is a standalone
`Prop`-valued class with only `U_lowestType_zero`. This asymmetry means
that in the boundary regime, `HasQuadraticCost` must be provided separately,
while in the interior regime it comes bundled. The boundary regime theorems
(e.g., `boundary_regime_strategy`) must explicitly require both
`[HasQuadraticCost R]` and `[IsBoundaryRegime R]`.
