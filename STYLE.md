# MathEconLib Style Guide

This file provides the expected style of Lean files within the library. In general, `MathEconLib` follows the [Mathlib style guidelines](https://leanprover-community.github.io/contribute/style.html) and [naming conventions](https://leanprover-community.github.io/contribute/naming.html), so please look there for guidance on areas not covered in this file.

## Within-file organization

### Headers and imports
The file header should contain copyright information, a list of all the authors who have made significant contributions to the file, and a description of the contents. Put the module keyword on its own line right after the header, skip a line, then group all public imports together, skip another line, then group all imports together. Try to keep the imports alphabetical within each block of imports.

```
/-
Copyright (c) <YEAR> <AUTHORS>. All rights reserved.
Released under license as described in the file LICENSE.
Authors: <AUTHORS>
-/
module

<PUBLIC IMPORTS>

<IMPORTS>

<MODULE DOCSTRING>

@[expose] public <noncomputable?> section

<OPEN TERM(S)>

<NAMESPACE DECLARATIONS>
<CONTENT>
```

### `import`s
- Only include imports that are actually used or that are intentionally reexported as API. Mathlib's `#min_imports` works in `MathEconLib`; consult [their documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/MinImports.html) for more information. 
- The symbols exported by `public import` become part of the file's API, so prefer private imports except when necessary.

### Module docstrings
Top-level module docstrings discuss the *content* of the file and should be organized as below. Do not include meta-commentary or proof details.

```
/-!
# <Brief, descriptive title>

<One to two paragraph module description>

## Main definitions
<list of main definitions>

## Main statements
<list of main statements>

## Notes <optional section>
<This section should not be used often, but when used discusses further details of note.>

## References <optional section>
<references if appropriate using author-date>

## Tags
<comma delimited list of tags in all lowercase>
-/
```

## Declaration guidelines
- Reserve the `theorem` keyword for important results and theorems. Otherwise use the `lemma` keyword.
- Unused hypothesis should have their warnings suppressed with `set_option linter.unusedVariables false in`; prefer this to prefixing with an underscore. Always include a comment justifying why the unused hypothesis is necessary for the desired semantics of the declaration. If it is not necessary, remove it.
- Always use Mathlib naming conventions. Often the Mathlib-style name is not like the common name; in that case the common name should be given in the docstring as shown below:
  ```
  /-- **Central Limit Theorem:** Given a sequence of random variables `X : ℕ → Ω → ℝ` that are
  independent, identically distributed, centered and with variance `1` and a random variable
  `Y : Ω' → ℝ` following `gaussianReal 0 1`, the sequence
  `n ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k` converges to `Y` in distribution. -/
  theorem tendstoInDistribution_inv_sqrt_mul_sum <...>
  ```
- Prefer `structure` over `def foo := p₁ ∧ p₂ ∧ …` for any `Prop` with more than one conjunct. A predicate bundle with named fields documents each component, gives callers stable named projections, and is the natural home for its own API (`Foo.of_…`, `Foo.mp`, …). Bare `def`s built from `And` are reserved for very short-lived, local, or single-use predicates that never accumulate their own API.
- All declarations should have docstrings.
- Docstrings should be brief and discuss the result without mentioning metacommentary or proof strategies.
- Use namespacing to control name length. For example, mathlib would usually avoid a flat name like:
    `isSomePredicate_of_IsSomeOtherLongPredicate_of_someOtherProperty`
  and prefer one of these shapes, depending on context:
    `SomePredicate.of_isSomeOtherLongPredicate_of_someOtherProperty`
  or, if it is naturally a theorem about an object/class namespace:
    `SomeObject.isSomePredicate_of_isSomeOtherLongPredicate_of_someOtherProperty`
  or, if the target predicate is itself the namespace:
  `IsSomePredicate.of_isSomeOtherLongPredicate_of_someOtherProperty`

  Real examples of that style:

  `RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal`
  `Precoverage.IsStableUnderBaseChange.of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms`

### Private declarations
As a general principle, avoid private declarations unless there is a strong justification. Private declarations should also carry docstrings.

## Proofs
Prefer readable and short proofs.

### Comments
- Inline proof comments should be used sparingly and only to describe a subtle point that is not immediately obvious. 
- Comments should always have the intended audience of experienced lean4 devs and competent mathematicians.
- If the comment explains a proof step that is immediately obvious by the next line, it should be deleted.
- Avoid metacommentary.

### Example
This comment should be deleted:
```
-- hlt : u < cdfReal F c. By continuity, ∃ δ > 0, ∀ y, |y - c| < δ → cdfReal F y > u.
  have h_cont_at_c : ContinuousAt (cdfReal F) c := h_cont.continuousAt
```

This comment should NOT be deleted:
```
-- `G ω` is the average distance from `ω` to its perturbed posterior `kLam ω`; `B μ`
-- is the `μ`-average of `G`, and both are bounded by `‖dBC‖`.
  set G : Ω → ℝ := fun ω => ∫ y, dist ω y ∂kLamKernel ω with hG_def
  have hG_smeas : MeasureTheory.StronglyMeasurable G :=
    MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'
      (κ := kLamKernel) continuous_dist.stronglyMeasurable
  have hG_bdd : ∀ ω, |G ω| ≤ ‖dBC‖ := by
```

## Locale
Prefer American English spellings.
