# Schauder review: stage 1

Issue: [#191](https://github.com/matheconlib/matheconlib/issues/191).
Baseline: `6c0e61ed4c95252e2c985ccc456e2c53617fb941`,
`MathEconLib/ForMathlib/Schauder.lean`, lines 55–1087.
Lean 4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

This records Codex's statement/proof review and a second adversarial pass over the
39 declarations below. Maintainer review of the proposed changes remains pending.
The later sections, starting at `ordMin`, remain unreviewed under #191.

The mathematical reference is Nikolai V. Ivanov, *Beyond Sperner's lemma*,
[arXiv:1902.00827v2](https://arxiv.org/html/1902.00827v2), Section 1:
dominant sets, cells/rooms/doors, and Lemmas 2, 4, 6 and 7. The Lean graph
keeps colorful rooms and rooms/doors of one distinguished missing-color type.
The three definitions agree with that restriction. For nonempty `σ`, the
dominance predicate expresses the minimum-based condition without choosing minima;
for empty `σ` and nonempty `C`, it holds as required.

## Findings and changes

- Enabling the five suppressed linters exposed 16 warnings: nine unnecessary
  `Fintype` binders, five unnecessary `DecidableEq` binders, one blanket
  `open Classical`, and one use of `show` to change a goal. These are fixed.
  Only private helper types lose binders. Definitions, conclusions and the three
  public declarations are preserved.
- Several docstrings were misleading. The comment attached to `card_erase_ne'`
  described an entire neighbor-uniqueness argument. The injective-case comment
  incorrectly claimed `σ.image c ⊆ C` and cited a nonexistent helper. Other
  comments obscured the actual cardinality argument or assumed nonemptiness not
  needed by their lemma. These now describe the proofs they accompany.
- `isDominant_mono_C` duplicated `isDominant_mono`; its proof now uses that lemma.
  A redundant nested contradiction in `caseB_impossible'` is removed.

Classical reasoning is local to proofs. The seven graph-degree statements use
`open Classical in` because their types need a finite enumeration of the neighbor
set. The graph-degree API already provides
`SimpleGraph.degree_eq_one_iff_existsUnique_adj`; the local proof uses it.
Mathlib's `Finset.image_erase` requires global injectivity, while the reviewed
helper only assumes injectivity on the particular finset, so that helper remains.

All five linters are explicitly enabled through `scarf_degree_outside_door`.
Their temporary suppressions and the blanket `open Classical` begin only after
that proof, immediately before the unreviewed `ordMin` section. No helper is
exported and no upstream contribution is included.

## Declaration checklist

All entries were retained and checked in both passes. Locations are baseline lines.

| Line | Declaration | Checked argument |
|---|---|---|
| 55 | `isDominant` | Quantifiers require one witnessing order for each `y`; all points of `σ` must block that `y`. |
| 62 | `scarfAdjRel` | Symmetric room/door incidence; erasure requires membership, insertion requires nonmembership, and equal pairs are excluded. |
| 78 | `IsScarfVtx` | Nonempty color set, dominance, and the three intended cardinality/color cases. |
| 86 | `isDominant_erase` | Restrict the universal condition to a smaller finset. |
| 97 | `image_erase_of_injOn` | A surviving preimage cannot map to the erased image under local injectivity; conversely every other image has a surviving preimage. |
| 108 | `colorful_room_unique_adj_mem` | Equal image/cardinality gives injectivity; erase the unique point colored `i₀`. Other erasures, insertions and reverse incidences are excluded. |
| 193 | `isDominant_mono` | The same witnessing order belongs to the larger color set. |
| 210 | `adj_insert_of_not_mem` | Insertion changes the color set and satisfies the forward incidence branch. |
| 230 | `isScarfVtx_insert_of_not_mem` | Inserted color gives nonemptiness; dominance persists and exactly `i₀` is missing. |
| 241 | `colorful_room_unique_adj_not_mem` | The only allowed neighbor inserts `i₀`; an erasure would instead lose a color already in `C`. |
| 296 | `colorful_room_unique_adj` | Exhaustive split on membership of `i₀` in `C`. |
| 308 | `degree_one_of_unique_adj_raw` | Lift unique raw neighbors into the vertex subtype and apply Mathlib's degree-one criterion. |
| 323 | `scarf_degree_colorful_room` | Apply the unique-neighbor result using the vertex's dominance/nonemptiness. |
| 337 | `nearly_colorful_image_card_cases` | One missing color bounds the image size below by `|C|−1`; image size is at most `|σ|=|C|`. |
| 349 | `scarf_degree_of_two_adj_pairs` | The neighbor finset consists of exactly two distinct subtype vertices. |
| 377 | `erase_image_eq_of_duplicate` | The distinct point `y` preserves the erased point's color. |
| 393 | `collision_with_uniqueness` | Image deficit one yields a collision; erasing one colliding point leaves an injective restriction, excluding a third equal-colored point. |
| 432 | `noninjective_pair_exists` | Apply that collision result and preserve the image under either erasure. |
| 453 | `image_subset_of_sdiff_singleton` | The intersection has the image's full cardinality, so it equals the image. |
| 473 | `not_scarf_erase_non_colliding_1` | Erasing a unique color adds a second missing color distinct from `i₀`. |
| 487 | `not_scarf_insert_form` | A color outside `C` is also outside the image; inserting it leaves two missing colors. |
| 523 | `card_erase_ne'` | Membership makes erasure decrease cardinality strictly. |
| 529 | `image_card_eq'` | For an image contained in `C`, singleton difference gives deficit one. |
| 538 | `image_erase_eq_of_cover'` | A surviving point covers the erased point's color. |
| 544 | `cz_unique'` | Another collision away from `x,y` would contradict injectivity after erasing that point. |
| 571 | `not_scarf_vtx_erase_non_colliding'` | Cardinality excludes room cases; the extra missing color excludes the door case. |
| 592 | `caseB_impossible'` | A room cannot itself be obtained as a door of another room: both incidence forms change cardinality by one. |
| 603 | `ncr_noninjective_uniqueness` | Only the two colliding points can be erased; insertions and reverse incidence are excluded. |
| 636 | `ncr_noninjective_two_adj_pairs` | Both erasures are dominant Scarf vertices, distinct and adjacent, and exhaust all neighbors. |
| 677 | `scarf_degree_ncr_case_noninjective` | Transfer those two neighbors to the subtype graph. |
| 706 | `ncr_injective_unique_y` | Equal cardinalities and one missing color yield exactly one image color outside `C`; injectivity identifies its unique point. |
| 752 | `isDominant_mono_C` | Same monotonicity with reordered arguments; now reuses the earlier lemma. |
| 782 | `ncr_injective_uniqueness` | Erase the unique outside-colored point or insert its color; every other edit loses the required color condition. |
| 870 | `ncr_injective_p1_isScarfVtx` | Erasing that point preserves dominance and the missing color, with door cardinality. |
| 894 | `ncr_injective_p2_isScarfVtx` | Inserting its color preserves dominance and the missing color, with door cardinality. |
| 909 | `ncr_injective_two_adj_pairs` | Construct both distinct neighbors and apply the uniqueness argument. |
| 950 | `scarf_degree_ncr_case_injective` | Transfer the injective-case neighbors to the subtype graph. |
| 967 | `scarf_degree_nearly_colorful_room` | The two image-cardinality cases exhaust the possibilities. |
| 982 | `scarf_degree_outside_door` | An empty door has color set `{i₀}`; neighbors must be singleton rooms whose point is maximal in order `i₀`. Finiteness/nonemptiness supply that unique maximum. |

## Adversarial checks

Checked both directions of incidence, empty/singleton finsets, one available
color (`n = 0`), distinctness of the two neighbors, and both coloring cases.
The outside-door proof genuinely needs finite nonempty `T`; finiteness is retained
there and in graph-degree types. An empty color set is excluded by `IsScarfVtx`.
If `T` is empty, dominance alone can be vacuous; it must not be treated as proving
that a Scarf room or a maximum exists.

The image need not be contained in `C` in the injective case: take one point
colored `1`, `C = {0}`, and `i₀ = 0`. The cardinalities agree and exactly `0` is
missing. The corrected proof documentation handles this case. In the noninjective
case, two independent colliding pairs would give image deficit at least two,
so they cannot satisfy the deficit-one hypothesis used by `cz_unique'`.

No incorrect definition, false statement or proof gap was found in this stage.
That conclusion covers these declarations only. The remaining Schauder proof and
its historical linter findings still need the later stages of #191.

## Verification

The first section compiles with warnings treated as errors: **16 exposed linter
warnings before cleanup, zero afterward**. The original section fails that same
strict check, providing a negative control. To reproduce the section check:

```sh
mkdir -p .lake/schauder-review
sed '/^-- Later stages of #191/,$d' MathEconLib/ForMathlib/Schauder.lean \
  > .lake/schauder-review/ScarfRooms.lean
printf '\nend\n' >> .lake/schauder-review/ScarfRooms.lean
lake env lean -DwarningAsError=true .lake/schauder-review/ScarfRooms.lean
```

The full default build passed **9,220 jobs**, including API pins, Kakutani/Nash,
tests and examples, from a checkout with no project build cache. Only the pinned
dependency cache was reused. Execution was in a nonroot container without
network, host mounts, credentials or added capabilities. The build still emits
118 existing warnings elsewhere in the file/project; they remain later work.
The source from the `ordMin` docstring onward is byte-for-byte unchanged from
the baseline, as are all three initial definitions.

Integration commands are `bash scripts/update-imports.sh`,
`bash scripts/check-headers.sh`, `lake --rehash --no-ansi build`, and
`python3 scripts/check-proof-integrity.py`. The last command checks all project
sources, compiled private declarations and retained anonymous proofs. Its complete
report is `.lake/proof-integrity/report.json`, also saved by required PR CI as the
`proof-integrity` artifact. The PR records the final audit result and tested revision.
