This is Lean4 project (lean-4.28.0) to formalize theorems in auction theory. The main mathematical reference are located `documents/` folder.

To achieve good formalization, we try to split the argument into two parts, the "mathematcis" and the "econimics".

The mathematical part is the core idea involving analysis, combinatorics etc. Then we just "specialize" the mathematical version to achieve the theorem we want.

Task:
- [x] formalize ‹The Envelope Theorem› in section 5.1
- [x] formalize ‹Myerson's Lemma› in section 5.2
- [x] formalize ‹Revenue Equivalence Theorem› in section 5.3
  - [x] generalize: `payment_equivalence` in `Envelope/Theorem.lean` (no efficiency/symmetry/distributional assumptions)
  - [x] generalize: `revenue_equivalence` no longer requires efficiency; uses general `payment_equivalence`
  - [x] refactor: `Efficient` is now a separate predicate, not baked into `RevenueEquivalenceSetup`
- [x] formalize ‹All-Purchase Auction› in chapter 6
  - [x] Lemma 6.1 — weak monotonicity (`AllPurchase/Monotonicity.lean`)
  - [x] Lemma 6.2 — strict monotonicity (`AllPurchase/StrictMonotonicity.lean`)
  - [x] Lemma 6.3 — envelope / integral representation (`AllPurchase/Envelope.lean`)
  - [x] Proposition 6.4 — net payment identity (`AllPurchase/NetPayment.lean`)
- [ ] formalize game theoretic concepts in section 3

## Useful Lean commands

- `#min_imports`: suggests minimal imports to replace `import Mathlib`. Note: this command may suggest imports that do not actually compile.

## Useful lake commands

- `lake exe mk_all --lib Auctionlib --git`: regenerate `Auctionlib.lean` with all imports, using git to determine which files to include (respects `.gitignore`, so e.g. the Playground folder is excluded).
- `lake build`: build the whole project, should be run after `lake exe mk_all --lib Auctionlib --git` to
ensure all relevant files would be built.

## Some Lean4 Requirement and Tips

- `native_decide` tactic is **STRICTLY NOT ALLOWED**
- variable naming should follow mathlib naming conventions
- Grepping in the project root folder's `.lake` subfolder is good idea as it contains a copy of `mathlib` we are using