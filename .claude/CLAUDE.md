This is Lean4 project (lean-4.28.0) to formalize theorems in auction theory. The main mathematical reference is located is `documents/Auto_Formalizing_AuctionsFeb16_2026`.

To achieve good formalization, we try to split the argument into two parts, the "mathematcis" and the "econimics".

The mathematical part is the core idea involving analysis, combinatorics etc. Then we just "specialize" the mathematical version to achieve the theorem we want.

Task: 
- [x] formalize ‹The Envelop Theorem› in section 5.1.
- [x] formalize ‹Myerson's Lemma› in section 5.2
- [x] formalize ‹Revenue Equivalence Theorem› in section 5.3
- [ ] formalize game theoretic concepts in section 3

## Useful Lean commands

- `#min_imports`: suggests minimal imports to replace `import Mathlib`. Note: this command may suggest imports that do not actually compile.

## Useful lake commands

- `lake exe mk_all --lib Auctionlib --git`: regenerate `Auctionlib.lean` with all imports, using git to determine which files to include (respects `.gitignore`, so e.g. the Playground folder is excluded).

## Some Lean4 Requirement and Tips

- `native_decide` tactic is **STRICTLY NOT ALLOWED**
- variable naming should follow mathlib naming conventions
- Grepping in the project root folder's `.lake` subfolder is good idea as it contains a copy of `mathlib` we are using