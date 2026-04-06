This is Lean4 project (lean-4.28.0) to formalize theorems in auction theory. The main mathematical reference are located `documents/` folder.

## Architecture

Three-layer design following the mathematical reference (Section 2-3):

1. **Mechanism** (`Mechanism/Basic.lean`): allocation rule `x` + payment rule `t` over bid vectors (the rules of the game, Section 3b)
2. **Auction** (`Auction/`): mechanism + probabilistic environment (`θ`, `θmin`, `θmax`) on probability space `(Ω, ℙ)` (Section 3a+3b)
3. **BidderProblem** (`BidderProblem/`): per-bidder interim view (`winProb`, `cost`, `strategy`) with IC typeclass chain

Flow: `Auction → toBidderProblem → BidderProblem` (BIC → HasTypeDeviationIC → HasEnvelopeIC → envelope theorem)

Strategy-dependent interim quantities: `q_strat σ i b = 𝔼[xᵢ(b, σ(θ₋ᵢ))]`, `p_strat σ i b = 𝔼[tᵢ(b, σ(θ₋ᵢ))]`. Standard `q`/`p` are the `σ = id` case. For the all-purchase auction, `toAllPurchaseBidderProblem` derives `winProb` from `q_strat` (via `x_eq`) and `cost` from `allPurchaseNetCost` (via `t_eq`). Under linear scarcity, `LinearScarcityAuction.toQuadraticCostProblem` extends this with the quadratic cost proof.

Typeclasses on Mechanism: `IsAllPurchase` (posted price + scarcity function + `x_eq`/`t_eq`, derives `hasValidAllocation`)

Typeclasses on Auction: `HasIndependentTypes`, `HasIdenticalTypes`, `HasBoundedTypes`, `HasDensity`, `HasAtomlessTypes`, `IsSymmetricIPV` (bundle), `HasPosDensity`

Typeclasses on BidderProblem: `HasEnvelopeIC`, `HasTypeDeviationIC`, `HasUniversalIC`, `IsRegular`, `IsBoundaryRegime`

Structures for parametric families:
- `LinearScarcityAuction` extends `Auction`: all-purchase auction with linear scarcity `φ(B) = φ̄ − αB`
- `QuadraticCostProblem` extends `BidderProblem`: cost is `α·b² + K·b`
- `LinearCostProblem` extends `BidderProblem`: cost is `p_net·b`
- `InteriorRegimeProblem` extends `QuadraticCostProblem`: `K < 0`, `U(lowestType) = K²/(4α)`

## Task status

- [x] formalize ‹The Envelope Theorem› in section 5.1
- [x] formalize ‹Myerson's Lemma› in section 5.2
- [x] formalize ‹Revenue Equivalence Theorem› in section 5.3
- [x] formalize ‹All-Purchase Auction› equilibrium characterization (chapter 6)
  - [x] Lemma 6.1 — weak monotonicity
  - [x] Lemma 6.2 — strict monotonicity
  - [x] Lemma 6.3 — envelope / integral representation
  - [x] Proposition 6.4 — net payment identity
- [x] formalize ‹All-Purchase Auction› baseline demand & explicit solutions (chapter 6)
- [ ] formalize ‹All-Purchase Auction› economic analysis (section 6.7) — descoped: raw-ℝ versions deleted; needs redo connected to Auction/BidderProblem structures
  - [ ] Proposition 6.10 — revenue decomposition
  - [ ] Corollary 6.11 — bundled vs standalone revenue comparison
  - [ ] Proposition 6.12 — optimal pricing (interior regime)
  - [ ] Proposition 6.13 — welfare decomposition (Cournot + contest losses)
- [ ] formalize game theoretic concepts in section 3
- [x] delete old framework files (`Envelope/`, `AllPurchase/`, `RevenueEquivalence/` using old structures)

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
