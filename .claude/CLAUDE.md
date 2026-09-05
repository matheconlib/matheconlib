This is Lean4 project (lean-4.28.0) to formalize theorems in auction theory. The main mathematical reference are located `documents/` folder.

## Architecture

Three-layer design following the mathematical reference (Section 2-3):

1. **Mechanism** (`Mechanism/Core/`): `Auctionlib.Mechanism.Mechanism I A O` stores an outcome rule and signed transfers (positive to the agent). Carriers are explicit; payment is negative transfer. Environments and deterministic solution predicates are prior-free.
2. **Auction** (`Auction/`): mechanism + probabilistic environment (`θ`, `θmin`, `θmax`) on probability space `(Ω, ℙ)` (Section 3a+3b)
3. **BidderProblem** (`BidderProblem/`): per-bidder interim view (`winProb`, `cost`, `strategy`) with IC typeclass chain

Flow: `Auction → toBidderProblem halloc → BidderProblem` (BIC → HasTypeDeviationIC → HasEnvelopeIC → envelope theorem). Allocation bounds are an explicit `IsValidAllocation` proof.

Strategy-dependent interim quantities use the coordinate of `rules.outcome` and the canonical `rules.payment` (negative transfer). Standard `q`/`p` are the `σ = id` case. All-purchase calculations receive an explicit `AllPurchaseSpec` for selected price/scarcity data and its `payment_eq` identity. Under linear scarcity, `LinearScarcityAuction.toQuadraticCostProblem` uses `A.spec` and proves the quadratic cost form.

Mechanism properties are ordinary propositions. `UsesStrictHighestBidAllocation` preserves the old rule that tied highest bids allocate nothing; it is distinct from environment-relative welfare efficiency. `AllPurchaseSpec` carries selected data, while `IsAllPurchase` is its `Nonempty` predicate. Neither is a typeclass.

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
- [x] formalize ‹All-Purchase Auction› economic analysis (section 6.7)
  - [x] Proposition 6.10 — revenue decomposition
  - [x] Corollary 6.11 — bundled vs standalone revenue comparison
  - [x] Proposition 6.12 — optimal pricing (interior regime)
  - [x] Proposition 6.13 — welfare decomposition (Cournot + contest losses)
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
