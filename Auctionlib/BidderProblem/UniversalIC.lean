module

public import Auctionlib.BidderProblem.TypeDeviationIC

/-!
# Universal IC (Level 2)

`HasUniversalIC B S` is the strongest IC: type `v` weakly prefers `strategy(v)` to
every bid in the feasible set `S`.

## Instance chain

An instance `HasUniversalIC B S → HasTypeDeviationIC B` is provided, so all
type-deviation IC results (Myerson's lemma) and envelope theorem results are
automatically available.

## Note on strict monotonicity

Strict monotonicity of the equilibrium strategy (Lemma 6.2) requires
distributional structure (CDF, density, number of bidders) beyond what
`BidderProblem` captures.  This is proved at the `Auction` level, which has
access to the probability space and type distribution.
-/

@[expose] public section

open Set

namespace BidderProblem

variable (B : BidderProblem)

/-- **Universal IC** (Level 2): type `v` weakly prefers `strategy(v)` to every
bid in the feasible set `S`.  `S` is an `outParam` so that instance resolution
can find it. -/
class HasUniversalIC (B : BidderProblem) (S : outParam (Set ℝ)) : Prop where
  strategyInS : ∀ v ∈ B.typeInterval, B.strategy v ∈ S
  universalIC : ∀ v ∈ B.typeInterval, ∀ bid ∈ S,
    B.payoff v bid ≤ B.payoff v (B.strategy v)

/-! ### Instance: Level 2 → Level 1 -/

instance {B : BidderProblem} {S : Set ℝ} [h : HasUniversalIC B S] :
    HasTypeDeviationIC B where
  typeDeviationIC v hv v' hv' :=
    h.universalIC v hv (B.strategy v') (h.strategyInS v' hv')

end BidderProblem

end
