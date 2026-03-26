module

public import Auctionlib.Mechanism.TypeDeviationIC

/-!
# Universal IC (Level 2)

`HasUniversalIC M S` is the strongest IC: type `v` weakly prefers `strategy(v)` to
every bid in the feasible set `S`.

## Instance chain

An instance `HasUniversalIC M S → HasTypeDeviationIC M` is provided, so all
type-deviation IC results (Myerson's lemma) and envelope theorem results are
automatically available.

## Note on strict monotonicity

Strict monotonicity of the equilibrium strategy (Lemma 6.2) requires
distributional structure (CDF, density, number of bidders) beyond what
`Mechanism` captures.  This is proved at the `Auction` level, which has
access to the probability space and type distribution.
-/

@[expose] public section

open Set

namespace Mechanism

variable (M : Mechanism)

/-- **Universal IC** (Level 2): type `v` weakly prefers `strategy(v)` to every
bid in the feasible set `S`.  `S` is an `outParam` so that instance resolution
can find it. -/
class HasUniversalIC (M : Mechanism) (S : outParam (Set ℝ)) : Prop where
  strategyInS : ∀ v ∈ M.typeInterval, M.strategy v ∈ S
  universalIC : ∀ v ∈ M.typeInterval, ∀ bid ∈ S,
    M.payoff v bid ≤ M.payoff v (M.strategy v)

/-! ### Instance: Level 2 → Level 1 -/

instance {M : Mechanism} {S : Set ℝ} [h : HasUniversalIC M S] :
    HasTypeDeviationIC M where
  typeDeviationIC v hv v' hv' :=
    h.universalIC v hv (M.strategy v') (h.strategyInS v' hv')

end Mechanism

end
