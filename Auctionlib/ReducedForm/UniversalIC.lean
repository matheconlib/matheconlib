module

public import Auctionlib.ReducedForm.TypeDeviationIC

/-!
# Universal IC (Level 2)

`HasUniversalIC R S` is the strongest IC: type `v` weakly prefers `strategy(v)` to
every bid in the feasible set `S`.

## Instance chain

An instance `HasUniversalIC R S → HasTypeDeviationIC M` is provided, so all
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

namespace ReducedForm

variable (R : ReducedForm)

/-- **Universal IC** (Level 2): type `v` weakly prefers `strategy(v)` to every
bid in the feasible set `S`.  `S` is an `outParam` so that instance resolution
can find it. -/
class HasUniversalIC (R : ReducedForm) (S : outParam (Set ℝ)) : Prop where
  strategyInS : ∀ v ∈ R.typeInterval, R.strategy v ∈ S
  universalIC : ∀ v ∈ R.typeInterval, ∀ bid ∈ S,
    R.payoff v bid ≤ R.payoff v (R.strategy v)

/-! ### Instance: Level 2 → Level 1 -/

instance {R : ReducedForm} {S : Set ℝ} [h : HasUniversalIC R S] :
    HasTypeDeviationIC R where
  typeDeviationIC v hv v' hv' :=
    h.universalIC v hv (R.strategy v') (h.strategyInS v' hv')

end ReducedForm

end
