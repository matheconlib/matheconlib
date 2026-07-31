module

public import Auctionlib.SingleParameter.Basic
import Mathlib.Tactic.Linarith

/-!
# Incentive Compatibility for Single-Parameter Problems

This file defines three levels of incentive compatibility for a
`SingleParameterProblem`.

From weakest to strongest, they are:

1. `HasEnvelopeIC`: a comparison between the utilities and allocations of two
   types;
2. `HasTypeDeviationIC`: each type prefers its own strategy action to the
   action assigned to any other type;
3. `HasUniversalIC`: each type prefers its own strategy action to every
   feasible action.

The corresponding implication chain is

`HasUniversalIC → HasTypeDeviationIC → HasEnvelopeIC`.

This file also defines participation predicates. Participation is kept
separate from incentive compatibility: IC compares available actions, while
participation compares the resulting utility with an outside option.
-/

@[expose] public section

open Set

universe u

namespace SingleParameterProblem

variable {Action : Type u} (P : SingleParameterProblem Action)

/-! ## Incentive compatibility -/

/-- **Envelope incentive compatibility** compares two types `v` and `v'`.

The inequality says that the utility difference between the types is at least
the type difference multiplied by the allocation assigned to `v'`.

This is the weakest IC condition used by the single-parameter development. -/
class HasEnvelopeIC (P : SingleParameterProblem Action) : Prop where
  envelopeIC : ∀ v ∈ P.typeInterval, ∀ v' ∈ P.typeInterval,
    (v - v') * P.q v' ≤ P.U v - P.U v'

/-- **Type-deviation incentive compatibility** says that type `v` weakly
prefers its own strategy action to the strategy action assigned to any other
type `v'`. -/
class HasTypeDeviationIC (P : SingleParameterProblem Action) : Prop where
  typeDeviationIC : ∀ v ∈ P.typeInterval, ∀ v' ∈ P.typeInterval,
    P.payoff v (P.strategy v') ≤ P.payoff v (P.strategy v)

/-- **Universal incentive compatibility** says that type `v` weakly prefers
its own strategy action to every action in the feasible set `S`.

The `outParam` annotation allows typeclass search to infer `S` from an
available `HasUniversalIC` instance. -/
class HasUniversalIC
    (P : SingleParameterProblem Action) (S : outParam (Set Action)) : Prop where
  /-- The strategy chooses a feasible action for every type in the interval. -/
  strategyInS : ∀ v ∈ P.typeInterval, P.strategy v ∈ S
  /-- No feasible action gives a type more utility than its strategy action. -/
  universalIC : ∀ v ∈ P.typeInterval, ∀ a ∈ S,
    P.payoff v a ≤ P.payoff v (P.strategy v)

/-! ## The IC implication chain -/

/-- Type-deviation IC implies envelope IC. -/
instance instHasEnvelopeICOfHasTypeDeviationIC
    {P : SingleParameterProblem Action} [hIC : HasTypeDeviationIC P] :
    HasEnvelopeIC P where
  envelopeIC v hv v' hv' := by
    have h := hIC.typeDeviationIC v hv v' hv'
    simp only [payoff, q, U] at h ⊢
    linarith

/-- Universal IC implies type-deviation IC because the strategy action of any
other type is one of the feasible actions. -/
instance instHasTypeDeviationICOfHasUniversalIC
    {P : SingleParameterProblem Action} {S : Set Action}
    [hIC : HasUniversalIC P S] :
    HasTypeDeviationIC P where
  typeDeviationIC v hv v' hv' :=
    hIC.universalIC v hv (P.strategy v') (hIC.strategyInS v' hv')

/-! ## Participation -/

/-- The problem satisfies the participation constraint described by
`outsideOption` if every type in the type interval receives at least its
outside-option utility.

The outside option may depend on the agent's type. -/
def SatisfiesParticipation (outsideOption : ℝ → ℝ) : Prop :=
  ∀ v ∈ P.typeInterval, outsideOption v ≤ P.U v

/-- **Individual rationality** with the standard normalization that every
type has outside-option utility zero. -/
def IsIndividuallyRational : Prop :=
  P.SatisfiesParticipation (fun _ => 0)

/-- The lowest type receives utility zero.

This is stronger than individual rationality for the lowest type: it says that
the participation constraint binds there, not merely that utility is
nonnegative. -/
def HasZeroLowestTypeUtility : Prop :=
  P.U P.lowestType = 0

end SingleParameterProblem

end
