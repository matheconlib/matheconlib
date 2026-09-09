module

public import Auctionlib.SingleParameter.IC

/-!
# The Revelation Principle for Single-Parameter Problems

This file states the single-agent revelation principle on top of the
canonical reduced form `SingleParameterProblem.reduce`
(Hartline, *Mechanism Design and Approximation*, Theorem 2.11, single-agent
specialization).

A `SingleParameterProblem` bundles the rules of a choice problem — an
allocation and a payment as functions of an arbitrary action — with a
strategy mapping types to actions. The reduced form absorbs the strategy into
the rules: a reduced action is a reported type, the rules simulate the
strategy on the report, and truthful behavior is the identity strategy.

## Main definitions and results

* `SingleParameterProblem.IsDirect`: a real-action problem is *direct* when
  actions are interpreted as reported types and its strategy is truthful
  reporting, i.e. the identity.
* `SingleParameterProblem.instHasUniversalICReduce`: if the original strategy
  is type-deviation incentive compatible, then in the reduced problem
  truthful reporting is universally incentive compatible over all
  in-interval reports.
* `SingleParameterProblem.revelation_principle`: the headline existence
  statement. Every type-deviation IC problem is implemented by a direct
  problem — its reduced form — in which truth-telling is incentive
  compatible and which preserves the type interval, the induced allocation,
  the on-strategy payment, and the utility.
* `SingleParameterProblem.reduce_isIndividuallyRational`,
  `SingleParameterProblem.reduce_hasZeroLowestTypeUtility`: participation
  transfers to the reduced form.

The transfers of envelope and type-deviation IC between a problem and its
reduced form are provided by `Auctionlib.SingleParameter.IC`. The multi-agent
Bayesian version of the revelation principle is in
`Auctionlib.Auction.Revelation`.
-/

@[expose] public section

open Set

universe u

namespace SingleParameterProblem

variable {Action : Type u} (P : SingleParameterProblem Action)

/-! ## Direct problems -/

/-- A real-action problem is **direct** when its actions are interpreted as
reported types and its strategy is truthful reporting, i.e. the identity. -/
def IsDirect (D : SingleParameterProblem ℝ) : Prop :=
  D.strategy = id

/-- The reduced form of any problem is direct. -/
theorem reduce_isDirect : P.reduce.IsDirect :=
  rfl

/-- Reduction is idempotent: the reduced form of a reduced problem is
itself. -/
theorem reduce_reduce : P.reduce.reduce = P.reduce :=
  rfl

/-! ## Truthfulness of the reduced form -/

/-- **Truthfulness of the reduced form.** If the original strategy is
type-deviation incentive compatible, then in the reduced problem no
in-interval type prefers any in-interval report to truthful reporting.

Formally, this is universal IC of `P.reduce` with the type interval as the
set of feasible reports. -/
instance instHasUniversalICReduce
    {P : SingleParameterProblem Action} [hIC : HasTypeDeviationIC P] :
    HasUniversalIC P.reduce P.typeInterval where
  strategyInS _ hv := hv
  universalIC v hv w hw := hIC.typeDeviationIC v hv w hw

/-! ## Preservation of participation -/

/-- Reduction preserves individual rationality. -/
theorem reduce_isIndividuallyRational (h : P.IsIndividuallyRational) :
    P.reduce.IsIndividuallyRational :=
  h

/-- Reduction preserves the binding participation constraint at the lowest
type. -/
theorem reduce_hasZeroLowestTypeUtility (h : P.HasZeroLowestTypeUtility) :
    P.reduce.HasZeroLowestTypeUtility :=
  h

/-! ## The revelation principle -/

/-- **The revelation principle**.

Every single-parameter problem whose strategy is type-deviation incentive
compatible is implemented by a *direct* problem — concretely, its canonical
reduced form — such that:

1. the strategy is truthful reporting;
2. truthful reporting is universally incentive compatible over in-interval
   reports;
3. the type interval is unchanged;
4. the induced allocation `q` and the utility `U` are unchanged;
5. the payment collected at report `w` is the payment the original rules
   collect at the action `strategy w`. -/
theorem revelation_principle [HasTypeDeviationIC P] :
    ∃ D : SingleParameterProblem ℝ,
      D.IsDirect ∧
      HasUniversalIC D D.typeInterval ∧
      D.lowestType = P.lowestType ∧
      D.highestType = P.highestType ∧
      D.q = P.q ∧
      D.U = P.U ∧
      ∀ w : ℝ, D.payment w = P.payment (P.strategy w) :=
  ⟨P.reduce, P.reduce_isDirect, instHasUniversalICReduce, rfl, rfl,
    P.reduce_q, P.reduce_U, fun _ => rfl⟩

end SingleParameterProblem

end
