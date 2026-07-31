module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Auctionlib.SingleParameter.Basic

/-! # BidderProblem — Per-Bidder Interim View -/

@[expose] public section

open Set

/-- The per-bidder interim view of an auction.

`winProb(bid)` is the interim winning probability, `cost(bid)` is the
interim expected payment, and `strategy` maps types to bids.
The interim payoff is `π(v, bid) = v · winProb(bid) - cost(bid)`. -/
structure BidderProblem where
  /-- lower bound of type space -/
  lowestType : ℝ
  /-- upper bound of type space -/
  highestType : ℝ
  /-- winning/allocation probability as a function of bid -/
  winProb : ℝ → ℝ
  /-- winning probability takes values in `[0, 1]` -/
  winProb_range : ∀ x, winProb x ∈ Icc 0 1
  /-- cost/expenditure as a function of bid -/
  cost : ℝ → ℝ
  /-- equilibrium bidding strategy: maps types to bids -/
  strategy : ℝ → ℝ

namespace BidderProblem

variable (B : BidderProblem)

/-- The type interval `[lowestType, highestType]`. -/
abbrev typeInterval : Set ℝ := Icc B.lowestType B.highestType

/-! ### Derived quantities -/

def payoff (v bid : ℝ) : ℝ := v * B.winProb bid - B.cost bid
def q : ℝ → ℝ := B.winProb ∘ B.strategy
def U (v : ℝ) : ℝ := B.payoff v (B.strategy v)

@[simp] lemma payoff_eq (v bid : ℝ) :
    B.payoff v bid = v * B.winProb bid - B.cost bid := rfl
@[simp] lemma q_eq (v : ℝ) : B.q v = B.winProb (B.strategy v) := rfl
@[simp] lemma U_eq (v : ℝ) :
    B.U v = v * B.winProb (B.strategy v) - B.cost (B.strategy v) := rfl

lemma q_range (v : ℝ) : B.q v ∈ Icc 0 1 := B.winProb_range (B.strategy v)

/-! ### Compatibility with the general single-parameter model -/

/-- Regard a bidder's real-valued bid as the action in a
`SingleParameterProblem`.

This conversion changes no mathematical data:

* `winProb` becomes the general allocation rule;
* `cost` becomes the general payment rule;
* the type bounds and strategy are unchanged.
-/
def toSingleParameterProblem : SingleParameterProblem ℝ where
  lowestType := B.lowestType
  highestType := B.highestType
  allocation := B.winProb
  allocation_range := B.winProb_range
  payment := B.cost
  strategy := B.strategy

@[simp]
lemma toSingleParameterProblem_lowestType :
    B.toSingleParameterProblem.lowestType = B.lowestType :=
  rfl

@[simp]
lemma toSingleParameterProblem_highestType :
    B.toSingleParameterProblem.highestType = B.highestType :=
  rfl

@[simp]
lemma toSingleParameterProblem_allocation (bid : ℝ) :
    B.toSingleParameterProblem.allocation bid = B.winProb bid :=
  rfl

@[simp]
lemma toSingleParameterProblem_payment (bid : ℝ) :
    B.toSingleParameterProblem.payment bid = B.cost bid :=
  rfl

@[simp]
lemma toSingleParameterProblem_strategy (v : ℝ) :
    B.toSingleParameterProblem.strategy v = B.strategy v :=
  rfl

@[simp]
lemma toSingleParameterProblem_typeInterval :
    B.toSingleParameterProblem.typeInterval = B.typeInterval :=
  rfl

@[simp]
lemma toSingleParameterProblem_payoff (v bid : ℝ) :
    B.toSingleParameterProblem.payoff v bid = B.payoff v bid :=
  rfl

@[simp]
lemma toSingleParameterProblem_q (v : ℝ) :
    B.toSingleParameterProblem.q v = B.q v :=
  rfl

@[simp]
lemma toSingleParameterProblem_U (v : ℝ) :
    B.toSingleParameterProblem.U v = B.U v :=
  rfl

/-! ### Regular equilibrium -/

class IsRegular (B : BidderProblem) : Prop where
  winProb_mono : Monotone B.winProb
  strategy_mono : MonotoneOn B.strategy B.typeInterval
  strategy_nonneg : ∀ v ∈ B.typeInterval, 0 ≤ B.strategy v
  cost_continuous : Continuous B.cost

end BidderProblem

end
