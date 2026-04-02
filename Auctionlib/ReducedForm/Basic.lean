module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! # Reduced Form — Per-Bidder Interim View -/

@[expose] public section

open Set

/-- The per-bidder interim reduced form of an auction.

`winProb(bid)` is the interim winning probability, `cost(bid)` is the
interim expected payment, and `strategy` maps types to bids.
The interim payoff is `π(v, bid) = v · winProb(bid) - cost(bid)`. -/
structure ReducedForm where
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

namespace ReducedForm

variable (R : ReducedForm)

/-- The type interval `[lowestType, highestType]`. -/
abbrev typeInterval : Set ℝ := Icc R.lowestType R.highestType

/-! ### Derived quantities -/

def payoff (v bid : ℝ) : ℝ := v * R.winProb bid - R.cost bid
def q : ℝ → ℝ := R.winProb ∘ R.strategy
def U (v : ℝ) : ℝ := R.payoff v (R.strategy v)

@[simp] lemma payoff_eq (v bid : ℝ) :
    R.payoff v bid = v * R.winProb bid - R.cost bid := rfl
@[simp] lemma q_eq (v : ℝ) : R.q v = R.winProb (R.strategy v) := rfl
@[simp] lemma U_eq (v : ℝ) :
    R.U v = v * R.winProb (R.strategy v) - R.cost (R.strategy v) := rfl

lemma q_range (v : ℝ) : R.q v ∈ Icc 0 1 := R.winProb_range (R.strategy v)

/-! ### Regular equilibrium -/

class IsRegular (R : ReducedForm) : Prop where
  winProb_mono : Monotone R.winProb
  strategy_mono : MonotoneOn R.strategy R.typeInterval
  strategy_nonneg : ∀ v ∈ R.typeInterval, 0 ≤ R.strategy v
  cost_continuous : Continuous R.cost

end ReducedForm

end
