module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# General Mechanism — Structure and Derived Quantities

This file defines `Mechanism`, the single type for all single-item auction mechanisms
with quasi-linear payoffs:

  `π(v, bid) = v · winProb(bid) - cost(bid)`

## Auction formats as special cases

| Auction        | `winProb(bid)` | `cost(bid)`           |
|----------------|----------------|-----------------------|
| All-purchase   | `G(bid)`       | `C(bid)`              |
| First-price    | `G(bid)`       | `bid · G(bid)`        |
| All-pay        | `G(bid)`       | `bid`                 |
| Second-price   | `G(bid)`       | `E[payment ∣ bid]`    |
-/

@[expose] public section

open Set

/-- A single-crossing mechanism with quasi-linear payoffs.

A bidder with type `v ∈ [lowestType, highestType]` uses `strategy`,
experiences winning component `winProb(bid)` and cost component `cost(bid)`.
The interim payoff is `π(v, bid) = v · winProb(bid) - cost(bid)`.

This captures every standard single-item IPV auction format. -/
structure Mechanism where
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

namespace Mechanism

variable (M : Mechanism)

/-- The type interval `[lowestType, highestType]`. -/
abbrev typeInterval : Set ℝ := Icc M.lowestType M.highestType

/-! ### Derived quantities -/

/-- Interim payoff for type `v` choosing bid `bid`:
`payoff v bid = v · winProb(bid) - cost(bid)`. -/
def payoff (v bid : ℝ) : ℝ := v * M.winProb bid - M.cost bid

/-- Equilibrium allocation: `q(v) = winProb(strategy(v))`, the winning probability
for type `v` when following the equilibrium strategy. -/
def q : ℝ → ℝ := M.winProb ∘ M.strategy

/-- Equilibrium utility: `U(v) = payoff(v, strategy(v))`. -/
def U (v : ℝ) : ℝ := M.payoff v (M.strategy v)

@[simp] lemma payoff_eq (v bid : ℝ) :
    M.payoff v bid = v * M.winProb bid - M.cost bid := rfl
@[simp] lemma q_eq (v : ℝ) : M.q v = M.winProb (M.strategy v) := rfl
@[simp] lemma U_eq (v : ℝ) :
    M.U v = v * M.winProb (M.strategy v) - M.cost (M.strategy v) := rfl

lemma q_range (v : ℝ) : M.q v ∈ Icc 0 1 := M.winProb_range (M.strategy v)

/-! ### Regular equilibrium -/

/-- A mechanism is a **regular equilibrium** if the strategy is monotone and
nonnegative, the winning probability is monotone, and the cost is continuous.

These are the standard regularity conditions satisfied by any well-behaved
symmetric equilibrium in a single-item auction. -/
class IsRegular (M : Mechanism) : Prop where
  /-- winning probability is monotone -/
  winProb_mono : Monotone M.winProb
  /-- equilibrium strategy is weakly increasing -/
  strategy_mono : MonotoneOn M.strategy M.typeInterval
  /-- equilibrium bids are nonneg -/
  strategy_nonneg : ∀ v ∈ M.typeInterval, 0 ≤ M.strategy v
  /-- cost function is continuous -/
  cost_continuous : Continuous M.cost

end Mechanism

end
