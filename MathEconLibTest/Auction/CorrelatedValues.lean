/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Auction.Typeclasses
public import MathEconLib.Probability.FinDist.Measure
import Mathlib.Tactic.FinCases

/-!
# Correlated values distinguish marginal averages from interim incentives

Both bidders have the same Bernoulli value. The mechanism allocates nothing and charges each bidder
`(2 * b₀ - 1) * (2 * b₁ - 1)`. Averaging over the unconditional opponent law makes every fixed
report's expected payment zero. Conditional on either realized value, truthful reporting costs one
and the opposite report earns one. Truthful realized revenue is two.

This regression records the counterexample behind maintenance issue #209.
-/

@[expose] public noncomputable section

open MathEconLib MathEconLib.Probability MeasureTheory ProbabilityTheory

namespace MathEconLibTest.CorrelatedValues

local instance : MeasureSpace Bool where
  toMeasurableSpace := ⊤
  volume := @FinDist.toMeasure Bool _ ⊤ FinDist.uniform

local instance : MeasurableSingletonClass Bool := ⟨fun _ ↦ trivial⟩

local instance : IsProbabilityMeasure (volume : Measure Bool) := inferInstanceAs
  (IsProbabilityMeasure (FinDist.uniform : FinDist Bool).toMeasure)

/-- Integration is the average over the two equally likely states. -/
lemma integral_bool (f : Bool → ℝ) : ∫ ω, f ω = (f false + f true) / 2 := by
  change (∫ ω, f ω ∂(FinDist.uniform : FinDist Bool).toMeasure) = _
  rw [← FinDist.expect_eq_integral]
  simp only [FinDist.expect, FinDist.uniform_pmf, smul_eq_mul, Fintype.sum_bool,
    Fintype.card_bool]
  ring

/-- A fair Bernoulli value. -/
def value (ω : Bool) : ℝ := if ω then 1 else 0

/-- Zero allocation and a payment depending on both reports, with perfectly correlated values. -/
def auction : MathEconLib.Auction Bool 2 where
  rules.outcome _ _ := 0
  rules.transfer _ b := -((2 * b 0 - 1) * (2 * b 1 - 1))
  outcome_measurable _ := measurable_const
  θmin _ := 0
  θmax _ := 1
  θ _ := value
  θ_measurable _ := measurable_of_countable _

/-- Every fixed report has zero expected payment under the unconditional opponent law. -/
lemma marginal_payment (i : Fin 2) (b : ℝ) : auction.p i b = 0 := by
  simp only [Auction.p, Auction.p_strat, integral_bool]
  fin_cases i <;> simp [auction, Mechanism.payment, value] <;> ring

/-- The unconditional allocation is zero. -/
lemma marginal_allocation (i : Fin 2) (b : ℝ) : auction.q i b = 0 := by
  simp [Auction.q, Auction.q_strat, auction]

/-- The old BIC definition accepts the counterexample. -/
theorem old_bic : auction.BIC where
  bic i s _ s' _ := by simp [Auction.U, marginal_payment, marginal_allocation]

/-- The old revenue definition reports zero. -/
theorem old_expectedRevenue : auction.expectedRevenue = 0 := by
  simp [Auction.expectedRevenue, marginal_payment]

/-- Under truthful reporting each bidder is charged one in either state. -/
lemma truthful_payment (i : Fin 2) (ω : Bool) :
    auction.rules.payment i (auction.θ · ω) = 1 := by
  cases ω <;> norm_num [auction, Mechanism.payment, value]

/-- Reversing either bidder's report changes its payment to negative one. -/
lemma deviating_payment (i : Fin 2) (ω : Bool) :
    auction.rules.payment i
      (Function.update (auction.θ · ω) i (1 - value ω)) = -1 := by
  fin_cases i <;> cases ω <;> norm_num [auction, Mechanism.payment, value]

/-- In each state the feasible opposite report strictly improves either bidder's utility. -/
theorem profitable_deviation (i : Fin 2) (ω : Bool) :
    auction.θ i ω * auction.rules.outcome (auction.θ · ω) i -
        auction.rules.payment i (auction.θ · ω) <
      auction.θ i ω *
          auction.rules.outcome (Function.update (auction.θ · ω) i (1 - value ω)) i -
        auction.rules.payment i
          (Function.update (auction.θ · ω) i (1 - value ω)) := by
  rw [truthful_payment, deviating_payment]
  norm_num [auction]

/-- The opposite report belongs to the stated type interval in either state. -/
lemma deviation_mem_interval (i : Fin 2) (ω : Bool) :
    1 - value ω ∈ auction.interval i := by
  cases ω <;> norm_num [Auction.interval, auction, value]

/-- Actual expected truthful revenue is two under the correlated joint law. -/
theorem realized_revenue :
    (∫ ω, auction.rules.revenue (auction.θ · ω)) = 2 := by
  rw [integral_bool]
  simp only [Mechanism.revenue_eq_sum_payment, truthful_payment]
  norm_num

end MathEconLibTest.CorrelatedValues
