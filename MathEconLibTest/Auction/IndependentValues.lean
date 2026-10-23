/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Auction.Typeclasses
public import MathEconLib.Probability.FinDist.Measure
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Independent values: a positive control for the auction semantics repair

Two bidders have independent fair Bernoulli values. Each can buy half the object for a payment of
one quarter by reporting at least one half. Truthful reporting satisfies the independent-types BIC
interface on the entire stated interval, and realized expected revenue is one quarter.

The example exercises the joint-to-interim revenue bridge with measurable, integrable payments.
-/

@[expose] public noncomputable section

open MathEconLib MathEconLib.Probability MeasureTheory ProbabilityTheory

namespace MathEconLibTest.IndependentValues

local instance : MeasurableSpace Bool := ⊤

local instance : MeasurableSingletonClass Bool := ⟨fun _ ↦ trivial⟩

local instance : MeasureSpace (Fin 2 → Bool) where
  toMeasurableSpace := inferInstance
  volume := Measure.pi (fun _ : Fin 2 ↦ (FinDist.uniform : FinDist Bool).toMeasure)

local instance : IsProbabilityMeasure (volume : Measure (Fin 2 → Bool)) := inferInstanceAs
  (IsProbabilityMeasure (Measure.pi (fun _ : Fin 2 ↦ (FinDist.uniform : FinDist Bool).toMeasure)))

/-- A zero-or-one value. -/
def value (b : Bool) : ℝ := if b then 1 else 0

/-- Each bidder can buy half the object at a per-unit price of one half. -/
def auction : MathEconLib.Auction (Fin 2 → Bool) 2 where
  rules.outcome b i := if (1 / 2 : ℝ) ≤ b i then 1 / 2 else 0
  rules.transfer i b := -(if (1 / 2 : ℝ) ≤ b i then 1 / 4 else 0)
  outcome_measurable i := Measurable.ite
    (measurableSet_le measurable_const (measurable_pi_apply i)) measurable_const measurable_const
  θmin _ := 0
  θmax _ := 1
  θ i ω := value (ω i)
  θ_measurable i := (measurable_of_countable value).comp (measurable_pi_apply i)

/-- Product Bernoulli coordinates give independent bidder values. -/
instance independent_types : auction.HasIndependentTypes where
  θ_indep := iIndepFun_pi (fun _ ↦ (measurable_of_countable value).aemeasurable)

/-- The marginal allocation is half the object when the bidder accepts the posted price. -/
lemma allocation (i : Fin 2) (b : ℝ) :
    auction.q i b = if (1 / 2 : ℝ) ≤ b then 1 / 2 else 0 := by
  simp [Auction.q, Auction.q_strat, auction]

/-- The marginal payment is one quarter when the bidder accepts the posted price. -/
lemma payment (i : Fin 2) (b : ℝ) :
    auction.p i b = if (1 / 2 : ℝ) ≤ b then 1 / 4 else 0 := by
  simp [Auction.p, Auction.p_strat, auction, Mechanism.payment]

/-- Truthful reporting maximizes utility on the full interval under independent types. -/
instance bic : auction.BIC where
  toHasIndependentTypes := inferInstance
  bic i s _ s' _ := by
    simp only [Auction.U, allocation, payment]
    split_ifs <;> linarith

/-- The posted-price payment rule is measurable. -/
lemma payment_measurable (i : Fin 2) : Measurable (auction.rules.payment i) :=
  (Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply i))
    (measurable_const (a := (1 / 4 : ℝ))) (measurable_const (a := (0 : ℝ)))).neg.neg

/-- The revenue bridge applies, and each bidder's expected payment is one eighth. -/
theorem expectedRevenue_quarter : auction.expectedRevenue = 1 / 4 := by
  rw [auction.expectedRevenue_eq_sum_integral_p payment_measurable (fun _ ↦ Integrable.of_finite)]
  have hp (i : Fin 2) : (∫ ω, auction.p i (auction.θ i ω)) = 1 / 8 := by
    simp only [payment]
    change (∫ ω : Fin 2 → Bool, (if (1 / 2 : ℝ) ≤ value (ω i) then 1 / 4 else 0)
      ∂Measure.pi (fun _ : Fin 2 ↦ (FinDist.uniform : FinDist Bool).toMeasure)) = _
    rw [integral_comp_eval (μ := fun _ : Fin 2 ↦ (FinDist.uniform : FinDist Bool).toMeasure)
      (i := i) (measurable_of_countable
        (fun b : Bool ↦ if (1 / 2 : ℝ) ≤ value b then (1 / 4 : ℝ) else 0)).aestronglyMeasurable]
    rw [← FinDist.expect_eq_integral]
    norm_num [FinDist.expect, FinDist.uniform_pmf, value]
  simp_rw [hp]
  norm_num

end MathEconLibTest.IndependentValues
