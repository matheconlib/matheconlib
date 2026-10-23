/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Auction.Typeclasses
public import MathEconLib.Probability.FinDist.Measure
import Mathlib.Tactic.FinCases
import Mathlib.Probability.Independence.Integration

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
open MathEconLib.GameTheory.BayesianPrior

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

/-- Both realized values lie in the declared interval. -/
instance bounded_types : auction.HasBoundedTypes where
  θ_in i ω := by cases ω <;> norm_num [auction, value]

/-- The counterexample uses a measurable polynomial payment rule. -/
lemma payment_measurable (i : Fin 2) : Measurable (auction.rules.payment i) := by
  change Measurable (fun b : Fin 2 → ℝ ↦ -(-((2 * b 0 - 1) * (2 * b 1 - 1))))
  fun_prop

/-- Finite support makes every realized payment integrable. -/
lemma payment_integrable (i : Fin 2) :
    Integrable (fun ω ↦ auction.rules.payment i (auction.θ · ω)) := Integrable.of_finite

/-- Every fixed report has zero expected payment under the unconditional opponent law. -/
lemma marginal_payment (i : Fin 2) (b : ℝ) : auction.p i b = 0 := by
  simp only [Auction.p, Auction.p_strat, integral_bool]
  fin_cases i <;> simp [auction, Mechanism.payment, value] <;> ring

/-- The unconditional allocation is zero. -/
lemma marginal_allocation (i : Fin 2) (b : ℝ) : auction.q i b = 0 := by
  simp [Auction.q, Auction.q_strat, auction]

/-- All the incentive inequalities in the old, unrestricted BIC definition hold. -/
theorem old_bic_inequalities (i : Fin 2) (s s' : ℝ) :
    s * auction.q i s' - auction.p i s' ≤ auction.U i s := by
  simp [Auction.U, marginal_payment, marginal_allocation]

/-- The old revenue definition reports zero. -/
theorem old_expectedRevenue :
    (∫ ω, ∑ i : Fin 2, auction.p i (auction.θ i ω)) = 0 := by
  simp [marginal_payment]

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

/-- Each bidder's own value uniquely determines the state, so the deviation uses only own
information. -/
lemma state_determined_by_value (i : Fin 2) {ω ω' : Bool}
    (h : auction.θ i ω = auction.θ i ω') : ω = ω' := by
  cases ω <;> cases ω' <;> norm_num [auction, value] at *

/-- The values are not independent: their joint second moment is one half, not one quarter. -/
theorem not_independent : ¬ auction.HasIndependentTypes := by
  intro h
  have hXY := h.θ_indep.indepFun (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  have hh := hXY.integral_fun_mul_eq_mul_integral
    (auction.θ_measurable 0).aestronglyMeasurable
    (auction.θ_measurable 1).aestronglyMeasurable
  simp only [integral_bool] at hh
  norm_num [auction, value] at hh

/-- A selected conditional-belief version for any auction whose values all equal the state.
At every real true type `s`, opponents have that same value. The disintegration identity checks
agreement with the actual correlated prior. -/
def diagonalBeliefs (A : MathEconLib.Auction Bool 2)
    (hθ : ∀ i ω, A.θ i ω = value ω) : ConditionalBeliefs A.typeLaw where
  opponents i := Kernel.deterministic (fun s _ ↦ s)
    (measurable_pi_lambda _ fun _ ↦ measurable_id)
  isMarkov _ := inferInstance
  disintegrates i := by
    rw [Measure.compProd_deterministic]
    simp only [marginalType, Auction.typeLaw]
    rw [Measure.map_map (measurable_pi_apply i) (measurable_pi_lambda _ A.θ_measurable)]
    rw [Measure.map_map (show Measurable (fun s : ℝ ↦
        (s, fun _ : {j : Fin 2 // j ≠ i} ↦ s)) from
          measurable_id.prodMk (measurable_pi_lambda _ fun _ ↦ measurable_id))
      ((measurable_pi_apply i).comp (measurable_pi_lambda _ A.θ_measurable))]
    rw [Measure.map_map ((measurable_pi_apply i).prodMk (measurable_drop i))
      (measurable_pi_lambda _ A.θ_measurable)]
    congr 1
    funext ω
    change (A.θ i ω, fun _ : {j : Fin 2 // j ≠ i} ↦ A.θ i ω) =
      (A.θ i ω, fun j ↦ A.θ j.val ω)
    congr 1
    funext j
    exact (hθ i ω).trans (hθ j ω).symm

/-- The general BIC predicate rejects the bad mechanism by its actual profitable deviation,
without imposing independence on BIC. -/
theorem not_bic : ¬ auction.BIC (diagonalBeliefs auction (fun _ _ ↦ rfl)) := by
  intro h
  have hh := h.bic 0 1 (by norm_num [Auction.interval, auction])
    0 (by norm_num [Auction.interval, auction])
  norm_num [Auction.conditionalUtility, Mechanism.DirectMechanism.interimUtility_eq_integral,
    diagonalBeliefs, Kernel.deterministic_apply, Auction.valuationEnvironment,
    Mechanism.QuasilinearEnvironment.ofPrivate,
    auction, GameTheory.BayesianPrior.insert, Equiv.piSplitAt] at hh

/-- The old marginal participation inequality accepts the bad correlated mechanism. -/
theorem old_marginal_ir : auction.MarginalIR := by
  intro i s _
  simp [Auction.U, marginal_payment, marginal_allocation]

/-- Conditional interim IR rejects its negative truthful utility. -/
theorem not_interim_ir : ¬ auction.InterimIR (diagonalBeliefs auction (fun _ _ ↦ rfl)) := by
  intro h
  have hh := h.2 0 1 (by norm_num [Auction.interval, auction])
  norm_num [Auction.conditionalUtility, Mechanism.DirectMechanism.interimUtility_eq_integral,
    diagonalBeliefs, Kernel.deterministic_apply, Auction.valuationEnvironment,
    Mechanism.QuasilinearEnvironment.ofPrivate, auction,
    GameTheory.BayesianPrior.insert, Equiv.piSplitAt] at hh

/-- Actual expected truthful revenue is two under the correlated joint law. -/
theorem realized_revenue :
    (∫ ω, auction.rules.revenue (auction.θ · ω)) = 2 := by
  rw [integral_bool]
  simp only [Mechanism.revenue_eq_sum_payment, truthful_payment]
  norm_num

/-- The repaired expected-revenue definition returns the realized joint revenue. -/
theorem expectedRevenue_two : auction.expectedRevenue = 2 := realized_revenue

/-- A correlated truthful mechanism: no allocation, and each bidder pays squared disagreement
with the other bidder's report. -/
def squareAuction : MathEconLib.Auction Bool 2 where
  rules.outcome _ _ := 0
  rules.transfer _ b := -((b 0 - b 1) ^ 2)
  outcome_measurable _ := measurable_const
  θmin _ := 0
  θmax _ := 1
  θ _ := value
  θ_measurable _ := measurable_of_countable _

/-- Conditional utility is a negative square for every real true type and report, including
unrealized interior types under the selected diagonal-belief version. -/
lemma square_utility (i : Fin 2) (s r : ℝ) :
    squareAuction.conditionalUtility (diagonalBeliefs squareAuction (fun _ _ ↦ rfl)) i s r =
      -((r - s) ^ 2) := by
  rw [Auction.conditionalUtility, Mechanism.DirectMechanism.interimUtility_eq_integral]
  fin_cases i <;>
    simp [diagonalBeliefs, Kernel.deterministic_apply, squareAuction,
      Auction.valuationEnvironment, Mechanism.QuasilinearEnvironment.ofPrivate,
      GameTheory.BayesianPrior.insert, Equiv.piSplitAt]
  all_goals ring

/-- General BIC accepts a correlated model, with a proof over the full report continuum. -/
theorem square_bic : squareAuction.BIC (diagonalBeliefs squareAuction (fun _ _ ↦ rfl)) := by
  refine ⟨?_, ?_⟩
  · intro i s _ r _
    simp only [diagonalBeliefs, Kernel.deterministic_apply]
    apply integrable_dirac
    simp
  · intro i s _ r _
    change squareAuction.conditionalUtility (diagonalBeliefs squareAuction (fun _ _ ↦ rfl))
      i s r ≤ squareAuction.conditionalUtility
        (diagonalBeliefs squareAuction (fun _ _ ↦ rfl)) i s s
    rw [square_utility, square_utility]
    nlinarith [sq_nonneg (r - s)]

/-- The correlated positive control is outside IPV, although it satisfies general BIC. -/
theorem square_not_ipv : ¬ squareAuction.IsIPV := by
  intro h
  exact not_independent ⟨h.θ_indep⟩

/-- Conditional participation accepts the truthful correlated positive control. -/
theorem square_interim_ir :
    squareAuction.InterimIR (diagonalBeliefs squareAuction (fun _ _ ↦ rfl)) := by
  refine ⟨fun i s hs ↦ square_bic.integrable i s hs s hs, ?_⟩
  intro i s _
  rw [square_utility]
  simp

/-- Its old marginal participation inequality incorrectly rejects truthful utility zero. -/
theorem square_not_marginal_ir : ¬ squareAuction.MarginalIR := by
  intro h
  have hh := h 0 0 (by norm_num [Auction.interval, squareAuction])
  norm_num [Auction.U, Auction.q, Auction.q_strat, Auction.p, Auction.p_strat,
    integral_bool, squareAuction, Mechanism.payment, value] at hh

/-- The old marginal inequalities reject this genuinely BIC mechanism at a supported type and
an interior report. This is the audit's false negative, independently of the false-positive test. -/
theorem square_marginal_false_negative :
    ¬ (∀ i, ∀ s ∈ squareAuction.interval i, ∀ r ∈ squareAuction.interval i,
      s * squareAuction.q i r - squareAuction.p i r ≤ squareAuction.U i s) := by
  intro h
  have hh := h 0 0 (by norm_num [Auction.interval, squareAuction])
    (1 / 2) (by norm_num [Auction.interval, squareAuction])
  norm_num [Auction.U, Auction.q, Auction.q_strat, Auction.p, Auction.p_strat,
    integral_bool, squareAuction, Mechanism.payment, value] at hh

end MathEconLibTest.CorrelatedValues
