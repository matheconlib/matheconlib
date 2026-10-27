/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.SingleParameter.IC
public import MathEconLib.ValueDistribution.PostedPrice
import Mathlib.Tactic.NormNum

/-!
# A Becker-inspired crime choice

This is a stylized, risk-neutral binary choice inspired by Becker's analysis
of crime and punishment, not a formalization of his full enforcement model.
A type `v` is the net gain from committing an offense rather than choosing
not to. If the probability of a monetary fine is `p` and the fine is `f`,
the expected sanction is `p * f`. Committing an offense has expected payoff
`v - p * f`; choosing not to has payoff zero. When `v = p * f`, both actions
give payoff zero. This example chooses to commit the offense as a tie-breaking
convention.

The allocation in `SingleParameterProblem` is interpreted here as the offense
indicator. Individual choice and pointwise comparative statics use the shared
single-parameter foundation without a type distribution. The final section
adds an exogenous `ValueDistribution` to derive the aggregate crime rate,
holding that distribution fixed when comparing policies.
While the policy interpretation presumes `p ∈ [0, 1]` and `0 ≤ f`, only the
comparative-statics corollaries that need nonnegativity assume it explicitly.

The optimality proof reuses the posted-price problem at price `p * f`, with
a local correspondence between crime and purchase decisions.

## References

Gary S. Becker (1968), *Crime and Punishment: An Economic Approach*,
*Journal of Political Economy* **76**(2), 169–217.
Section II.B.3, pp. 176–177, especially the expected-utility formula in
footnote 16. The binary action space, risk neutrality, and tie-breaking rule
are choices of this example.
[DOI: 10.1086/259394](https://doi.org/10.1086/259394).
-/

namespace MathEconLibExamples

@[expose] public section

open MathEconLib

namespace SingleParameter

/-! ## The choice problem -/

/-- The two actions in the stylized crime-choice problem. -/
inductive CrimeDecision where
  /-- Commit the offense. -/
  | commit
  /-- Abstain from committing the offense. -/
  | abstain
  deriving DecidableEq

namespace CrimeDecision

/-- One for committing the offense, zero for abstaining. -/
def allocation : CrimeDecision → ℝ
  | commit => 1
  | abstain => 0

/-- The risk-neutral expected fine paid by the individual at each action.

This is a payment, not a payoff: `SingleParameterProblem.payoff` subtracts it
from the gain associated with the action. -/
def expectedPayment (p f : ℝ) : CrimeDecision → ℝ
  | commit => p * f
  | abstain => 0

end CrimeDecision

/-- The crime-choice problem with an exogenous probability `p` and fine `f`.

The type is the net gain from the offense. The type interval limits the
generic incentive-compatibility and participation statements. The cutoff
strategy is defined for every real gain; the population distribution is
supplied separately.

The real comparison used in the strategy makes this definition
`noncomputable`; this adds no economic assumption. -/
noncomputable def crimeProblem
    (lowestType highestType p f : ℝ) :
    SingleParameterProblem CrimeDecision where
  lowestType := lowestType
  highestType := highestType
  allocation := CrimeDecision.allocation
  allocation_range decision := by
    cases decision <;> simp [CrimeDecision.allocation]
  payment := CrimeDecision.expectedPayment p f
  strategy v := if p * f ≤ v then .commit else .abstain

@[simp]
lemma crimeProblem_payoff_commit
    (lowestType highestType p f v : ℝ) :
    (crimeProblem lowestType highestType p f).payoff v .commit =
      v - p * f := by
  simp [crimeProblem, SingleParameterProblem.payoff,
    CrimeDecision.allocation, CrimeDecision.expectedPayment]

@[simp]
lemma crimeProblem_payoff_abstain
    (lowestType highestType p f v : ℝ) :
    (crimeProblem lowestType highestType p f).payoff v .abstain = 0 := by
  simp [crimeProblem, SingleParameterProblem.payoff,
    CrimeDecision.allocation, CrimeDecision.expectedPayment]

/-- A type chooses to commit the offense exactly when its net gain reaches the expected sanction. -/
theorem crimeProblem_strategy_commit_iff
    (lowestType highestType p f v : ℝ) :
    (crimeProblem lowestType highestType p f).strategy v = .commit ↔
      p * f ≤ v := by
  by_cases h : p * f ≤ v <;> simp [crimeProblem, h]

/-- The induced offense indicator is a threshold rule. -/
theorem crimeProblem_q
    (lowestType highestType p f v : ℝ) :
    (crimeProblem lowestType highestType p f).q v =
      if p * f ≤ v then 1 else 0 := by
  by_cases h : p * f ≤ v <;>
    simp [crimeProblem, SingleParameterProblem.q, CrimeDecision.allocation, h]

/-! ## Optimality and participation -/

-- The action correspondence is used only to reuse posted-price optimality.
private def toPurchaseDecision : CrimeDecision → SingleParameterProblem.PurchaseDecision
  | .commit => .buy
  | .abstain => .doNotBuy

private lemma crimeProblem_payoff_eq_postedPriceProblem
    (lowestType highestType p f v : ℝ) (decision : CrimeDecision) :
    (crimeProblem lowestType highestType p f).payoff v decision =
      (SingleParameterProblem.postedPriceProblem lowestType highestType (p * f)).payoff
        v (toPurchaseDecision decision) := by
  cases decision <;>
    simp only [toPurchaseDecision, crimeProblem_payoff_commit, crimeProblem_payoff_abstain,
      SingleParameterProblem.postedPriceProblem_payoff_buy,
      SingleParameterProblem.postedPriceProblem_payoff_doNotBuy]

private lemma crimeProblem_strategy_eq_postedPriceProblem
    (lowestType highestType p f v : ℝ) :
    toPurchaseDecision ((crimeProblem lowestType highestType p f).strategy v) =
      (SingleParameterProblem.postedPriceProblem lowestType highestType (p * f)).strategy v := by
  by_cases h : p * f ≤ v <;>
    simp [crimeProblem, SingleParameterProblem.postedPriceProblem, toPurchaseDecision, h]

/-- The threshold strategy maximizes expected payoff among both actions. -/
instance crimeProblem_hasUniversalIC
    (lowestType highestType p f : ℝ) :
    SingleParameterProblem.HasUniversalIC
      (crimeProblem lowestType highestType p f)
      (Set.univ : Set CrimeDecision) where
  strategyInS _ _ := Set.mem_univ _
  universalIC v hv decision _ := by
    have h := (inferInstance : SingleParameterProblem.HasUniversalIC
      (SingleParameterProblem.postedPriceProblem lowestType highestType (p * f))
      (Set.univ : Set SingleParameterProblem.PurchaseDecision)).universalIC
        v hv (toPurchaseDecision decision) (Set.mem_univ _)
    rw [← crimeProblem_strategy_eq_postedPriceProblem] at h
    simpa only [← crimeProblem_payoff_eq_postedPriceProblem] using h

/-- The shared IC hierarchy also supplies type-deviation IC. -/
example (lowestType highestType p f : ℝ) :
    SingleParameterProblem.HasTypeDeviationIC
      (crimeProblem lowestType highestType p f) :=
  inferInstance

/-- The same hierarchy supplies envelope IC without another crime-specific
proof. -/
example (lowestType highestType p f : ℝ) :
    SingleParameterProblem.HasEnvelopeIC
      (crimeProblem lowestType highestType p f) :=
  inferInstance

/-- Abstaining is feasible and pays zero, so optimal choice is individually
rational. -/
theorem crimeProblem_isIndividuallyRational
    (lowestType highestType p f : ℝ) :
    (crimeProblem lowestType highestType p f).IsIndividuallyRational := by
  intro v hv
  have h := (inferInstance : SingleParameterProblem.HasUniversalIC
    (crimeProblem lowestType highestType p f)
    (Set.univ : Set CrimeDecision)).universalIC
      v hv .abstain (Set.mem_univ _)
  change 0 ≤ (crimeProblem lowestType highestType p f).payoff
    v ((crimeProblem lowestType highestType p f).strategy v)
  simpa only [crimeProblem_payoff_abstain] using h

/-! ## Pointwise comparative statics -/

/-- Raising the expected sanction weakly reduces the offense indicator for
every type. -/
theorem crimeProblem_q_antitone_in_expectedSanction
    (lowestType highestType p f p' f' v : ℝ)
    (hsanction : p * f ≤ p' * f') :
    (crimeProblem lowestType highestType p' f').q v ≤
      (crimeProblem lowestType highestType p f).q v := by
  rw [crimeProblem_q, crimeProblem_q]
  by_cases hhigh : p' * f' ≤ v
  · have hlow : p * f ≤ v := le_trans hsanction hhigh
    simp [hhigh, hlow]
  · by_cases hlow : p * f ≤ v <;> simp [hhigh, hlow]

/-- At a nonnegative fine, raising the conviction probability weakly reduces
the offense indicator. -/
theorem crimeProblem_q_antitone_in_probability_of_nonneg_fine
    (lowestType highestType p p' f v : ℝ)
    (hp : p ≤ p') (hf : 0 ≤ f) :
    (crimeProblem lowestType highestType p' f).q v ≤
      (crimeProblem lowestType highestType p f).q v :=
  crimeProblem_q_antitone_in_expectedSanction
    lowestType highestType p f p' f v
    (mul_le_mul_of_nonneg_right hp hf)

/-- At a nonnegative conviction probability, raising the fine weakly reduces
the offense indicator. -/
theorem crimeProblem_q_antitone_in_fine_of_nonneg_probability
    (lowestType highestType p f f' v : ℝ)
    (hf : f ≤ f') (hp : 0 ≤ p) :
    (crimeProblem lowestType highestType p f').q v ≤
      (crimeProblem lowestType highestType p f).q v :=
  crimeProblem_q_antitone_in_expectedSanction
    lowestType highestType p f p f' v
    (mul_le_mul_of_nonneg_left hf hp)

/-! ## A concrete policy -/

/-- With probability `1/2` and fine `2`, type `3/4` abstains. -/
example :
    (crimeProblem 0 2 (1 / 2) 2).strategy (3 / 4) = .abstain := by
  norm_num [crimeProblem]

/-- Under the same policy, type `3/2` chooses to commit the offense. -/
example :
    (crimeProblem 0 2 (1 / 2) 2).strategy (3 / 2) = .commit := by
  norm_num [crimeProblem]

/-- The general deterrence theorem applies to a concrete increase in the
probability, from `1/4` to `1/2`, at fine `2`. -/
example (v : ℝ) :
    (crimeProblem 0 2 (1 / 2) 2).q v ≤
      (crimeProblem 0 2 (1 / 4) 2).q v := by
  apply crimeProblem_q_antitone_in_probability_of_nonneg_fine
  all_goals norm_num

/-- At the cutoff, both actions give zero payoff; the chosen offense indicator is one. -/
example :
    (crimeProblem 0 2 (1 / 2) 2).q 1 = 1 ∧
      (crimeProblem 0 2 (1 / 2) 2).payoff 1 .commit = 0 ∧
      (crimeProblem 0 2 (1 / 2) 2).payoff 1 .abstain = 0 := by
  rw [crimeProblem_q, crimeProblem_payoff_commit, crimeProblem_payoff_abstain]
  norm_num

/-! ## Aggregate crime under a fixed type distribution

Let `D` describe the population's net gains from committing an offense.
The expected offense indicator, `D.expectedAllocation`, is the aggregate
crime rate. The same distribution is used for both policies; the comparison
does not model a policy-induced change in the population's gains.

Because individuals choose to commit at the cutoff, the crime rate includes
any probability mass at `p * f`. No density or atomlessness is assumed.
The offense indicator is measurable and bounded, hence integrable under any
probability distribution of gains. No moment bound on those gains is needed.
-/

/-- The aggregate crime rate is the probability that the net gain is at least
the expected sanction, including types exactly at the cutoff. -/
theorem crimeProblem_expectedAllocation_eq_probAtLeast
    (D : ValueDistribution) (lowestType highestType p f : ℝ) :
    D.expectedAllocation (crimeProblem lowestType highestType p f) =
      D.probAtLeast (p * f) := by
  calc
    D.expectedAllocation (crimeProblem lowestType highestType p f) =
        D.expectedAllocation
          (SingleParameterProblem.postedPriceProblem lowestType highestType (p * f)) := by
      unfold ValueDistribution.expectedAllocation
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with v
      rw [crimeProblem_q, SingleParameterProblem.postedPriceProblem_q]
    _ = D.probAtLeast (p * f) :=
      D.expectedAllocation_postedPriceProblem lowestType highestType (p * f)

/-- For a fixed type distribution, raising the expected sanction weakly
reduces the aggregate crime rate. -/
theorem crimeProblem_expectedAllocation_antitone_in_expectedSanction
    (D : ValueDistribution) (lowestType highestType p f p' f' : ℝ)
    (hsanction : p * f ≤ p' * f') :
    D.expectedAllocation (crimeProblem lowestType highestType p' f') ≤
      D.expectedAllocation (crimeProblem lowestType highestType p f) := by
  rw [crimeProblem_expectedAllocation_eq_probAtLeast,
    crimeProblem_expectedAllocation_eq_probAtLeast]
  exact D.antitone_probAtLeast hsanction

/-- The same increase from probability `1/4` to `1/2` at fine `2` weakly
reduces aggregate crime under any fixed type distribution. -/
example (D : ValueDistribution) :
    D.expectedAllocation (crimeProblem 0 2 (1 / 2) 2) ≤
      D.expectedAllocation (crimeProblem 0 2 (1 / 4) 2) := by
  apply crimeProblem_expectedAllocation_antitone_in_expectedSanction
  norm_num

/-- In a population with net gain `1` for every individual and fine `2`, the
crime rate falls from `1` to `0` when the probability rises from `1/2` to `3/4`.
At the lower probability, the entire population is exactly at the cutoff and
chooses to commit the offense, so its probability mass is included. -/
example :
    let D : ValueDistribution := (MeasureTheory.Measure.dirac (1 : ℝ)).toProbabilityMeasure
    D.expectedAllocation (crimeProblem 0 2 (1 / 2) 2) = 1 ∧
      D.expectedAllocation (crimeProblem 0 2 (3 / 4) 2) = 0 := by
  dsimp only
  rw [crimeProblem_expectedAllocation_eq_probAtLeast,
    crimeProblem_expectedAllocation_eq_probAtLeast]
  norm_num [ValueDistribution.probAtLeast, MeasureTheory.ProbabilityMeasure.coeFn_def]

end SingleParameter

end

end MathEconLibExamples
