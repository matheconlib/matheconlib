module

public import MathEconLib.SingleParameter.IC
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A Becker-inspired crime choice

This is a stylized, risk-neutral binary choice, not Becker's full model of
enforcement. A type `v` is the net gain from committing an offense rather than
abstaining. If the probability of a monetary fine is `p` and the fine is `f`,
the expected sanction is `p * f`. Committing has expected payoff `v - p * f`;
abstaining has payoff zero. The strategy commits at the equality tie.

The allocation in `SingleParameterProblem` is interpreted here as the offense
indicator. This example imports the shared single-parameter foundation; it
does not add another choice-problem structure or a probability distribution.
The policy interpretation presumes `p ∈ [0, 1]` and `0 ≤ f`. Only the
comparative-statics corollaries that need those bounds assume them explicitly.
-/

namespace MathEconLibExamples

@[expose] public section

open MathEconLib

namespace SingleParameter

/-- The two actions in the stylized crime-choice problem. -/
inductive CrimeDecision where
  /-- Commit the offense. -/
  | commit
  /-- Abstain from the offense. -/
  | abstain
  deriving DecidableEq

namespace CrimeDecision

/-- One for committing the offense, zero for abstaining. -/
def allocation : CrimeDecision → ℝ
  | commit => 1
  | abstain => 0

/-- The risk-neutral expected fine associated with each action. -/
def expectedPayment (p f : ℝ) : CrimeDecision → ℝ
  | commit => p * f
  | abstain => 0

end CrimeDecision

/-- The crime-choice problem with an exogenous probability `p` and fine `f`.

The type is the net gain from the offense. The real comparison used in the
strategy makes this definition `noncomputable`; this adds no economic
assumption. -/
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

/-- A type commits exactly when its net gain reaches the expected sanction. -/
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

/-- The threshold strategy maximizes expected payoff among both actions. -/
instance crimeProblem_hasUniversalIC
    (lowestType highestType p f : ℝ) :
    SingleParameterProblem.HasUniversalIC
      (crimeProblem lowestType highestType p f)
      (Set.univ : Set CrimeDecision) where
  strategyInS _ _ := Set.mem_univ _
  universalIC v _ decision _ := by
    by_cases h : p * f ≤ v
    · cases decision <;>
        simp [crimeProblem, SingleParameterProblem.payoff,
          CrimeDecision.allocation, CrimeDecision.expectedPayment, h]
    · have hv : v < p * f := lt_of_not_ge h
      cases decision with
      | commit =>
        simp [crimeProblem, SingleParameterProblem.payoff,
          CrimeDecision.allocation, CrimeDecision.expectedPayment, h]
        linarith
      | abstain =>
        simp [crimeProblem, SingleParameterProblem.payoff,
          CrimeDecision.allocation, CrimeDecision.expectedPayment, h]

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

/-- Raising the expected sanction weakly reduces the offense indicator for
every type. -/
theorem crimeProblem_q_antitone_expectedSanction
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
theorem crimeProblem_q_antitone_probability
    (lowestType highestType p p' f v : ℝ)
    (hp : p ≤ p') (hf : 0 ≤ f) :
    (crimeProblem lowestType highestType p' f).q v ≤
      (crimeProblem lowestType highestType p f).q v :=
  crimeProblem_q_antitone_expectedSanction
    lowestType highestType p f p' f v
    (mul_le_mul_of_nonneg_right hp hf)

/-- At a nonnegative conviction probability, raising the fine weakly reduces
the offense indicator. -/
theorem crimeProblem_q_antitone_fine
    (lowestType highestType p f f' v : ℝ)
    (hf : f ≤ f') (hp : 0 ≤ p) :
    (crimeProblem lowestType highestType p f').q v ≤
      (crimeProblem lowestType highestType p f).q v :=
  crimeProblem_q_antitone_expectedSanction
    lowestType highestType p f p f' v
    (mul_le_mul_of_nonneg_left hf hp)

/-! ## A concrete policy and two types -/

/-- With probability `1/2` and fine `2`, type `3/4` abstains. -/
example :
    (crimeProblem 0 2 (1 / 2) 2).strategy (3 / 4) = .abstain := by
  norm_num [crimeProblem]

/-- Under the same policy, type `3/2` commits. -/
example :
    (crimeProblem 0 2 (1 / 2) 2).strategy (3 / 2) = .commit := by
  norm_num [crimeProblem]

/-- The general deterrence theorem applies to a concrete increase in the
probability, from `1/4` to `1/2`, at fine `2`. -/
example (v : ℝ) :
    (crimeProblem 0 2 (1 / 2) 2).q v ≤
      (crimeProblem 0 2 (1 / 4) 2).q v := by
  apply crimeProblem_q_antitone_probability
  all_goals norm_num

end SingleParameter

end

end MathEconLibExamples
