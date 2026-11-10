/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

import MathEconLib.Decision.ExpectedUtility
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Expected Utility: Public API and Applications

These checks pin the statements of the expected utility development through its public module
`MathEconLib.Decision.ExpectedUtility`, and apply the representation and uniqueness theorems to
concrete preferences over lotteries.

## Checks

* Pins — the definitions of independence, continuity and expected utility representation,
  Propositions 3.1 and 3.2, the expected utility theorem, and uniqueness up to positive affine maps.
* A ranking by the probability of one prize — it is continuous and independent, so the expected
  utility theorem gives it a representation; by uniqueness, every Bernoulli function for it values
  that prize above the other.
* Indifference — the restricted theorem applies with no strictly ranked prizes, and by uniqueness
  every Bernoulli function for it is constant.
-/

set_option linter.privateModule false

namespace MathEconLib.Decision.Tests

open MathEconLib.Probability MathEconLib.Preferences MathEconLib.Decision

section Pins

variable {Z : Type*} [Fintype Z] (R : Preference (FinDist Z)) (v w : Z → ℝ)

example : HasExpectedUtilityRepresentation R ↔
    ∃ v : Z → ℝ, R.IsRepresentedBy fun p => p.expect v :=
  Iff.rfl

example : IsMixtureIndependent R ↔ ∀ (p q r : FinDist Z) (α : unitInterval), 0 < (α : ℝ) →
    (q ≼[R] p ↔ FinDist.mixture α q r ≼[R] FinDist.mixture α p r) :=
  isMixtureIndependent_iff

example : IsMixtureContinuous R ↔ ∀ p q r : FinDist Z, q ≺[R] p → r ≺[R] q →
    ∃ α : unitInterval, 0 < (α : ℝ) ∧ (α : ℝ) < 1 ∧ q ~[R] FinDist.mixture α p r :=
  isMixtureContinuous_iff

example (h : R.IsRepresentedBy fun p => p.expect v) : IsMixtureIndependent R :=
  isMixtureIndependent_of_isRepresentedBy h

example (h : R.IsRepresentedBy fun p => p.expect v) : IsMixtureContinuous R :=
  isMixtureContinuous_of_isRepresentedBy h

example (h : R.IsRepresentedBy fun p => p.expect v) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    R.IsRepresentedBy fun p => p.expect fun z => a * v z + b :=
  isRepresentedBy_expect_mul_add h ha b

example (hv : R.IsRepresentedBy fun p => p.expect v) (hw : R.IsRepresentedBy fun p => p.expect w) :
    ∃ a > (0 : ℝ), ∃ b : ℝ, ∀ z, w z = a * v z + b :=
  exists_eq_mul_add_of_isRepresentedBy hv hw

example [DecidableEq Z] (R : CompletePreference (FinDist Z))
    (hC : IsMixtureContinuousOn degenerate R.toPreference)
    (hDB : IsMixtureIndependentOn degenerate binary R.toPreference)
    (hBD : IsMixtureIndependentOn binary degenerate R.toPreference) :
    HasExpectedUtilityRepresentation R.toPreference :=
  hasExpectedUtilityRepresentation_of_isMixtureContinuousOn_of_isMixtureIndependentOn hC hDB hBD

example (R : CompletePreference (FinDist Z)) :
    HasExpectedUtilityRepresentation R.toPreference ↔
      IsMixtureContinuous R.toPreference ∧ IsMixtureIndependent R.toPreference :=
  hasExpectedUtilityRepresentation_iff_isMixtureContinuous_and_isMixtureIndependent

end Pins

/-! ### Ranking lotteries by the probability of one prize -/

/-- Lotteries over two prizes, ranked by the probability of the prize `0`. -/
noncomputable def probZero : CompletePreference (FinDist (Fin 2)) :=
  CompletePreference.ofUtility fun p => p.pmf 0

theorem probZero_isMixtureIndependent : IsMixtureIndependent probZero.toPreference := by
  rw [isMixtureIndependent_iff]
  intro p q r α hα
  simp only [probZero, CompletePreference.toPreference_ofUtility, Preference.ofUtility_le_iff,
    FinDist.mixture_pmf]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem probZero_isMixtureContinuous : IsMixtureContinuous probZero.toPreference := by
  rw [isMixtureContinuous_iff]
  intro p q r hqp hrq
  simp only [probZero, CompletePreference.toPreference_ofUtility, Preference.ofUtility_lt_iff]
    at hqp hrq
  have hpr : 0 < p.pmf 0 - r.pmf 0 := by linarith
  let α : unitInterval := ⟨(q.pmf 0 - r.pmf 0) / (p.pmf 0 - r.pmf 0),
    unitInterval.div_mem (by linarith) hpr.le (by linarith)⟩
  refine ⟨α, div_pos (by linarith) hpr, (div_lt_one hpr).2 (by linarith), ?_⟩
  simp only [probZero, CompletePreference.toPreference_ofUtility,
    Preference.ofUtility_antisymmRel_iff, FinDist.mixture_pmf, α]
  field_simp
  ring

/-- The expected utility theorem applied: ranking by the probability of the prize `0` is
continuous and independent, so it has an expected utility representation. -/
theorem probZero_hasExpectedUtilityRepresentation :
    HasExpectedUtilityRepresentation probZero.toPreference :=
  hasExpectedUtilityRepresentation_iff_isMixtureContinuous_and_isMixtureIndependent.2
    ⟨probZero_isMixtureContinuous, probZero_isMixtureIndependent⟩

/-- The Bernoulli function paying `1` for the prize `0` and `0` for the prize `1` represents it. -/
theorem probZero_isRepresentedBy :
    probZero.IsRepresentedBy fun p : FinDist (Fin 2) => p.expect ![(1 : ℝ), 0] := by
  intro p q
  simp [probZero, FinDist.expect_eq_sum, Fin.sum_univ_two]

/-- Uniqueness applied: every Bernoulli function for `probZero` values the prize `0` strictly
above the prize `1`. -/
theorem lt_of_probZero_isRepresentedBy {w : Fin 2 → ℝ}
    (hw : probZero.IsRepresentedBy fun p => p.expect w) : w 1 < w 0 := by
  obtain ⟨a, ha, b, hab⟩ := exists_eq_mul_add_of_isRepresentedBy probZero_isRepresentedBy hw
  have h0 : (![(1 : ℝ), 0] : Fin 2 → ℝ) 0 = 1 := rfl
  have h1 : (![(1 : ℝ), 0] : Fin 2 → ℝ) 1 = 0 := rfl
  rw [hab 0, hab 1, h0, h1]
  linarith

/-! ### Indifference: a constant Bernoulli function -/

/-- Indifference between all lotteries over three prizes. -/
noncomputable def indifferent : CompletePreference (FinDist (Fin 3)) :=
  CompletePreference.ofUtility fun _ => (0 : ℝ)

/-- The restricted theorem applies although no prize is strictly better than another. -/
theorem indifferent_hasExpectedUtilityRepresentation :
    HasExpectedUtilityRepresentation indifferent.toPreference :=
  hasExpectedUtilityRepresentation_of_isMixtureContinuousOn_of_isMixtureIndependentOn
    (isMixtureContinuousOn_of_not_exists fun ⟨_, _, _, _, _, _, h, _⟩ => by
      simp [indifferent] at h)
    (fun _ _ _ _ _ _ _ => by simp [indifferent])
    (fun _ _ _ _ _ _ _ => by simp [indifferent])

theorem indifferent_isRepresentedBy :
    indifferent.IsRepresentedBy fun p : FinDist (Fin 3) => p.expect fun _ => (0 : ℝ) := by
  intro p q
  simp [indifferent, FinDist.expect_const]

/-- Uniqueness applied: every Bernoulli function for indifference is constant. -/
theorem eq_of_indifferent_isRepresentedBy {w : Fin 3 → ℝ}
    (hw : indifferent.IsRepresentedBy fun p => p.expect w) (y z : Fin 3) : w y = w z := by
  obtain ⟨a, -, b, hab⟩ := exists_eq_mul_add_of_isRepresentedBy indifferent_isRepresentedBy hw
  rw [hab y, hab z]

end MathEconLib.Decision.Tests
