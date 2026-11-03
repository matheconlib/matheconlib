/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLibExamples

/-!
# Matching-pennies audit checks

These checks import the canonical example through the examples umbrella. They verify its payoff
interpretation, indifference against a uniform opponent, and uniqueness after conversion to
probability measures. A profile with only one uniform player gives both players zero expected
payoff but is not an equilibrium. No game or equilibrium predicate is defined again here.
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MathEconLib.Probability
open MathEconLibExamples.GameTheory.MatchingPennies

namespace MathEconLibTest.GameTheory.MatchingPennies

/-- The independent expected payoff agrees with the elementary two-coin formula. -/
example (σ : Fin 2 → FinDist (Fin 2)) :
    matchingPennies.finiteExpectedPayoff p0 σ =
      (2 * σ p0 heads - 1) * (2 * σ p1 heads - 1) := by
  rw [expectedPayoff_p0_closed]
  have hp0 := FinDist.sum_pmf_two (σ p0)
  have hp1 := FinDist.sum_pmf_two (σ p1)
  dsimp [headsBias, heads, tails] at *
  have h0 : σ p0 0 - σ p0 1 = 2 * σ p0 0 - 1 := by linarith
  have h1 : σ p1 0 - σ p1 1 = 2 * σ p1 0 - 1 := by linarith
  rw [h0, h1]

/-- The expected payoffs sum to zero at every independent mixed profile. -/
example (σ : Fin 2 → FinDist (Fin 2)) :
    matchingPennies.finiteExpectedPayoff p0 σ +
      matchingPennies.finiteExpectedPayoff p1 σ = 0 := by
  rw [expectedPayoff_p0_closed, expectedPayoff_p1_closed, add_neg_cancel]

/-- Either player receives zero against a uniform opponent, whatever mixed action they choose. -/
example (i : Fin 2) (τ : FinDist (Fin 2)) :
    matchingPennies.finiteExpectedPayoff i (Function.update uniformProfile i τ) = 0 := by
  fin_cases i <;>
    simp [expectedPayoff_p0_closed, expectedPayoff_p1_closed, headsBias, uniformProfile, p0, p1]

/-- Zero expected payoffs alone do not imply equilibrium: player 1 can switch to tails. -/
example :
    (∀ i, matchingPennies.finiteExpectedPayoff i ![FinDist.pure heads, uniformAction] = 0) ∧
      ¬ matchingPennies.IsFiniteMixedNash ![FinDist.pure heads, uniformAction] := by
  constructor
  · intro i
    fin_cases i <;>
      simp [expectedPayoff_p0_closed, expectedPayoff_p1_closed, headsBias, p0, p1]
  · intro h
    have hdev := (StrategicGame.isFiniteMixedNash_iff _ _).1 h p1 (FinDist.pure tails)
    norm_num [expectedPayoff_p1_closed, headsBias, p0, p1, heads, tails] at hdev

/-- Uniqueness holds for arbitrary independent probability measures, via the existing bridge. -/
example (σ : StrategicGame.MixedStrategy (fun _ : Fin 2 ↦ Fin 2))
    (hσ : matchingPennies.IsMixedNash σ) :
    σ = StrategicGame.toProbability uniformProfile := by
  have hfinite : matchingPennies.IsFiniteMixedNash (StrategicGame.toSimplex σ) :=
    (StrategicGame.isFiniteMixedNash_iff_isMixedNash _ _).2 (by simpa using hσ)
  have heq := matchingPennies_mixed_nash_unique _ hfinite
  simpa using congrArg StrategicGame.toProbability heq

end MathEconLibTest.GameTheory.MatchingPennies

end
