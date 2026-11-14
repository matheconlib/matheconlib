/-
Copyright (c) 2026 Yaron Velner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaron Velner
-/
module

public import MathEconLibExamples

/-!
# Rock paper scissors audit checks

These checks import the canonical example through the examples umbrella. They verify its payoff
interpretation, indifference against a uniform opponent, and uniqueness after conversion to
probability measures. A profile with only one uniform player gives both players zero expected
payoff but is not an equilibrium. No game or equilibrium predicate is defined again here.
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MathEconLib.Probability
open MathEconLibExamples.GameTheory.RockPaperScissors

namespace MathEconLibTest.GameTheory.RockPaperScissors

/-- The independent expected payoff agrees with the elementary formula. -/
example (σ : Fin 2 → FinDist (Fin 3)) :
    rockPaperScissors.finiteExpectedPayoff p0 σ =
      (σ p0) rock *
        ((σ p1) scissors - (σ p1) paper) +
      (σ p0) paper *
        ((σ p1) rock - (σ p1) scissors) +
      (σ p0) scissors *
        ((σ p1) paper - (σ p1) rock) := by
  simp [expectedPayoff_p0, expectedPayoff_p0_closed]


/-- The expected payoffs sum to zero at every independent mixed profile. -/
example (σ : Fin 2 → FinDist (Fin 3)) :
    rockPaperScissors.finiteExpectedPayoff p0 σ +
      rockPaperScissors.finiteExpectedPayoff p1 σ = 0 := by
  simp [expectedPayoff_p0, expectedPayoff_p0_closed, expectedPayoff_p1, expectedPayoff_p1_closed]
  ring


/-- Either player receives zero against a uniform opponent, whatever mixed action they choose. -/
example (i : Fin 2) (τ : FinDist (Fin 3)) :
    rockPaperScissors.finiteExpectedPayoff i (Function.update uniformProfile i τ) = 0 := by
  fin_cases i
  · simp [expectedPayoff_p0_closed, expectedPayoff_p0,
          uniformProfile, uniformAction, p0, p1]
  · simp [expectedPayoff_p1_closed, expectedPayoff_p1,
          uniformProfile, uniformAction, p0, p1]



/-- Zero expected payoffs alone do not imply equilibrium: player 1 can switch to paper. -/
example :
    (∀ i, rockPaperScissors.finiteExpectedPayoff i ![FinDist.pure rock, uniformAction] = 0) ∧
      ¬ rockPaperScissors.IsFiniteMixedNash ![FinDist.pure rock, uniformAction] := by
  constructor
  · intro i
    fin_cases i <;>
      simp [expectedPayoff_p0, expectedPayoff_p0_closed, expectedPayoff_p1,
            expectedPayoff_p1_closed, rock, paper, scissors]
  · intro h
    rw [StrategicGame.isFiniteMixedNash_iff] at h
    have hdev := h p1 (FinDist.pure paper)
    norm_num [expectedPayoff_p1_closed, expectedPayoff_p1,
              p0, p1, rock, paper, scissors] at hdev

/-- Uniqueness holds for arbitrary independent probability measures, via the existing bridge. -/
example (σ : StrategicGame.MixedStrategy (fun _ : Fin 2 ↦ Fin 3))
    (hσ : rockPaperScissors.IsMixedNash σ) :
    σ = StrategicGame.toProbability uniformProfile := by
  have hfinite : rockPaperScissors.IsFiniteMixedNash (StrategicGame.toSimplex σ) :=
    (StrategicGame.isFiniteMixedNash_iff_isMixedNash _ _).2 (by simpa using hσ)
  have heq := rockPaperScissors_mixed_nash_unique _ hfinite
  simpa using congrArg StrategicGame.toProbability heq

end MathEconLibTest.GameTheory.RockPaperScissors

end
