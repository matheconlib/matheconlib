/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.RandomPreferences
import Lean

/-! General joint laws need neither DA nor a uniform-law import. -/

open Lean Elab Command in
run_cmd do
  for entry in (← getEnv).header.modules do
    if entry.module == `MathEconLib.ForMathlib.Uniform then
      logError m!"General profile laws import uniform-law helpers through {entry.module}."
    if (`MathEconLib.Matching).isPrefixOf entry.module &&
        entry.module != `MathEconLib.Matching.Classical.Marriage.Preferences &&
        entry.module != `MathEconLib.Matching.Classical.Marriage.RankPreferences &&
        entry.module != `MathEconLib.Matching.Classical.Marriage.RandomPreferences then
      logError m!"General profile laws import a specialization through {entry.module}."

namespace MathEconLibTest.Matching.RandomPreferences

open MathEconLib.Matching.MarriageMarket
open RankProfile
open scoped BigOperators

-- A nonuniform law works on an unequal market, with the outcome rule supplied explicitly.
example (p : RankProfile 1 2) :
    expectedAverageProposerRank (PMF.pure p) (fun _ ↦ ⊥) = 3 := by
  simp [expectedAverageProposerRank, PMF.toMeasure_pure, averageProposerRank, rank]

example (μ : PMF (RankProfile 0 2)) (outcome : RankProfile 0 2 → Fin 0 ≃. Fin 2) :
    expectedAverageProposerRank μ outcome = 0 := by simp

-- Arbitrary individual laws give the declared marginals and full joint independence.
example {m n : ℕ} (ν : ∀ a, PMF (Ranking m n a)) (a : Fin m ⊕ Fin n) :
    (independentProfile ν).toMeasure.map (fun p ↦ equivAgentRanks m n p a) =
      (ν a).toMeasure := independentProfile_map_ranking ν a

example {m n : ℕ} (ν : ∀ a, PMF (Ranking m n a)) :
    ProbabilityTheory.iIndepFun (fun a p ↦ equivAgentRanks m n p a)
      (independentProfile ν).toMeasure := iIndepFun_independentProfile ν

#print axioms RankProfile.expectedAverageProposerRank_eq_sum
#print axioms RankProfile.independentProfile_map_agentRanks
#print axioms RankProfile.iIndepFun_independentProfile

end MathEconLibTest.Matching.RandomPreferences
