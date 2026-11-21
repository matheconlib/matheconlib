/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.RankPreferences
import Lean

/-!
Dependency and semantic checks for deterministic ranks. This imports only the lower ranking
layer; public-umbrella checks for the same API are in `Matching.RandomPreferences`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for entry in env.header.modules do
    if (`Mathlib.Probability).isPrefixOf entry.module ||
        (`MathEconLib.Probability).isPrefixOf entry.module then
      logError m!"Deterministic ranks import probability through {entry.module}."
    if (`MathEconLib.Matching).isPrefixOf entry.module &&
        entry.module != `MathEconLib.Matching.Classical.Marriage.Preferences &&
        entry.module != `MathEconLib.Matching.Classical.Marriage.RankPreferences then
      logError m!"Deterministic ranks import the matching theory through {entry.module}."

namespace MathEconLibTest.Matching.RankPreferences

open MathEconLib.Matching.MarriageMarket
open RankProfile
open scoped BigOperators

example {m n : ℕ} (p : RankProfile m n) : p.symm.symm = p := symm_symm p

example {m n : ℕ} (p : RankProfile m n) :
    p.symm.toMarriageMarket = p.toMarriageMarket.symm := symm_toMarriageMarket p

-- Receiver statistics use side exchange and the inverse matching.
example {m n : ℕ} (p : RankProfile m n) (μ : Fin m ≃. Fin n) :
    p.symm.averageProposerRank μ.symm = 𝔼 j, (rank (p.womanRank j) (μ.symm j) : ℝ) := rfl

-- On an empty assignment, all-agent averages retain the outside-option rank.
example (p : RankProfile 1 2) : p.averageProposerRank ⊥ = 3 := by
  simp [averageProposerRank, rank]

example (p : RankProfile 1 2) : p.symm.averageProposerRank (⊥ : Fin 1 ≃. Fin 2).symm = 2 := by
  simp [averageProposerRank, rank]

example (p : RankProfile 0 2) (μ : Fin 0 ≃. Fin 2) : p.averageProposerRank μ = 0 := by
  simp [averageProposerRank]

-- A nonempty proposer population facing no partners receives outside-option rank one.
example (p : RankProfile 1 0) : p.averageProposerRank ⊥ = 1 := by
  simp [averageProposerRank, rank]

#print axioms RankProfile.symm_toMarriageMarket
#print axioms RankProfile.rank_injective
#print axioms RankProfile.averageProposerRank_le

end MathEconLibTest.Matching.RankPreferences
