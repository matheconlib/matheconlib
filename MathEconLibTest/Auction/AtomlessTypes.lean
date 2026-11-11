/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

import MathEconLib.Auction.Typeclasses

/-!
# Atomless types for every bidder

Regression checks for #214. `HasAtomlessTypes` previously constrained only bidder `0`, so a
family whose other bidders have point-mass types could still satisfy it. The class now requires
every bidder's type law to be atomless.

The negative control is the issue's counterexample in general form: a bidder whose type is
constant has a point-mass law, so no auction with such a bidder satisfies `HasAtomlessTypes`.
The positive check extracts atomlessness for an arbitrary bidder without identical types.
-/

open MathEconLib MeasureTheory ProbabilityTheory

namespace MathEconLibTest.AtomlessTypes

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n]

/-- Atomlessness is available for every bidder, with no identical-types assumption. -/
example (A : Auction Ω n) [A.HasAtomlessTypes] (i : Fin n) (x : ℝ) :
    Measure.map (A.θ i) ℙ {x} = 0 := by
  have : NullSingletonClass (Measure.map (A.θ i) ℙ) := Auction.HasAtomlessTypes.θ_noAtoms i
  exact measure_singleton x

/-- A bidder with a constant type rules out `HasAtomlessTypes`, whichever bidder it is. Under the
previous bidder-`0` field, any constant bidder `i ≠ 0` went undetected. -/
theorem not_hasAtomlessTypes_of_const (A : Auction Ω n) (i : Fin n) (c : ℝ)
    (hc : ∀ ω, A.θ i ω = c) : ¬ A.HasAtomlessTypes := by
  intro h
  have : NullSingletonClass (Measure.map (A.θ i) ℙ) := h.θ_noAtoms i
  have hzero : Measure.map (A.θ i) ℙ {c} = 0 := measure_singleton c
  have hfun : A.θ i = fun _ => c := funext hc
  rw [hfun, Measure.map_const] at hzero
  simp at hzero

end MathEconLibTest.AtomlessTypes
