/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# A genuinely infinite client of the infinite-data Afriat theorem

At the fixed price vector `(1, 0)`, observation `n` chooses `(n, 0)`.
The choices are pairwise distinct, the second good is free, and observation
zero has zero choice and zero income. Utility equal to the first coordinate
rationalizes the observations. The terminal declaration also invokes the
general infinite-data characterization. All premises are proved for these exact
illustrative observations; these are not empirical estimates.

Adapted from Victor H. Aguiar's Apache-2.0
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), module `RenyInfiniteExample`.
-/

set_option autoImplicit false

@[expose] public section

namespace MathEconLibExamples.RevealedPreference.RenyInfinite

open MathEconLib.RevealedPreference

def price (_n : ℕ) : Bundle 2 := ![1, 0]

def choice (n : ℕ) : Bundle 2 := ![(n : ℝ), 0]

def firstGoodUtility (x : Bundle 2) : ℝ := x 0

theorem price_admissible : RenyPriceAdmissible price := by
  intro n
  constructor
  · intro i
    fin_cases i <;> norm_num [price]
  · intro hzero
    have hcoord := congrFun hzero (0 : Fin 2)
    norm_num [price] at hcoord

theorem choice_admissible : RenyChoiceAdmissible choice := by
  intro n i
  fin_cases i <;> simp [choice]

/-- Every natural-number observation has a different chosen bundle. -/
theorem choice_injective : Function.Injective choice := by
  intro m n hmn
  have hcoord := congrFun hmn (0 : Fin 2)
  simpa [choice] using hcoord

/-- The distinct observations do not come from repeating a finite dataset. -/
theorem infinitely_many_choices : Set.Infinite (Set.range choice) :=
  Set.infinite_range_of_injective choice_injective

theorem zero_observation_choice : choice 0 = 0 := by
  ext i
  fin_cases i <;> simp [choice]

theorem first_good_rationalizes :
    rawRenyRationalizes price choice firstGoodUtility := by
  intro n y _hy
  constructor
  · intro hbudget
    simpa [price, choice, firstGoodUtility, dot, Fin.sum_univ_succ, Matrix.vecHead] using hbudget
  · intro hbudget
    simpa [price, choice, firstGoodUtility, dot, Fin.sum_univ_succ, Matrix.vecHead] using hbudget

theorem graph_garp : GraphGARP price choice :=
  graphGARP_of_rawRenyRationalizes price choice firstGoodUtility
    choice_admissible first_good_rationalizes

/-- A concrete, genuinely infinite downstream application of Reny's theorem. -/
theorem has_regular_rationalization : HasRegularRenyRationalization price choice := by
  exact (infinite_graphGARP_iff_regularRenyRationalization (by decide) price choice
    price_admissible choice_admissible).mp graph_garp

end MathEconLibExamples.RevealedPreference.RenyInfinite
