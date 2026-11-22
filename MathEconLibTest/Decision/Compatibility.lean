/-
Copyright (c) 2026 Siyang Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siyang Liu
-/
module

import MathEconLib.Decision.RiskAversion

/-!
# Compatibility pins for risk aversion over finite lotteries

Compile-time checks of the public statements of `MathEconLib.Decision.RiskAversion`. Each pin
fixes a declaration's type, so an accidental change to a hypothesis or conclusion fails the build.
This module contains only `example`s and belongs to `MathEconLibTest`.
-/

-- This module only contains `example`s, which are never public.
set_option linter.privateModule false

open MathEconLib.Decision MathEconLib.Probability

namespace DecisionCompatibility

example {u : ℝ → ℝ} {I : Set ℝ} (hu : ConcaveOn ℝ I u) :
    LotteryRiskAverse u I :=
  lotteryRiskAverse_of_concaveOn hu

example {u : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I) (hu : LotteryRiskAverse u I) :
    ConcaveOn ℝ I u :=
  concaveOn_of_lotteryRiskAverse hI hu

example {u : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I) :
    LotteryRiskAverse u I ↔ ConcaveOn ℝ I u :=
  lotteryRiskAverse_iff_concaveOn hI

example {u : ℝ → ℝ} {I : Set ℝ} (hu : LotteryRiskAverse u I) {α : Type*} [Fintype α]
    (d : FinDist α) (x : α → ℝ) (hx : ∀ a, 0 < d.pmf a → x a ∈ I) :
    d.expect (u ∘ x) ≤ u (d.expect x) :=
  hu.expect_comp_le d x hx

example {α : Type*} [Fintype α] {I : Set ℝ} (hI : Convex ℝ I) (d : FinDist α) {x : α → ℝ}
    (hx : ∀ a, 0 < d.pmf a → x a ∈ I) : d.expect x ∈ I :=
  FinDist.expect_mem_of_convex hI d hx

end DecisionCompatibility
