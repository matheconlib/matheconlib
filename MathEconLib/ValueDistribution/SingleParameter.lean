/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.SingleParameter.Basic
public import MathEconLib.ValueDistribution.Basic

/-!
# Expected Quantities in a Single-Parameter Problem

This file connects a deterministic `SingleParameterProblem` to a distribution
of buyer types. It defines expected allocation and expected payment using
mathlib's ordinary integral. The distribution remains separate from the
deterministic problem.

The expected quantities and seller objective are functions of these separate
objects, rather than fields of a new bundled distributed-problem structure.
They impose no measurability, integrability, support, or incentive-compatibility
assumptions. Each theorem can request exactly the assumptions it uses; for
example, a theorem using the problem's type interval can separately assume
that the distribution is supported on that interval.

Mathlib's integral is defined for every function, including functions that are
not integrable. Consequently, a theorem giving these integrals their usual
economic interpretation must establish the relevant measurability and
integrability assumptions.

This module introduces no density abstraction and does not import the auction
layer. Future auction-facing density results should reuse the existing
`Auction.HasDensity` class rather than create a parallel notion here.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory

universe u

namespace ValueDistribution

/-- Expected allocation when buyer types follow the problem's strategy.

The integrand is the induced allocation `P.q`, rather than the primitive
allocation on actions: the distribution is over types, and `P.q value` is the
allocation obtained after type `value` chooses `P.strategy value`. -/
noncomputable def expectedAllocation
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action) : ℝ :=
  ∫ value, P.q value ∂(D : Measure ℝ)

/-- Expected payment made by buyer types following the problem's strategy.

The primitive payment rule takes an action, so the integrand first sends a
type `value` to its chosen action `P.strategy value`, then evaluates
`P.payment` at that action. Positive values are payments by the buyer, in
accordance with the sign convention of `SingleParameterProblem`. -/
noncomputable def expectedPayment
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action) : ℝ :=
  ∫ value, P.payment (P.strategy value) ∂(D : Measure ℝ)

/-! ## Seller objective -/

/-- Expected seller profit from a single buyer.

The seller begins with continuation value `continuationValue`, pays
`acquisitionCost` for approaching the buyer, receives the buyer's expected
payment, and gives up the continuation value in proportion to the expected
allocation.

Here the continuation value is constant across buyer types, and the acquisition
cost is incurred regardless of the buyer's type or the outcome. A future
extension can allow type-dependent continuation values without changing this
definition or its existing consumers. -/
noncomputable def sellerProfit
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    (continuationValue acquisitionCost : ℝ) : ℝ :=
  continuationValue - acquisitionCost + D.expectedPayment P -
    continuationValue * D.expectedAllocation P

/-! ## Reduction -/

/-- Passing to the canonical reduced form preserves expected allocation. -/
theorem expectedAllocation_reduce
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action) :
    D.expectedAllocation P.reduce = D.expectedAllocation P :=
  rfl

/-- Passing to the canonical reduced form preserves expected payment. -/
theorem expectedPayment_reduce
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action) :
    D.expectedPayment P.reduce = D.expectedPayment P :=
  rfl

/-- Passing to the canonical reduced form preserves expected seller profit. -/
theorem sellerProfit_reduce
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    (continuationValue acquisitionCost : ℝ) :
    D.sellerProfit P.reduce continuationValue acquisitionCost =
      D.sellerProfit P continuationValue acquisitionCost :=
  rfl

end ValueDistribution

end

end MathEconLib
