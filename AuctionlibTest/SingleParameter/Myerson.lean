/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

import Auctionlib.SingleParameter.Myerson

/-!
# Compatibility checks for Myerson's lemma

Compile-time pins for the direct problem, canonical payment, and implementability theorem.
-/

open MeasureTheory Set

noncomputable section

namespace SingleParameterMyersonCompatibility

open SingleParameterProblem

variable (lowestType highestType : ℝ) (x : ℝ → ℝ) (hx : ∀ v, x v ∈ Icc 0 1)

example (payment : ℝ → ℝ) (v : ℝ) :
    (directProblem lowestType highestType x hx payment).q v = x v :=
  directProblem_q lowestType highestType x hx payment v

example (payment : ℝ → ℝ) (v : ℝ) :
    (directProblem lowestType highestType x hx payment).U v = v * x v - payment v :=
  directProblem_U lowestType highestType x hx payment v

example (payment : ℝ → ℝ) :
    (directProblem lowestType highestType x hx payment).typeInterval =
      Icc lowestType highestType :=
  rfl

example {Action : Type*} (P : SingleParameterProblem Action) :
    P.reduce = directProblem P.lowestType P.highestType P.q P.q_range
      (fun w => P.payment (P.strategy w)) :=
  rfl

example (v : ℝ) :
    myersonPayment lowestType x v = v * x v - ∫ w in lowestType..v, x w :=
  rfl

example (v : ℝ) :
    (myersonProblem lowestType highestType x hx).U v = ∫ w in lowestType..v, x w :=
  myersonProblem_U lowestType highestType x hx v

example :
    (myersonProblem lowestType highestType x hx).HasZeroLowestTypeUtility :=
  myersonProblem_hasZeroLowestTypeUtility lowestType highestType x hx

example :
    (myersonProblem lowestType highestType x hx).IsIndividuallyRational :=
  myersonProblem_isIndividuallyRational lowestType highestType x hx

example (hmono : MonotoneOn x (Icc lowestType highestType)) :
    HasTypeDeviationIC (myersonProblem lowestType highestType x hx) :=
  myersonProblem_hasTypeDeviationIC lowestType highestType x hx hmono

example (hmono : MonotoneOn x (Icc lowestType highestType)) :
    HasUniversalIC (myersonProblem lowestType highestType x hx)
      (Icc lowestType highestType) :=
  myersonProblem_hasUniversalIC lowestType highestType x hx hmono

example :
    (∃ payment : ℝ → ℝ,
      HasTypeDeviationIC (directProblem lowestType highestType x hx payment)) ↔
      MonotoneOn x (Icc lowestType highestType) :=
  exists_hasTypeDeviationIC_directProblem_iff_monotoneOn lowestType highestType x hx

example {Action : Type*} (P : SingleParameterProblem Action) [HasEnvelopeIC P]
    (hU0 : P.HasZeroLowestTypeUtility) (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.payment (P.strategy v) = myersonPayment P.lowestType P.q v :=
  P.payment_eq_myersonPayment hU0 v hv

/-! ## Revenue equivalence -/

/- The generic payment-uniqueness theorem reproduces revenue equivalence for two direct mechanisms
with the same allocation and lowest-type utility. -/

example (payment₁ payment₂ : ℝ → ℝ)
    (hIC₁ : HasEnvelopeIC (directProblem lowestType highestType x hx payment₁))
    (hIC₂ : HasEnvelopeIC (directProblem lowestType highestType x hx payment₂))
    (hU0 : (directProblem lowestType highestType x hx payment₁).U lowestType =
      (directProblem lowestType highestType x hx payment₂).U lowestType)
    (v : ℝ) (hv : v ∈ Icc lowestType highestType) : payment₁ v = payment₂ v := by
  let P₁ := directProblem lowestType highestType x hx payment₁
  let P₂ := directProblem lowestType highestType x hx payment₂
  letI : HasEnvelopeIC P₁ := hIC₁
  letI : HasEnvelopeIC P₂ := hIC₂
  simpa [P₁, P₂] using P₁.payment_unique P₂ rfl rfl rfl hU0 v hv

end SingleParameterMyersonCompatibility

end
