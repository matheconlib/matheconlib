/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.SingleParameter.Payment

/-!
# Myerson's lemma for single-parameter problems

The direct problem associated with an allocation and payment rule, the canonical Myerson payment,
and the equivalence between implementability and monotonicity.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace SingleParameterProblem

/-- The direct single-parameter problem with truthful reporting. -/
def directProblem (lowestType highestType : ℝ) (x : ℝ → ℝ)
    (hx : ∀ v, x v ∈ Icc 0 1) (payment : ℝ → ℝ) : SingleParameterProblem ℝ where
  lowestType := lowestType
  highestType := highestType
  allocation := x
  allocation_range := hx
  payment := payment
  strategy := id

/-- The reduced allocation of a direct problem is its allocation rule. -/
@[simp] lemma directProblem_q (lowestType highestType : ℝ) (x : ℝ → ℝ)
    (hx : ∀ v, x v ∈ Icc 0 1) (payment : ℝ → ℝ) (v : ℝ) :
    (directProblem lowestType highestType x hx payment).q v = x v :=
  rfl

/-- Utility in a direct problem is value times allocation minus payment. -/
@[simp] lemma directProblem_U (lowestType highestType : ℝ) (x : ℝ → ℝ)
    (hx : ∀ v, x v ∈ Icc 0 1) (payment : ℝ → ℝ) (v : ℝ) :
    (directProblem lowestType highestType x hx payment).U v = v * x v - payment v :=
  rfl

/-- The type interval of a direct problem is its declared closed interval. -/
@[simp] lemma directProblem_typeInterval (lowestType highestType : ℝ) (x : ℝ → ℝ)
    (hx : ∀ v, x v ∈ Icc 0 1) (payment : ℝ → ℝ) :
    (directProblem lowestType highestType x hx payment).typeInterval =
      Icc lowestType highestType :=
  rfl

/-- Every problem's reduced form is its associated direct problem. -/
theorem reduce_eq_directProblem {Action : Type*} (P : SingleParameterProblem Action) :
    P.reduce = directProblem P.lowestType P.highestType P.q P.q_range
      (fun w => P.payment (P.strategy w)) :=
  rfl

/-- The canonical payment implementing an allocation with zero utility for the lowest type. -/
def myersonPayment (lowestType : ℝ) (x : ℝ → ℝ) (v : ℝ) : ℝ :=
  v * x v - ∫ w in lowestType..v, x w

/-- The direct problem using the canonical Myerson payment. -/
def myersonProblem (lowestType highestType : ℝ) (x : ℝ → ℝ)
    (hx : ∀ v, x v ∈ Icc 0 1) : SingleParameterProblem ℝ :=
  directProblem lowestType highestType x hx (myersonPayment lowestType x)

/-- The reduced allocation of a Myerson problem is its allocation rule. -/
@[simp] lemma myersonProblem_q (lowestType highestType : ℝ) (x : ℝ → ℝ)
    (hx : ∀ v, x v ∈ Icc 0 1) (v : ℝ) :
    (myersonProblem lowestType highestType x hx).q v = x v :=
  rfl

/-- The payment rule of a Myerson problem is the canonical Myerson payment. -/
@[simp] lemma myersonProblem_payment (lowestType highestType : ℝ) (x : ℝ → ℝ)
    (hx : ∀ v, x v ∈ Icc 0 1) (v : ℝ) :
    (myersonProblem lowestType highestType x hx).payment v = myersonPayment lowestType x v :=
  rfl

/-- Utility in the Myerson problem is the integral of the allocation from the lowest type. -/
theorem myersonProblem_U (lowestType highestType : ℝ) (x : ℝ → ℝ)
    (hx : ∀ v, x v ∈ Icc 0 1) (v : ℝ) :
    (myersonProblem lowestType highestType x hx).U v = ∫ w in lowestType..v, x w := by
  simp only [myersonProblem, directProblem_U, myersonPayment]
  ring

/-- The Myerson normalization gives the lowest type zero utility. -/
theorem myersonProblem_hasZeroLowestTypeUtility (lowestType highestType : ℝ)
    (x : ℝ → ℝ) (hx : ∀ v, x v ∈ Icc 0 1) :
    (myersonProblem lowestType highestType x hx).HasZeroLowestTypeUtility := by
  change (myersonProblem lowestType highestType x hx).U lowestType = 0
  rw [myersonProblem_U]
  exact intervalIntegral.integral_same

/-- The Myerson problem is individually rational; monotonicity is not required. -/
theorem myersonProblem_isIndividuallyRational (lowestType highestType : ℝ)
    (x : ℝ → ℝ) (hx : ∀ v, x v ∈ Icc 0 1) :
    (myersonProblem lowestType highestType x hx).IsIndividuallyRational := by
  intro v hv
  rw [myersonProblem_U]
  exact intervalIntegral.integral_nonneg hv.1 fun w _ => (hx w).1

/-- A monotone allocation is type-deviation incentive compatible under the Myerson payment. -/
theorem myersonProblem_hasTypeDeviationIC (lowestType highestType : ℝ)
    (x : ℝ → ℝ) (hx : ∀ v, x v ∈ Icc 0 1)
    (hmono : MonotoneOn x (Icc lowestType highestType)) :
    HasTypeDeviationIC (myersonProblem lowestType highestType x hx) := by
  apply (myersonProblem lowestType highestType x hx).typeDeviationIC_of_monotone_q
  · simpa using hmono
  · intro v hv
    change myersonPayment lowestType x v =
      v * x v - (myersonProblem lowestType highestType x hx).U lowestType -
        ∫ w in lowestType..v, x w
    rw [myersonProblem_U]
    simp [myersonPayment]

/-- For a direct problem, type-deviation IC is universal IC over the report interval. -/
theorem myersonProblem_hasUniversalIC (lowestType highestType : ℝ)
    (x : ℝ → ℝ) (hx : ∀ v, x v ∈ Icc 0 1)
    (hmono : MonotoneOn x (Icc lowestType highestType)) :
    HasUniversalIC (myersonProblem lowestType highestType x hx)
      (Icc lowestType highestType) := by
  have hic := myersonProblem_hasTypeDeviationIC lowestType highestType x hx hmono
  exact
    { strategyInS := fun _ hv => hv
      universalIC := fun v hv w hw => hic.typeDeviationIC v hv w hw }

/-- Envelope IC of a direct problem forces its allocation to be monotone. -/
theorem monotoneOn_of_hasEnvelopeIC_directProblem (lowestType highestType : ℝ)
    (x : ℝ → ℝ) (hx : ∀ v, x v ∈ Icc 0 1) (payment : ℝ → ℝ)
    (h : HasEnvelopeIC (directProblem lowestType highestType x hx payment)) :
    MonotoneOn x (Icc lowestType highestType) := by
  letI := h
  simpa using (directProblem lowestType highestType x hx payment).q_monotoneOn

/-- **Myerson's lemma.** A direct allocation is implementable exactly when it is monotone. -/
theorem exists_hasTypeDeviationIC_directProblem_iff_monotoneOn
    (lowestType highestType : ℝ) (x : ℝ → ℝ) (hx : ∀ v, x v ∈ Icc 0 1) :
    (∃ payment : ℝ → ℝ,
      HasTypeDeviationIC (directProblem lowestType highestType x hx payment)) ↔
      MonotoneOn x (Icc lowestType highestType) := by
  constructor
  · rintro ⟨payment, hic⟩
    letI := hic
    exact monotoneOn_of_hasEnvelopeIC_directProblem
      lowestType highestType x hx payment inferInstance
  · intro hmono
    refine ⟨myersonPayment lowestType x, ?_⟩
    exact myersonProblem_hasTypeDeviationIC lowestType highestType x hx hmono

/-- Under envelope IC and the zero-rent normalization, on-strategy payments equal the canonical
Myerson payment. -/
theorem payment_eq_myersonPayment {Action : Type*} (P : SingleParameterProblem Action)
    [HasEnvelopeIC P] (hU0 : P.HasZeroLowestTypeUtility) (v : ℝ)
    (hv : v ∈ P.typeInterval) :
    P.payment (P.strategy v) = myersonPayment P.lowestType P.q v := by
  rw [P.payment_identity v hv, myersonPayment, hU0]
  ring

end SingleParameterProblem

end
