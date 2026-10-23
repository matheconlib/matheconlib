/-
Copyright (c) 2026 Ruiz Chen, Jujian Zhang, Scott Duke Kominers, Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen, Jujian Zhang, Scott Duke Kominers, Bo Cowgill
-/
module

public import MathEconLib.Auction.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.CDF

import MathEconLib.ForMathlib.IndepFun

/-! # Auction Environment Typeclasses (Section 3a) -/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n]

namespace Auction

/-! ### Composable typeclasses -/

/-- All bidders share the same type distribution and bounds (symmetric bidders). -/
class HasIdenticalTypes (A : Auction Ω n) : Prop where
  θ_identical : ∀ i j, IdentDistrib (A.θ i) (A.θ j) ℙ ℙ
  θmin_eq : ∀ i, A.θmin i = A.θmin 0
  θmax_eq : ∀ i, A.θmax i = A.θmax 0

/-- Each bidder's type lies in the declared interval. -/
class HasBoundedTypes (A : Auction Ω n) : Prop where
  θ_in : ∀ i (ω : Ω), A.θ i ω ∈ Icc (A.θmin i) (A.θmax i)

/-- Each bidder's type distribution has a density w.r.t. Lebesgue measure. -/
class HasDensity (A : Auction Ω n) : Prop where
  θ_hasPDF : ∀ i, HasPDF (A.θ i) ℙ volume

/-- The type distribution is atomless. -/
class HasAtomlessTypes (A : Auction Ω n) : Prop where
  θ_noAtoms : NullSingletonClass (Measure.map (A.θ 0) ℙ)

/-! ### IsSymmetricIPV (convenience bundle) -/

/-- Symmetric IPV: all five properties bundled. -/
class IsSymmetricIPV (A : Auction Ω n) : Prop extends
    HasIndependentTypes A, HasIdenticalTypes A, HasBoundedTypes A,
    HasDensity A, HasAtomlessTypes A

/-! ### Common type bounds (needs HasIdenticalTypes) -/

variable (A : Auction Ω n)

noncomputable def lowestType [HasIdenticalTypes A] : ℝ := A.θmin 0

@[simp] lemma θmin_eq_lowestType [HasIdenticalTypes A] (i) :
    A.θmin i = A.lowestType := by
  rw [HasIdenticalTypes.θmin_eq]; rfl

noncomputable def highestType [HasIdenticalTypes A] : ℝ := A.θmax 0

@[simp] lemma θmax_eq_highestType [HasIdenticalTypes A] (i) :
    A.θmax i = A.highestType := by
  rw [HasIdenticalTypes.θmax_eq]; rfl

/-! ### Common CDF (needs HasIdenticalTypes) -/

-- Compatibility name; Mathlib now supplies the instance.
theorem isProbabilityMeasure_map_θ₀ :
    IsProbabilityMeasure (Measure.map (A.θ 0) ℙ) :=
  inferInstance

/-- The common CDF: `F(s) = cdf(Measure.map (θ₀) ℙ)(s)`. -/
noncomputable abbrev commonCDF [HasIdenticalTypes A] (s : ℝ) : ℝ :=
  ProbabilityTheory.cdf (Measure.map (A.θ 0) ℙ) s

set_option linter.unusedSectionVars false in
lemma commonCDF_nonneg [HasIdenticalTypes A] (s : ℝ) :
    0 ≤ A.commonCDF s := cdf_nonneg _ s

set_option linter.unusedSectionVars false in
lemma commonCDF_le_one [HasIdenticalTypes A] (s : ℝ) :
    A.commonCDF s ≤ 1 := cdf_le_one _ s

set_option linter.unusedSectionVars false in
lemma commonCDF_mono [HasIdenticalTypes A] :
    Monotone A.commonCDF := monotone_cdf _

lemma commonCDF_measurable [HasIdenticalTypes A] :
    Measurable A.commonCDF := (A.commonCDF_mono).measurable

lemma commonCDF_eq [HasIdenticalTypes A] (s : ℝ) :
    A.commonCDF s = Measure.real ℙ (A.θ 0 ⁻¹' Iic s) := by
  simp [ProbabilityTheory.cdf_eq_real, Measure.real,
    Measure.map_apply (A.θ_measurable 0) measurableSet_Iic]

/-! ### CDF boundary values (needs HasIdenticalTypes + HasBoundedTypes + HasAtomlessTypes) -/

@[simp] lemma commonCDF_lowestType
    [HasIdenticalTypes A] [HasBoundedTypes A] [HasAtomlessTypes A] :
    A.commonCDF A.lowestType = 0 := by
  rw [A.commonCDF_eq, Measure.real]
  suffices h : ℙ (A.θ 0 ⁻¹' Iic A.lowestType) = 0 by simp [h]
  have heq : A.θ 0 ⁻¹' Iic A.lowestType = A.θ 0 ⁻¹' {A.lowestType} := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_singleton_iff]
    constructor
    · intro h
      have hθ := HasBoundedTypes.θ_in (A := A) 0 ω
      rw [A.θmin_eq_lowestType] at hθ
      exact le_antisymm h hθ.1
    · intro h; exact le_of_eq h
  rw [heq, ← Measure.map_apply (A.θ_measurable 0) (measurableSet_singleton _)]
  have : NullSingletonClass (Measure.map (A.θ 0) ℙ) := HasAtomlessTypes.θ_noAtoms
  exact measure_singleton _

@[simp] lemma commonCDF_highestType
    [HasIdenticalTypes A] [HasBoundedTypes A] :
    A.commonCDF A.highestType = 1 := by
  rw [A.commonCDF_eq]
  have huniv : A.θ 0 ⁻¹' Iic A.highestType = Set.univ := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
    have hθ := HasBoundedTypes.θ_in (A := A) 0 ω
    rw [A.θmax_eq_highestType] at hθ
    exact hθ.2
  simp [huniv]

/-! ### Lowest-type normalization and revenue -/

/-- Zero lowest-type utility: the participation constraint binds at the lowest
type, so the lowest type earns exactly zero. This is the normalization used by
revenue equivalence; the actual participation predicates are the `InterimIR`
family. Matches `SingleParameterProblem.HasZeroLowestTypeUtility`. -/
class HasZeroLowestTypeUtility [HasIdenticalTypes A] : Prop where
  zeroLowestTypeUtility : ∀ i, A.U i A.lowestType = 0

/-- Expected realized truthful revenue under the joint law of all bidder types. This definition
allows correlated types. As a totalized Bochner integral it is zero for a nonintegrable revenue;
economic uses should establish integrability. -/
noncomputable def expectedRevenue : ℝ :=
  𝔼[fun ω => A.rules.revenue (A.θ · ω)]

omit [NeZero n] in
/-- A bidder's type is independent of the profile with its own coordinate replaced by zero. -/
private lemma indepFun_type_update [A.HasIndependentTypes] (i : Fin n) :
    IndepFun (A.θ i) (fun ω => Function.update (A.θ · ω) i 0) ℙ := by
  classical
  let S : Finset (Fin n) := {i}
  let T : Finset (Fin n) := Finset.univ.erase i
  have hST : Disjoint S T := by simp [S, T]
  have h := iIndepFun.indepFun_finset S T hST
    (HasIndependentTypes.θ_indep (A := A)) A.θ_measurable
  let f : (S → ℝ) → ℝ := fun x => x ⟨i, by simp [S]⟩
  let g : (T → ℝ) → (Fin n → ℝ) :=
    fun x j => if hj : j = i then 0 else x ⟨j, by simp [T, hj]⟩
  have hf : Measurable f := measurable_pi_apply _
  have hg : Measurable g := by
    apply Measurable.of_eval
    intro j
    by_cases hj : j = i
    · simp only [g, dite_eq_left hj]
      exact measurable_const
    · simp only [g, dite_eq_right hj]
      exact measurable_pi_apply _
  have hc := h.comp hf hg
  have hleft : (f ∘ fun (ω : Ω) (j : S) ↦ A.θ j ω) = A.θ i := rfl
  have hright : (g ∘ fun (ω : Ω) (j : T) ↦ A.θ j ω) =
      (fun ω ↦ Function.update (A.θ · ω) i 0) := by
    funext ω j
    by_cases hj : j = i
    · subst j; simp [g]
    · simp [g, hj]
  rw [hleft, hright] at hc
  exact hc

omit [NeZero n] in
/-- Under independent types, a measurable, integrable realized payment has the same expectation as
the marginal interim payment evaluated at the bidder's own type. -/
lemma integral_payment_eq_integral_p [A.HasIndependentTypes]
    (i : Fin n) (hm : Measurable (A.rules.payment i))
    (hi : Integrable (fun ω => A.rules.payment i (A.θ · ω)) ℙ) :
    (∫ ω, A.rules.payment i (A.θ · ω) ∂ℙ) = ∫ ω, A.p i (A.θ i ω) ∂ℙ := by
  let Y : Ω → (Fin n → ℝ) := fun ω => Function.update (A.θ · ω) i 0
  let h : ℝ → (Fin n → ℝ) → ℝ := fun x y => A.rules.payment i (Function.update y i x)
  have hXY : IndepFun (A.θ i) Y ℙ := A.indepFun_type_update i
  have hY : Measurable Y := measurable_update_left.comp
    (Measurable.of_eval A.θ_measurable)
  have hh : Measurable h.uncurry := hm.comp (measurable_update'.comp
    (measurable_snd.prodMk measurable_fst))
  have hl : (fun ω => A.rules.payment i (A.θ · ω)) =
      (fun ω => h (A.θ i ω) (Y ω)) := by
    funext ω
    simp [h, Y]
  have hr : (fun ω => A.p i (A.θ i ω)) =
      (fun ω => ∫ ω', h (A.θ i ω) (Y ω') ∂ℙ) := by
    funext ω
    simp [p, p_strat, h, Y]
  rw [hl, hr]
  exact integral_indep_swap hXY (A.θ_measurable i) hY h hh (hl ▸ hi)

omit [NeZero n] in
/-- Independent types and measurable, integrable realized payments justify computing actual
expected revenue as the sum of expected marginal interim payments. -/
lemma expectedRevenue_eq_sum_integral_p [A.HasIndependentTypes]
    (hm : ∀ i, Measurable (A.rules.payment i))
    (hi : ∀ i, Integrable (fun ω => A.rules.payment i (A.θ · ω)) ℙ) :
    A.expectedRevenue = ∑ i : Fin n, ∫ ω, A.p i (A.θ i ω) ∂ℙ := by
  unfold expectedRevenue
  simp_rw [Mechanism.revenue_eq_sum_payment]
  rw [integral_finsetSum _ fun i _ => hi i]
  exact Finset.sum_congr rfl fun i _ => A.integral_payment_eq_integral_p i (hm i) (hi i)

end Auction

end

end MathEconLib
