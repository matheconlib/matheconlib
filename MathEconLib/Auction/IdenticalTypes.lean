/-
Copyright (c) 2026 Jujian Zhang, Scott Duke Kominers, Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Duke Kominers, Ruiz Chen
-/
module

public import MathEconLib.Auction.Typeclasses

/-!
# Lemmas requiring only `HasIdenticalTypes`

Results that depend on `HasIdenticalTypes` but not the full `IsSymmetricIPV` bundle.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n]

namespace Auction

variable (A : Auction Ω n)

/-- Identically distributed types give equal integrals of a measurable common function.
This is an equality of totalized integrals; economic expectation uses additionally require
integrability. -/
theorem integral_comp_type_eq [HasIdenticalTypes A]
    (f : ℝ → ℝ) (hf : Measurable f) (i j : Fin n) :
    (∫ ω, f (A.θ i ω) ∂ℙ) = ∫ ω, f (A.θ j ω) ∂ℙ :=
  ((HasIdenticalTypes.θ_identical i j).comp hf).integral_eq

/-- A measurable strategy monotone on the bounded common type interval is integrable at
 every bidder's realized type. Endpoint bids provide a uniform integrable bound. -/
theorem integrable_comp_type_of_monotoneOn [HasIdenticalTypes A] [HasBoundedTypes A]
    (f : ℝ → ℝ) (hf : Measurable f)
    (hmono : MonotoneOn f (Icc A.lowestType A.highestType)) (j : Fin n) :
    Integrable (fun ω => f (A.θ j ω)) ℙ := by
  apply (integrable_const (max |f A.lowestType| |f A.highestType|)).mono'
    (hf.comp (A.θ_measurable j)).aestronglyMeasurable
  apply ae_of_all
  intro ω
  have hmem : A.θ j ω ∈ Icc A.lowestType A.highestType := by
    simpa only [θmin_eq_lowestType, θmax_eq_highestType] using
      (HasBoundedTypes.θ_in (A := A) j ω)
  have hlo := hmono ⟨le_rfl, hmem.1.trans hmem.2⟩ hmem hmem.1
  have hhi := hmono hmem ⟨hmem.1.trans hmem.2, le_rfl⟩ hmem.2
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hlo),
    hhi.trans ((le_abs_self _).trans (le_max_right _ _))⟩

/-- **Linearity + symmetry**: for identically distributed types,
`E[Σ_{j≠i} f(V_j)] = (n−1) · E[f(V₀)]`. -/
theorem expected_sum_erase [HasIdenticalTypes A]
    (f : ℝ → ℝ) (hf_meas : Measurable f) (i : Fin n)
    (hf_int : ∀ j, Integrable (fun ω => f (A.θ j ω)) ℙ) :
    𝔼[fun ω => ∑ j ∈ Finset.univ.erase i, f (A.θ j ω)] =
      (↑(n - 1) : ℝ) * 𝔼[fun ω => f (A.θ 0 ω)] := by
  rw [integral_finsetSum _ (fun j _ => hf_int j)]
  have hsym : ∀ j, ∫ ω, f (A.θ j ω) ∂ℙ = ∫ ω, f (A.θ 0 ω) ∂ℙ :=
    fun j => A.integral_comp_type_eq f hf_meas j 0
  simp_rw [hsym]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Auction

end

end MathEconLib
