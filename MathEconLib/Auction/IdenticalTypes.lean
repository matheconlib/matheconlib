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

/-- **Linearity + symmetry**: for identically distributed types,
`E[Σ_{j≠i} f(V_j)] = (n−1) · E[f(V₀)]`. -/
theorem expected_sum_erase [HasIdenticalTypes A]
    (f : ℝ → ℝ) (hf_meas : Measurable f) (i : Fin n)
    (hf_int : ∀ j, Integrable (fun ω => f (A.θ j ω)) ℙ) :
    𝔼[fun ω => ∑ j ∈ Finset.univ.erase i, f (A.θ j ω)] =
      (↑(n - 1) : ℝ) * 𝔼[fun ω => f (A.θ 0 ω)] := by
  rw [integral_finset_sum _ (fun j _ => hf_int j)]
  have hsym : ∀ j, ∫ ω, f (A.θ j ω) ∂ℙ = ∫ ω, f (A.θ 0 ω) ∂ℙ := fun j => by
    rw [← integral_map (A.θ_measurable j).aemeasurable
          hf_meas.aestronglyMeasurable,
        (HasIdenticalTypes.θ_identical j 0).map_eq,
        integral_map (A.θ_measurable 0).aemeasurable
          hf_meas.aestronglyMeasurable]
  simp_rw [hsym]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Auction

end

end MathEconLib
