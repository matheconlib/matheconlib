module

public import MathEconLib.Auction.Typeclasses
public import MathEconLib.ValueDistribution.Uniform
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Independent uniform values for 2 bidders

This probability space supplies the concrete all-purchase example with 2 bidders.
Each coordinate has the uniform law on `[0, 2]`. Clamping the coordinate to
that interval changes it only on a null set and makes the declared type bounds
hold at every state, as required by `Auction.HasBoundedTypes`.
-/

namespace MathEconLib.Examples.AllPurchase.UniformProbability

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- The common uniform value distribution. -/
def law : ValueDistribution :=
  ValueDistribution.uniformInterval 0 2 (by norm_num)

/-- A named state space keeps the probability measure local to this example. -/
def Ω := Fin 2 → ℝ

instance : MeasureSpace Ω where
  toMeasurableSpace := inferInstanceAs (MeasurableSpace (Fin 2 → ℝ))
  volume := Measure.pi fun _ : Fin 2 => (law : Measure ℝ)

instance : IsProbabilityMeasure (ℙ : Measure Ω) := by
  change IsProbabilityMeasure (Measure.pi fun _ : Fin 2 => (law : Measure ℝ))
  infer_instance

private def clamp (x : ℝ) : ℝ := max 0 (min 2 x)

private theorem measurable_clamp : Measurable clamp := by
  unfold clamp
  fun_prop

private theorem map_clamp : Measure.map clamp (law : Measure ℝ) = law := by
  have heq : clamp =ᵐ[(law : Measure ℝ)] id := by
    filter_upwards [ValueDistribution.uniformInterval_supported 0 2 (by norm_num)]
      with x hx
    simp only [clamp, id_eq, min_eq_right hx.2, max_eq_right hx.1]
  rw [Measure.map_congr heq, Measure.map_id]

/-- Bidder `i`'s value, with pointwise support in `[0, 2]`. -/
def value (i : Fin 2) (ω : Ω) : ℝ := max 0 (min 2 (ω i))

/-- Each value is measurable. -/
theorem measurable_value (i : Fin 2) : Measurable (value i) :=
  measurable_clamp.comp (measurable_pi_apply i)

/-- The stated bounds hold even at states in the null complement of the support. -/
theorem value_mem (i : Fin 2) (ω : Ω) : value i ω ∈ Icc 0 2 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Every bidder's value has the common uniform law. -/
theorem map_value (i : Fin 2) : Measure.map (value i) ℙ = (law : Measure ℝ) := by
  change Measure.map (clamp ∘ Function.eval i)
    (Measure.pi fun _ : Fin 2 => (law : Measure ℝ)) = _
  rw [← Measure.map_map measurable_clamp (measurable_pi_apply i),
    (measurePreserving_eval (fun _ : Fin 2 => (law : Measure ℝ)) i).map_eq,
    map_clamp]

/-- The 2 values are independent. -/
theorem independent_values : iIndepFun value ℙ := by
  change iIndepFun (fun (i : Fin 2) (ω : Fin 2 → ℝ) => clamp (ω i))
    (Measure.pi fun _ : Fin 2 => (law : Measure ℝ))
  exact iIndepFun_pi (fun _ : Fin 2 => measurable_clamp.aemeasurable)

/-- The 2 values are identically distributed. -/
theorem identical_values (i j : Fin 2) : IdentDistrib (value i) (value j) ℙ ℙ where
  aemeasurable_fst := (measurable_value i).aemeasurable
  aemeasurable_snd := (measurable_value j).aemeasurable
  map_eq := (map_value i).trans (map_value j).symm

/-- The common value law has a Lebesgue density. -/
theorem hasPDF_value (i : Fin 2) : HasPDF (value i) ℙ volume := by
  apply (Real.hasPDF_iff_of_aemeasurable (measurable_value i).aemeasurable).2
  rw [map_value]
  exact ValueDistribution.uniformInterval_absolutelyContinuous 0 2 (by norm_num)

/-- Every value law is atomless. -/
instance noAtoms_value (i : Fin 2) : NoAtoms (Measure.map (value i) ℙ) := by
  rw [map_value]
  exact ValueDistribution.uniformInterval_noAtoms 0 2 (by norm_num)

/-- The uniform CDF on its support. -/
theorem cdf_value (i : Fin 2) (v : ℝ) (hv : v ∈ Icc 0 2) :
    cdf (Measure.map (value i) ℙ) v = v / 2 := by
  rw [map_value]
  simpa [law] using ValueDistribution.uniformInterval_cdf 0 2 (by norm_num) v hv

/-- Bounded measurable state functions are integrable under this probability law. -/
theorem integrable_of_bounded {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hbound : ∀ ω, ‖f ω‖ ≤ C) : Integrable f :=
  (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ hbound)

/-- Each bidder's value is integrable. -/
theorem integrable_value (i : Fin 2) : Integrable (value i) := by
  apply integrable_of_bounded (measurable_value i) (C := 2)
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (value_mem i ω).1]
  exact (value_mem i ω).2

/-- The squared value is integrable. -/
theorem integrable_value_sq (i : Fin 2) : Integrable (fun ω => value i ω ^ 2) := by
  apply integrable_of_bounded ((measurable_value i).pow measurable_const) (C := 4)
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := value_mem i ω
  nlinarith [h.1, h.2, mul_nonneg h.1 (sub_nonneg.mpr h.2)]

/-- Expectations of measurable functions reduce to an elementary interval integral. -/
theorem integral_comp_value (i : Fin 2) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ ω, f (value i ω) ∂ℙ) = (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..2, f x := by
  calc
    (∫ ω, f (value i ω) ∂ℙ) =
        ∫ x, f x ∂Measure.map (value i) ℙ :=
      (integral_map (measurable_value i).aemeasurable hf.aestronglyMeasurable).symm
    _ = (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..2, f x := by
      rw [map_value, law, ValueDistribution.toMeasure_uniformInterval,
        ProbabilityTheory.cond, integral_smul_measure, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 by norm_num)]
      norm_num [Real.volume_Icc]

/-- Each bidder's expected value is `1`. -/
theorem integral_value (i : Fin 2) : (∫ ω, value i ω ∂ℙ) = 1 := by
  have h := integral_comp_value i (f := fun x : ℝ => x ^ 1)
    (measurable_id.pow measurable_const)
  rw [_root_.integral_pow] at h
  norm_num at h
  exact h

/-- The second moment of the uniform law is `4 / 3`. -/
theorem integral_value_sq (i : Fin 2) : (∫ ω, value i ω ^ 2 ∂ℙ) = 4 / 3 := by
  rw [integral_comp_value i (f := fun x : ℝ => x ^ 2)
    (measurable_id.pow measurable_const), _root_.integral_pow]
  norm_num

end

end

end MathEconLib.Examples.AllPurchase.UniformProbability
