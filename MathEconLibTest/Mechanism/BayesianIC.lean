/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Mechanism

/-!
# Quasilinear BIC permits interdependent valuations

Reports choose an outcome vector. Each agent values accurate matching to its own true type,
plus the other agent's true type. The latter makes values interdependent, even though truthful
reporting remains optimal. A Dirac prior and its constant conditional-belief version make all
integrability and equilibrium checks explicit. Incentive comparisons cover all real reports.

A separate two-good posted-price client uses vector reports in `ℝ × ℝ` and the same BIC predicate.
It proves truthfulness for all vector reports and evaluates a concrete truthful payment. Both
clients import the public mechanism umbrella so missing exports fail this regression.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory MathEconLib.Mechanism
open MathEconLib.GameTheory.BayesianPrior

namespace MathEconLibTest.GeneralBayesianIC

/-- Values depend on the other agent's true type as well as the chosen outcome. -/
def environment : QuasilinearEnvironment (Fin 2) (fun _ ↦ ℝ) (Fin 2 → ℝ) where
  value i θ o := -((o i - θ i) ^ 2) + θ (1 - i)

/-- Reports choose the matching outcome, with zero transfers. -/
def mechanism : DirectMechanism (Fin 2) (fun _ ↦ ℝ) (Fin 2 → ℝ) where
  outcome r := r
  transfer _ _ := 0

/-- The actual type profile is zero. -/
def prior : Measure (Fin 2 → ℝ) := Measure.dirac 0

instance : IsProbabilityMeasure prior := inferInstanceAs
  (IsProbabilityMeasure (Measure.dirac (0 : Fin 2 → ℝ)))

/-- Constant opponent beliefs select zero also at unrealized own types. -/
def beliefs : ConditionalBeliefs prior where
  opponents i := Kernel.const ℝ (Measure.dirac 0)
  isMarkov _ := inferInstance
  disintegrates i := by
    simp only [marginalType, prior, Measure.compProd_const]
    rw [Measure.map_dirac (measurable_pi_apply i),
      Measure.map_dirac ((measurable_pi_apply i).prodMk (measurable_drop i)),
      Measure.dirac_prod_dirac]
    rfl

/-- Changing the other agent's type changes agent zero's value at a fixed outcome. -/
theorem not_private_values : ¬ environment.IsPrivateValues := by
  intro h
  have hh := congrFun (h 0 (0 : Fin 2 → ℝ) (fun j ↦ if j = 0 then 0 else 1)
    (by norm_num)) 0
  norm_num [environment] at hh

/-- Truthful reports are optimal over the entire real type/report spaces, with integrable
conditional utilities, although the valuation environment is not private values. -/
theorem bic : DirectMechanism.Quasilinear.IsBIC environment mechanism prior beliefs := by
  refine ⟨?_, ?_⟩
  · intro i s _ r _
    exact integrable_dirac (by simp)
  · intro i s _ r _
    simp only [DirectMechanism.Quasilinear.interimUtility_eq_integral, beliefs, Kernel.const_apply,
      integral_dirac, QuasilinearEnvironment.utility, environment, mechanism,
      Function.update_self, insert_self, add_zero]
    nlinarith [sq_nonneg (r - s)]

/-- The general conditional incentive predicate connects to the existing truthful BNE API. -/
theorem truthful_bne : (mechanism.inducedBayesianGame environment).IsBNE prior
    (DirectMechanism.Quasilinear.truthfulStrategy environment mechanism) := by
  apply DirectMechanism.Quasilinear.IsBIC.isBNE environment mechanism prior beliefs bic
  · intro i
    change Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦
      -((p.1 i - p.2 i) ^ 2) + p.2 (1 - i) + 0)
    fun_prop
  · intro i
    exact integrable_dirac (by simp)

end MathEconLibTest.GeneralBayesianIC

namespace MathEconLibTest.TwoDimensionalBayesianIC

/-- Buy each good when its reported value reaches the per-good price one half. -/
def quantity (z : ℝ) : ℝ := if (1 / 2 : ℝ) ≤ z then 1 else 0

/-- Additive private values for two goods. The type is a vector, not a scalar auction value. -/
def environment : QuasilinearEnvironment Unit (fun _ ↦ ℝ × ℝ) (ℝ × ℝ) :=
  QuasilinearEnvironment.ofPrivate fun _ t x ↦ t.1 * x.1 + t.2 * x.2

/-- Separate posted prices for the two goods, with transfers paid by the buyer. -/
def mechanism : DirectMechanism Unit (fun _ ↦ ℝ × ℝ) (ℝ × ℝ) where
  outcome r := (quantity (r ()).1, quantity (r ()).2)
  transfer _ r := -(quantity (r ()).1 + quantity (r ()).2) / 2

/-- The component posted-price inequality holds for all real true values and reports. -/
lemma scalar_ic (s r : ℝ) :
    s * quantity r - quantity r / 2 ≤ s * quantity s - quantity s / 2 := by
  unfold quantity
  split_ifs <;> linarith

/-- The existing quasilinear BIC predicate accepts two-dimensional reports under any prior and
selected conditional beliefs. No multidimensional BIC definition is introduced. -/
theorem bic (μ : Measure (Unit → ℝ × ℝ)) [IsProbabilityMeasure μ]
    (B : ConditionalBeliefs μ) :
    DirectMechanism.Quasilinear.IsBIC environment mechanism μ B := by
  refine ⟨?_, ?_⟩
  · intro i s _ r _
    cases i
    simp [environment, mechanism, QuasilinearEnvironment.ofPrivate]
  · intro i s _ r _
    cases i
    simp only [DirectMechanism.Quasilinear.interimUtility_eq_integral, environment, mechanism,
      QuasilinearEnvironment.utility, QuasilinearEnvironment.ofPrivate,
      Function.update_self, insert_self, integral_const, probReal_univ, one_smul]
    have h₁ := scalar_ic s.1 r.1
    have h₂ := scalar_ic s.2 r.2
    linarith

/-- A concrete buyer values each good at one. -/
def prior : Measure (Unit → ℝ × ℝ) := Measure.dirac (fun _ ↦ (1, 1))

instance : IsProbabilityMeasure prior := inferInstanceAs
  (IsProbabilityMeasure (Measure.dirac (fun _ : Unit ↦ ((1, 1) : ℝ × ℝ))))

/-- The concrete vector-valued model satisfies the existing general incentive predicate. -/
theorem concrete_bic :
    DirectMechanism.Quasilinear.IsBIC environment mechanism prior (canonicalBeliefs prior) :=
  bic prior (canonicalBeliefs prior)

/-- The truthful buyer buys both goods and pays one in total. -/
theorem both_items_payment :
    mechanism.payment () (fun _ ↦ ((1, 1) : ℝ × ℝ)) = 1 := by
  norm_num [mechanism, quantity, MathEconLib.Mechanism.payment]

end MathEconLibTest.TwoDimensionalBayesianIC
