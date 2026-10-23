/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Mechanism.Core.BayesianIC

/-!
# General BIC permits interdependent valuations

Reports choose an outcome vector. Each agent values accurate matching to its own true type,
plus the other agent's true type. The latter makes values interdependent, even though truthful
reporting remains optimal. A Dirac prior and its constant conditional-belief version make all
integrability and equilibrium checks explicit. Incentive comparisons cover all real reports.
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
theorem bic : DirectMechanism.IsBIC environment mechanism prior beliefs := by
  refine ⟨?_, ?_⟩
  · intro i s _ r _
    exact integrable_dirac (by simp)
  · intro i s _ r _
    simp only [DirectMechanism.interimUtility_eq_integral, beliefs, Kernel.const_apply,
      integral_dirac, QuasilinearEnvironment.utility, environment, mechanism,
      Function.update_self, insert_self, add_zero]
    nlinarith [sq_nonneg (r - s)]

/-- The general conditional incentive predicate connects to the existing truthful BNE API. -/
theorem truthful_bne : (mechanism.inducedBayesianGame environment).IsBNE prior
    (DirectMechanism.truthfulStrategy environment mechanism) := by
  apply DirectMechanism.IsBIC.isBNE environment mechanism prior beliefs bic
  · intro i
    change Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦
      -((p.1 i - p.2 i) ^ 2) + p.2 (1 - i) + 0)
    fun_prop
  · intro i
    exact integrable_dirac (by simp)

end MathEconLibTest.GeneralBayesianIC
