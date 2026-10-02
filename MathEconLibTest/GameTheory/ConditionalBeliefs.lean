/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Beliefs

/-!
# Conditional-belief versions on binary type spaces

Two-player binary examples distinguish conditional from unconditional opponent beliefs and show
that valid disintegrations may differ at null types. The player's own type remains the specified
type under every opponent-belief version.

## Main definitions

* `nullPrior`: both players have type false with probability one.
* `constantBeliefs`, `matchingBeliefs`: versions that disagree at the null type true.
* `correlatedPrior`, `correlatedBeliefs`: equally likely common binary types and their conditional
  opponent beliefs.

## Main statements

* Two versions of conditional beliefs can disagree at a type of marginal probability zero.
* Under perfect correlation, conditional opponent beliefs differ from the unconditional law.
* `isIndependentOfOpponents_nullPrior`: degenerate own and opponent types are independent.

## Tags

conditional beliefs, correlation, null types, disintegration
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory MathEconLib.GameTheory.BayesianPrior

open scoped ENNReal

namespace MathEconLibTest.ConditionalBeliefs

/-- Binary types carry the discrete measurable space. -/
local instance : MeasurableSpace Bool := ⊤
/-- Every singleton of binary types is measurable. -/
local instance : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

/-- Both players share the same binary type. -/
def profile (t : Bool) : Bool → Bool := fun _ => t

/-- Opponents share the specified binary type. -/
def opponents (i : Bool) (t : Bool) : OpponentProfile (fun _ : Bool => Bool) i := fun _ => t

/-- The prior concentrates on the false type profile. -/
def nullPrior : Measure (Bool → Bool) := Measure.dirac (profile false)

/-- The degenerate prior has total mass one. -/
instance : IsProbabilityMeasure nullPrior :=
  inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))

/-- Beliefs assign probability one to opponents having false type at every own type. -/
def constantBeliefs : ConditionalBeliefs nullPrior where
  opponents i := Kernel.const Bool (Measure.dirac (opponents i false))
  isMarkov _ := inferInstance
  disintegrates i := by
    change (Measure.map (fun θ : Bool → Bool => θ i) (Measure.dirac (profile false))).compProd _ = _
    rw [Measure.map_dirac (measurable_pi_apply i)]
    change (Measure.dirac false).compProd _ =
      (Measure.dirac (profile false)).map (fun θ => (θ i, drop i θ))
    rw [Measure.map_dirac ((measurable_pi_apply i).prodMk (measurable_drop i))]
    ext s hs
    rw [Measure.dirac_compProd_apply hs]
    simp only [Kernel.const_apply, Measure.dirac_apply]
    rfl

/-- Beliefs assign probability one to opponents matching own type, including the null true type. -/
def matchingBeliefs : ConditionalBeliefs nullPrior where
  opponents i := Kernel.deterministic (opponents i) (measurable_of_countable _)
  isMarkov _ := inferInstance
  disintegrates i := by
    change (Measure.map (fun θ : Bool → Bool => θ i) (Measure.dirac (profile false))).compProd _ = _
    rw [Measure.map_dirac (measurable_pi_apply i)]
    change (Measure.dirac false).compProd _ =
      (Measure.dirac (profile false)).map (fun θ => (θ i, drop i θ))
    rw [Measure.map_dirac ((measurable_pi_apply i).prodMk (measurable_drop i))]
    ext s hs
    rw [Measure.dirac_compProd_apply hs]
    simp only [Kernel.deterministic_apply, Measure.dirac_apply]
    rfl

/-- The type true has zero marginal probability. -/
example (i : Bool) : marginalType nullPrior i {true} = 0 := by
  simp [marginalType, nullPrior, profile, Measure.map_dirac (measurable_pi_apply i)]

/-- Two valid belief versions can give different laws at a null type. -/
example : constantBeliefs.opponents false true ≠ matchingBeliefs.opponents false true := by
  intro h
  have he := congrArg (fun μ => μ {opponents false false}) h
  have hn : opponents false true ≠ opponents false false := by
    intro heq
    have hv := congrFun heq ⟨true, by decide⟩
    exact Bool.noConfusion hv
  simp [constantBeliefs, matchingBeliefs, Kernel.const_apply, Kernel.deterministic_apply,
    hn] at he

/-- The own coordinate is fixed even when opponents' beliefs at that type are arbitrary. -/
example (o : OpponentProfile (fun _ : Bool => Bool) false) : insert false true o false = true :=
  insert_self _ _ _

/-- Degenerate types are independent of opponents. -/
lemma isIndependentOfOpponents_nullPrior : IsIndependentOfOpponents nullPrior := by
  intro i
  rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_drop i).aemeasurable]
  simp only [nullPrior, Measure.map_dirac ((measurable_pi_apply i).prodMk (measurable_drop i)),
    Measure.map_dirac (measurable_pi_apply i), Measure.map_dirac (measurable_drop i),
    Measure.dirac_prod_dirac]

/-- The independent version keeps unconditional opponent beliefs even at the null type true. -/
example (i : Bool) : (independentBeliefs isIndependentOfOpponents_nullPrior).opponents i true =
    nullPrior.map (drop i) := rfl

/-- The perfectly correlated common prior gives equal mass to the two constant profiles. -/
def correlatedPrior : Measure (Bool → Bool) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (profile false) +
    (1 / 2 : ℝ≥0∞) • Measure.dirac (profile true)

/-- The equal mixture of the two constant profiles has total mass one. -/
instance : IsProbabilityMeasure correlatedPrior := ⟨by
  norm_num [correlatedPrior]
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩

/-- The conditional opponent kernel recovers the corresponding constant-type joint law. -/
lemma matching_disintegrates_dirac (i t : Bool) :
    (Measure.dirac t).compProd (Kernel.deterministic (opponents i) (measurable_of_countable _)) =
      Measure.dirac (t, opponents i t) := by
  ext s hs
  rw [Measure.dirac_compProd_apply hs]
  simp only [Kernel.deterministic_apply, Measure.dirac_apply]
  rfl

/-- Perfect correlation means an opponent's type equals the player's observed type. -/
def correlatedBeliefs : ConditionalBeliefs correlatedPrior where
  opponents i := Kernel.deterministic (opponents i) (measurable_of_countable _)
  isMarkov _ := inferInstance
  disintegrates i := by
    simp only [marginalType, correlatedPrior,
      Measure.map_add _ _ (measurable_pi_apply i),
      Measure.map_add _ _ ((measurable_pi_apply i).prodMk (measurable_drop i)), Measure.map_smul,
      Measure.map_dirac (measurable_pi_apply i),
      Measure.map_dirac ((measurable_pi_apply i).prodMk (measurable_drop i)), profile,
      Measure.compProd_add_left, Measure.compProd_smul_left, matching_disintegrates_dirac]
    rfl

/-- Given type true, the opponent is true with certainty; unconditionally that type has mass
half. -/
example : correlatedBeliefs.opponents false true {opponents false true} = 1 ∧
    correlatedPrior.map (drop false) {opponents false true} = 1 / 2 := by
  have hn : opponents false false ≠ opponents false true := by
    intro h
    have hv := congrFun h ⟨true, by decide⟩
    exact Bool.noConfusion hv
  constructor
  · simp [correlatedBeliefs, Kernel.deterministic_apply]
  · simp only [correlatedPrior, Measure.map_add _ _ (measurable_drop false), Measure.map_smul,
      Measure.map_dirac (measurable_drop false), Measure.add_apply, Measure.smul_apply,
      smul_eq_mul]
    change (1 / 2 : ℝ≥0∞) * (Measure.dirac (opponents false false)) {opponents false true} +
      (1 / 2 : ℝ≥0∞) * (Measure.dirac (opponents false true)) {opponents false true} = 1 / 2
    simp [hn]

end MathEconLibTest.ConditionalBeliefs
