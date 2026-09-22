/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Conditional beliefs about opponents' types

A common prior determines conditional beliefs about opponents' types up to marginal
almost-everywhere agreement. A selected version is a Markov kernel for each player, defined at
every own type. Inserting the player's own type reconstructs the full type profile. The prior need
not determine the selected beliefs on sets of marginal measure zero.

## Main definitions

* `BayesianPrior.ConditionalBeliefs`: Opponent kernels disintegrating the common prior.
* `BayesianPrior.canonicalBeliefs`: A conditional-belief version for standard Borel types.
* `BayesianPrior.independentBeliefs`: Constant opponent beliefs under independence.
* `BayesianPrior.OpponentBeliefsInvariantOn`: Agreement with the unconditional opponent law at
  every own type in a specified set.

## Main statements

* `BayesianPrior.ConditionalBeliefs.ae_eq`: Versions agree almost everywhere with respect to each
  player's own-type marginal.
* `BayesianPrior.ConditionalBeliefs.integral_insert` and
  `BayesianPrior.ConditionalBeliefs.lintegral_insert`: Iterated conditional integrals recover the
  prior integral.

## Tags

bayesian games, conditional beliefs, disintegration, independence
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace Auctionlib.GameTheory.BayesianPrior

variable {I : Type*} {Θ : I → Type*}

/-- The profile of all types other than player `i`'s type. -/
abbrev OpponentProfile (Θ : I → Type*) (i : I) := ∀ j : {j // j ≠ i}, Θ j

/-- Remove a player's type from a full profile. -/
def drop (i : I) (θ : ∀ j, Θ j) : OpponentProfile Θ i := fun j => θ j

/-- Reconstruct a profile with the specified own type and opponents' types. -/
def insert [DecidableEq I] (i : I) (θᵢ : Θ i) (θo : OpponentProfile Θ i) : ∀ j, Θ j :=
  (Equiv.piSplitAt i Θ).symm (θᵢ, θo)

/-- The inserted own type is exactly the specified type. -/
@[simp] lemma insert_self [DecidableEq I] (i : I) (θᵢ : Θ i) (θo : OpponentProfile Θ i) :
    insert i θᵢ θo i = θᵢ := by simp [insert, Equiv.piSplitAt]

/-- Insertion leaves every opponent's type unchanged. -/
@[simp] lemma insert_of_ne [DecidableEq I] (i : I) (θᵢ : Θ i)
    (θo : OpponentProfile Θ i) {j : I} (hj : j ≠ i) :
    insert i θᵢ θo j = θo ⟨j, hj⟩ := by simp [insert, Equiv.piSplitAt, hj]

/-- Removing and reinserting a coordinate recovers the full profile. -/
@[simp] lemma insert_drop [DecidableEq I] (i : I) (θ : ∀ j, Θ j) :
    insert i (θ i) (drop i θ) = θ := (Equiv.piSplitAt i Θ).symm_apply_apply θ

variable [∀ i, MeasurableSpace (Θ i)]

/-- Opponent projection is measurable. -/
@[fun_prop] lemma measurable_drop (i : I) : Measurable (drop (Θ := Θ) i) :=
  measurable_pi_lambda _ fun j => measurable_pi_apply j.val

/-- Inserting own and opponent types is jointly measurable. -/
@[fun_prop] lemma measurable_insert [DecidableEq I] (i : I) :
    Measurable (fun p : Θ i × OpponentProfile Θ i => insert i p.1 p.2) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases hj : j = i
  · subst j
    simpa using (measurable_fst : Measurable (Prod.fst : Θ i × OpponentProfile Θ i → Θ i))
  · simpa [insert_of_ne, hj] using (measurable_pi_apply ⟨j, hj⟩).comp
      (measurable_snd :
        Measurable (Prod.snd : Θ i × OpponentProfile Θ i → OpponentProfile Θ i))

/-- A player's marginal distribution of types. -/
def marginalType (μ : Measure (∀ i, Θ i)) (i : I) : Measure (Θ i) := μ.map (fun θ => θ i)

/-- The own-type marginal of a probability measure is a probability measure. -/
instance (μ : Measure (∀ i, Θ i)) [IsProbabilityMeasure μ] (i : I) :
    IsProbabilityMeasure (marginalType μ i) :=
  Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable

/-- Conditional distributions over opponents that disintegrate the common prior. Each kernel is
defined at every own type; the disintegration identity need not determine its values on sets of
marginal measure zero. -/
structure ConditionalBeliefs (μ : Measure (∀ i, Θ i)) where
  /-- Opponents' conditional type distribution given own type. -/
  opponents : (i : I) → Kernel (Θ i) (OpponentProfile Θ i)
  /-- Every conditional belief is a probability measure. -/
  isMarkov : ∀ i, IsMarkovKernel (opponents i)
  /-- Combining own-type marginals with beliefs recovers the joint law. -/
  disintegrates : ∀ i, (marginalType μ i).compProd (opponents i) =
    μ.map (fun θ => (θ i, drop i θ))

/-- Each player's conditional opponent beliefs form a Markov kernel. -/
instance {μ : Measure (∀ i, Θ i)} (B : ConditionalBeliefs μ) (i : I) :
    IsMarkovKernel (B.opponents i) := B.isMarkov i

/-- The first marginal of the own-type/opponents joint law. -/
@[simp] lemma fst_map_drop (μ : Measure (∀ i, Θ i)) (i : I) :
    (μ.map (fun θ => (θ i, drop i θ))).fst = marginalType μ i := by
  rw [Measure.fst, Measure.map_map measurable_fst
    ((measurable_pi_apply i).prodMk (measurable_drop i))]
  rfl

/-- A selected version of conditional beliefs for a probability prior on a countable product of
nonempty standard Borel type spaces. -/
def canonicalBeliefs [Countable I] [∀ i, StandardBorelSpace (Θ i)]
    [∀ i, Nonempty (Θ i)] (μ : Measure (∀ i, Θ i)) [IsProbabilityMeasure μ] :
    ConditionalBeliefs μ where
  opponents i := (μ.map (fun θ => (θ i, drop i θ))).condKernel
  isMarkov i := inferInstance
  disintegrates i := by
    rw [← fst_map_drop μ i]
    exact Measure.disintegrate _ _

/-- Own type is independent of the entire opponent-type profile. -/
def IsIndependentOfOpponents (μ : Measure (∀ i, Θ i)) : Prop :=
  ∀ i, IndepFun (fun θ => θ i) (drop i) μ

/-- Constant opponent beliefs for a prior with independent own and opponent types. -/
def independentBeliefs {μ : Measure (∀ i, Θ i)} [IsProbabilityMeasure μ]
    (h : IsIndependentOfOpponents μ) : ConditionalBeliefs μ where
  opponents i := Kernel.const (Θ i) (μ.map (drop i))
  isMarkov i := by
    haveI : IsProbabilityMeasure (μ.map (drop i)) :=
      Measure.isProbabilityMeasure_map (measurable_drop i).aemeasurable
    infer_instance
  disintegrates i := by
    rw [Measure.compProd_const]
    exact ((indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_drop i).aemeasurable).mp (h i)).symm

/-- Beliefs equal the unconditional opponent law at every own type in `T`. -/
def OpponentBeliefsInvariantOn {μ : Measure (∀ i, Θ i)} (B : ConditionalBeliefs μ)
    (i : I) (T : Set (Θ i)) : Prop :=
  ∀ θᵢ ∈ T, B.opponents i θᵢ = μ.map (drop i)

/-- The independent version equals the unconditional opponent law at every own type. -/
theorem opponentBeliefsInvariantOn_independentBeliefs {μ : Measure (∀ i, Θ i)}
    [IsProbabilityMeasure μ]
    (h : IsIndependentOfOpponents μ) (i : I) (T : Set (Θ i)) :
    OpponentBeliefsInvariantOn (independentBeliefs h) i T := fun _ _ => rfl

/-- For each player, two versions of conditional beliefs agree on a set of full own-type marginal
measure. -/
theorem ConditionalBeliefs.ae_eq [Countable I] [∀ i, StandardBorelSpace (Θ i)]
    [∀ i, Nonempty (Θ i)] {μ : Measure (∀ i, Θ i)} [IsProbabilityMeasure μ]
    (B B' : ConditionalBeliefs μ) (i : I) :
    B.opponents i =ᵐ[marginalType μ i] B'.opponents i := by
  have h_eq_condKernel (C : ConditionalBeliefs μ) : C.opponents i =ᵐ[marginalType μ i]
      (μ.map (fun θ => (θ i, drop i θ))).condKernel := by
    have heq := eq_condKernel_of_measure_eq_compProd (C.opponents i)
      (by rw [fst_map_drop]; exact (C.disintegrates i).symm)
    simpa using heq
  exact (h_eq_condKernel B).trans (h_eq_condKernel B').symm

/-- Measurable integrable functions remain integrable in own-type/opponents coordinates. -/
lemma ConditionalBeliefs.integrable_insert [DecidableEq I]
    {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    {μ : Measure (∀ i, Θ i)} [IsProbabilityMeasure μ] (B : ConditionalBeliefs μ) (i : I)
    {F : (∀ j, Θ j) → V} (hF : Measurable F) (hint : Integrable F μ) :
    Integrable (fun p : Θ i × OpponentProfile Θ i => F (insert i p.1 p.2))
      ((marginalType μ i).compProd (B.opponents i)) := by
  rw [B.disintegrates]
  apply (integrable_map_measure (hF.comp (measurable_insert i)).aestronglyMeasurable
    ((measurable_pi_apply i).prodMk (measurable_drop i)).aemeasurable).mpr
  simpa [Function.comp_def] using hint

/-- Iterated integration of a measurable integrable function against conditional opponent beliefs
and the own-type marginal recovers its prior integral. -/
theorem ConditionalBeliefs.integral_insert [DecidableEq I]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {μ : Measure (∀ i, Θ i)} [IsProbabilityMeasure μ] (B : ConditionalBeliefs μ) (i : I)
    {F : (∀ j, Θ j) → V} (hF : Measurable F) (hint : Integrable F μ) :
    (∫ θᵢ, ∫ θo, F (insert i θᵢ θo) ∂(B.opponents i θᵢ) ∂(marginalType μ i)) =
      ∫ θ, F θ ∂μ := by
  rw [← Measure.integral_compProd (B.integrable_insert i hF hint), B.disintegrates]
  simpa only [Function.comp_apply, insert_drop] using
    (integral_map (μ := μ) ((measurable_pi_apply i).prodMk (measurable_drop i)).aemeasurable
      (hF.comp (measurable_insert i)).aestronglyMeasurable)

/-- Iterated lower integration of a measurable function against conditional opponent beliefs and
the own-type marginal recovers its prior lower integral. -/
theorem ConditionalBeliefs.lintegral_insert [DecidableEq I]
    {μ : Measure (∀ i, Θ i)} [IsProbabilityMeasure μ] (B : ConditionalBeliefs μ) (i : I)
    {F : (∀ j, Θ j) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ θᵢ, ∫⁻ θo, F (insert i θᵢ θo) ∂(B.opponents i θᵢ)
      ∂(marginalType μ i)) =
      ∫⁻ θ, F θ ∂μ := by
  have hFi : Measurable (fun p : Θ i × OpponentProfile Θ i => F (insert i p.1 p.2)) :=
    hF.comp (measurable_insert i)
  rw [← Measure.lintegral_compProd hFi, B.disintegrates]
  rw [lintegral_map hFi ((measurable_pi_apply i).prodMk (measurable_drop i))]
  simp

end Auctionlib.GameTheory.BayesianPrior
