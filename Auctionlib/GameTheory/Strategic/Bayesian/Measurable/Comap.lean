/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Strategic.Bayesian.Measurable.PureBNE

/-!
# Action translation and Bayesian equilibrium

Players may choose actions in a new space that are measurably translated into the actions of a
Bayesian game. Every integrable unilateral deviation in the new game induces an integrable
unilateral deviation in the original game, with the same realized payoff. Equilibrium in the
original game therefore pulls back whenever its strategy profile is obtained by translating the new
profile. The action maps need not be injective or surjective.

## Main definitions

* `BayesianGame.Strategy.mapActions`: Translate the actions prescribed by measurable strategies.
* `BayesianGame.comapActionsComorphism`: The induced map of equilibrium problems.

## Main statements

* `BayesianGame.exAntePayoff_comapActions`: Action translation preserves ex-ante payoff integrals.
* `BayesianGame.incumbentPayoffsIntegrable_comapActions_iff`: Action translation preserves
  integrability of incumbent payoffs.
* `BayesianGame.IsBNE.comapActions`: Bayesian equilibrium pulls back under action translation.

## Tags

bayesian nash equilibrium, action translation, equilibrium transport
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Auctionlib.GameTheory.BayesianGame

universe uI uT uA uB uC uV

variable {I : Type uI} {Θ : I → Type uT} {A : I → Type uA}
  {B : I → Type uB} {C : I → Type uC} {V : Type uV}
  [∀ i, MeasurableSpace (Θ i)] [∀ i, MeasurableSpace (A i)]
  [∀ i, MeasurableSpace (B i)] [∀ i, MeasurableSpace (C i)]

/-- Translate each action prescribed by a measurable strategy through a measurable map. -/
def Strategy.mapActions (G : BayesianGame I Θ A V)
    (κ : ∀ i, {f : B i → A i // Measurable f})
    (s : (G.comapActions (fun i => (κ i).1)).Strategy) : G.Strategy :=
  fun i => ⟨(κ i).1 ∘ (s i).1, (κ i).2.comp (s i).2⟩

/-- A translated strategy prescribes the translated action at each type. -/
@[simp] lemma Strategy.mapActions_apply (G : BayesianGame I Θ A V)
    (κ : ∀ i, {f : B i → A i // Measurable f})
    (s : (G.comapActions (fun i => (κ i).1)).Strategy) (i : I) (t : Θ i) :
    (Strategy.mapActions G κ s i).1 t = (κ i).1 ((s i).1 t) := rfl

/-- Identity action translation preserves a measurable strategy profile. -/
@[simp] lemma Strategy.mapActions_id (G : BayesianGame I Θ A V) (s : G.Strategy) :
    Strategy.mapActions G (fun _ => ⟨id, measurable_id⟩) s = s := rfl

/-- Successive measurable action translations agree with their composition. -/
lemma Strategy.mapActions_comp (G : BayesianGame I Θ A V)
    (κ : ∀ i, {f : B i → A i // Measurable f})
    (τ : ∀ i, {f : C i → B i // Measurable f})
    (s : ((G.comapActions (fun i => (κ i).1)).comapActions (fun i => (τ i).1)).Strategy) :
    Strategy.mapActions G κ (Strategy.mapActions (G.comapActions (fun i => (κ i).1)) τ s) =
      Strategy.mapActions G (fun i => ⟨(κ i).1 ∘ (τ i).1, (κ i).2.comp (τ i).2⟩) s := rfl

/-- Translating strategies preserves the realized payoff at every type profile. -/
@[simp] lemma payoff_comapActions_strategy (G : BayesianGame I Θ A V)
    (κ : ∀ i, {f : B i → A i // Measurable f})
    (s : (G.comapActions (fun i => (κ i).1)).Strategy) (i : I) (θ : ∀ i, Θ i) :
    (G.comapActions (fun i => (κ i).1)).payoff i
        ((G.comapActions (fun i => (κ i).1)).measurableActionProfile s θ) θ =
      G.payoff i (G.measurableActionProfile (Strategy.mapActions G κ s) θ) θ := rfl

/-- Incumbent integrability is unchanged by translating the prescribed actions. -/
@[simp] lemma incumbentPayoffsIntegrable_comapActions_iff [NormedAddCommGroup V]
    (G : BayesianGame I Θ A V)
    (μ : Measure (∀ i, Θ i)) (κ : ∀ i, {f : B i → A i // Measurable f})
    (s : (G.comapActions (fun i => (κ i).1)).Strategy) :
    (G.comapActions (fun i => (κ i).1)).IncumbentPayoffsIntegrable μ s ↔
      G.IncumbentPayoffsIntegrable μ (Strategy.mapActions G κ s) := Iff.rfl

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Action translation preserves ex-ante payoff integrals under the same type-profile measure. -/
@[simp] lemma exAntePayoff_comapActions (G : BayesianGame I Θ A V) (μ : Measure (∀ i, Θ i))
    (κ : ∀ i, {f : B i → A i // Measurable f})
    (s : (G.comapActions (fun i => (κ i).1)).Strategy) (i : I) :
    (G.comapActions (fun i => (κ i).1)).exAntePayoff μ i s =
      G.exAntePayoff μ i (Strategy.mapActions G κ s) := rfl

/-- Measurable action translation maps unilateral integrable deviations to unilateral integrable
deviations and preserves the deviator's payoff. -/
def comapActionsComorphism (G : BayesianGame I Θ A V) (μ : Measure (∀ i, Θ i))
    (κ : ∀ i, {f : B i → A i // Measurable f}) :
    GameComorphism ((G.comapActions (fun i => (κ i).1)).bneProblem μ) (G.bneProblem μ) where
  toFun := Strategy.mapActions G κ
  deviatorMap := id
  deviation_maps i s s' hs := by
    refine ⟨fun j hj => ?_, hs.2⟩
    change (⟨(κ j).1 ∘ (s' j).1, _⟩ : {f : Θ j → A j // Measurable f}) = _
    simp only [hs.1 j hj]
    rfl
  value_eq _ _ := rfl

/-- A strategy profile is an equilibrium in the game with translated actions if its image is an
equilibrium in the original game. The action maps need not be injective or surjective. -/
theorem IsBNE.comapActions [LE V] {G : BayesianGame I Θ A V} {μ : Measure (∀ i, Θ i)}
    [IsProbabilityMeasure μ] (κ : ∀ i, {f : B i → A i // Measurable f})
    {s : (G.comapActions (fun i => (κ i).1)).Strategy}
    (h : G.IsBNE μ (Strategy.mapActions G κ s)) :
    (G.comapActions (fun i => (κ i).1)).IsBNE μ s :=
  ⟨(G.comapActionsComorphism μ κ).pullback h.isEquilibrium, h.integrable⟩

end Auctionlib.GameTheory.BayesianGame

end
