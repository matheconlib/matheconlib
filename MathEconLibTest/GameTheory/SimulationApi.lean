/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib

/-!
# Equilibrium simulation API pins

Each `example` restates the full type of a public declaration of the simulation layer and proves
it by the declaration itself, as in `ApiStability.lean`. The only project import is the public
root `MathEconLib`, so these checks also cover the export boundary.

The pins cover the comparison core, the `GameSimulation` record and its constructor fields,
identity, composition, exact-lift construction, conversion from `GameMorphism`, transport,
additive errors, both reflection entry points, and the dominated-strategy reductions.
-/

-- This module only contains `example`s, which are never public.
set_option linter.privateModule false

noncomputable section

open MathEconLib.GameTheory MathEconLib.Probability

namespace MathEconLibTest.GameTheory.SimulationApi

universe uS uI uT uJ uU uK uV uW uX uA uB

/-! ## Comparison core -/

-- Ordered comparison transport requires no order laws and permits different value spaces.
example : ∀ {V : Type uV} {S : Type uS} {I : Type uI} {P : EquilibriumProblem S I V}
    {W : Type uW} {T : Type uT} {J : Type uJ} [LE V] [LE W]
    {Q : EquilibriumProblem T J W} {s : S} {t : T},
    P.IsEquilibrium s → ∀ (g : J → I), Q.valid t →
      (∀ j t', Q.deviation j t t' → ∃ s', P.deviation (g j) s s' ∧
        (P.value (g j) s' ≤ P.value (g j) s → Q.value j t' ≤ Q.value j t)) →
      Q.IsEquilibrium t :=
  @EquilibriumProblem.IsEquilibrium.of_deviation_comparisons

-- Explicit comparison transport needs no order instance at all.
example : ∀ {V : Type uV} {S : Type uS} {I : Type uI} {P : EquilibriumProblem S I V}
    {W : Type uW} {T : Type uT} {J : Type uJ} {Q : EquilibriumProblem T J W}
    {R : I → V → V → Prop} {R' : J → W → W → Prop} {s : S} {t : T},
    P.IsEquilibriumWith R s → ∀ (g : J → I), Q.valid t →
      (∀ j t', Q.deviation j t t' → ∃ s', P.deviation (g j) s s' ∧
        (R (g j) (P.value (g j) s') (P.value (g j) s) → R' j (Q.value j t') (Q.value j t))) →
      Q.IsEquilibriumWith R' t :=
  @EquilibriumProblem.IsEquilibriumWith.of_deviation_comparisons

-- Pointwise domination needs no bundled map.
example : ∀ {V : Type uV} {W : Type uW} [Preorder V] [Preorder W] {S : Type uS} {I : Type uI}
    {T : Type uT} {J : Type uJ} {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    {s : S} {t : T},
    P.IsDeviationOptimal s → ∀ (g : J → I) (φ : J → V →o W),
      (∀ j, φ j (P.value (g j) s) ≤ Q.value j t) →
      (∀ j t', Q.deviation j t t' →
        ∃ s', P.deviation (g j) s s' ∧ Q.value j t' ≤ φ j (P.value (g j) s')) →
      Q.IsDeviationOptimal t :=
  @EquilibriumProblem.IsDeviationOptimal.of_dominated_deviations

/-! ## The simulation record -/

-- The constructor fixes the field names, their order, and each field's contract.
example : ∀ {V : Type uV} {W : Type uW} [Preorder V] [Preorder W] {S : Type uS} {I : Type uI}
    {T : Type uT} {J : Type uJ} {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    (toFun : S → T) (deviatorMap : J → I) (valueMap : J → V →o W),
    (∀ j s, valueMap j (P.value (deviatorMap j) s) ≤ Q.value j (toFun s)) →
    (∀ j s t, Q.deviation j (toFun s) t →
      ∃ s', P.deviation (deviatorMap j) s s' ∧
        Q.value j t ≤ valueMap j (P.value (deviatorMap j) s')) →
    (∀ s, P.valid s → Q.valid (toFun s)) →
    GameSimulation P Q :=
  @GameSimulation.mk

example : ∀ {V : Type uV} [Preorder V] {S : Type uS} {I : Type uI}
    (P : EquilibriumProblem S I V), GameSimulation P P :=
  @GameSimulation.id

example : ∀ {V : Type uV} {W : Type uW} {X : Type uX} [Preorder V] [Preorder W] [Preorder X]
    {S : Type uS} {I : Type uI} {T : Type uT} {J : Type uJ} {U : Type uU} {K : Type uK}
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    {R : EquilibriumProblem U K X},
    GameSimulation Q R → GameSimulation P Q → GameSimulation P R :=
  @GameSimulation.comp

example : ∀ {V : Type uV} {W : Type uW} [Preorder V] [Preorder W] {S : Type uS} {I : Type uI}
    {T : Type uT} {J : Type uJ} {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    (f : S → T) (g : J → I) (φ : J → V →o W),
    (∀ j s, Q.value j (f s) = φ j (P.value (g j) s)) →
    (∀ j s t, Q.deviation j (f s) t → ∃ s', P.deviation (g j) s s' ∧ f s' = t) →
    (∀ s, P.valid s → Q.valid (f s)) →
    GameSimulation P Q :=
  @GameSimulation.ofExactLifts

example : ∀ {V : Type uV} [Preorder V] {S : Type uS} {I : Type uI} {T : Type uT} {J : Type uJ}
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V},
    GameMorphism P Q → GameSimulation P Q :=
  @GameMorphism.toSimulation

/-! ## Transport and reflection -/

example : ∀ {V : Type uV} {W : Type uW} [Preorder V] [Preorder W] {S : Type uS} {I : Type uI}
    {T : Type uT} {J : Type uJ} {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    (f : GameSimulation P Q) {s : S},
    P.IsDeviationOptimal s → Q.IsDeviationOptimal (f.toFun s) :=
  @GameSimulation.transport_isDeviationOptimal

example : ∀ {V : Type uV} {W : Type uW} [Preorder V] [Preorder W] {S : Type uS} {I : Type uI}
    {T : Type uT} {J : Type uJ} {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    (f : GameSimulation P Q) {s : S},
    P.IsEquilibrium s → Q.IsEquilibrium (f.toFun s) :=
  @GameSimulation.transport

-- The error compatibility bound is evaluated only at the recoded source incumbent.
example : ∀ {V : Type uV} {W : Type uW} [Preorder V] [Preorder W] {S : Type uS} {I : Type uI}
    {T : Type uT} {J : Type uJ} {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    [Add V] [Add W] [AddRightMono W] (f : GameSimulation P Q) (ε : I → V) (δ : J → W) {s : S},
    (∀ j, f.valueMap j (P.value (f.deviatorMap j) s + ε (f.deviatorMap j)) ≤
      f.valueMap j (P.value (f.deviatorMap j) s) + δ j) →
    (∀ i s', P.deviation i s s' → P.value i s' ≤ P.value i s + ε i) →
    ∀ j t, Q.deviation j (f.toFun s) t → Q.value j t ≤ Q.value j (f.toFun s) + δ j :=
  @GameSimulation.transport_le_add

-- Reflection by comparisons at one incumbent, across different value spaces.
example : ∀ {V : Type uV} {W : Type uW} [Preorder V] [Preorder W] {S : Type uS} {I : Type uI}
    {T : Type uT} {J : Type uJ} {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    (f : GameSimulation P Q) {s : S} (g : I → J),
    (Q.valid (f.toFun s) → P.valid s) →
    (∀ i s', P.deviation i s s' → ∃ t, Q.deviation (g i) (f.toFun s) t ∧
      (Q.value (g i) t ≤ Q.value (g i) (f.toFun s) → P.value i s' ≤ P.value i s)) →
    (Q.IsEquilibrium (f.toFun s) ↔ P.IsEquilibrium s) :=
  @GameSimulation.isEquilibrium_iff_of_deviation_comparisons

-- Reflection by a separate comorphism on the same state map.
example : ∀ {V : Type uV} [Preorder V] {S : Type uS} {I : Type uI} {T : Type uT} {J : Type uJ}
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}
    (f : GameSimulation P Q) (g : GameComorphism P Q), g.toFun = f.toFun →
    ∀ s, (Q.IsEquilibrium (f.toFun s) ↔ P.IsEquilibrium s) :=
  @GameSimulation.isEquilibrium_iff

/-! ## Dominated-strategy reductions -/

-- Ordinary reductions need only a preorder and need not be injective.
example : ∀ {I : Type uI} {A : I → Type uA} {B : I → Type uB} {V : Type uV} [DecidableEq I]
    [Preorder V] (G : StrategicGame I A V) (f : ∀ i, B i → A i),
    (∀ b i a, ∃ b', G.payoff i (Function.update (fun j ↦ f j (b j)) i a) ≤
      (G.comapActions f).payoff i (Function.update b i b')) →
    GameSimulation (G.comapActions f).nashProblem G.nashProblem :=
  @StrategicGame.dominatedActionSimulation

example : ∀ {I : Type uI} {A : I → Type uA} {B : I → Type uB} {V : Type uV} [DecidableEq I]
    [Preorder V] (G : StrategicGame I A V) (f : ∀ i, B i → A i) (b : ∀ i, B i),
    (∀ i a, ∃ b', G.payoff i (Function.update (fun j ↦ f j (b j)) i a) ≤
      (G.comapActions f).payoff i (Function.update b i b')) →
    ((G.comapActions f).IsNash b ↔ G.IsNash (fun i ↦ f i (b i))) :=
  @StrategicGame.isNash_comapActions_iff_of_dominated

-- Finite mixed reductions allow infinite retained strategy carriers.
example : ∀ {I : Type uI} {A : I → Type uA} {B : I → Type uB} [DecidableEq I] [Fintype I]
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (G : StrategicGame I A ℝ) (f : ∀ i, B i → FinDist (A i)),
    (∀ b i a, ∃ b', G.finiteExpectedPayoff i
      (Function.update (fun j ↦ f j (b j)) i (FinDist.pure a)) ≤
        (G.finiteMixedExtension.comapActions f).payoff i (Function.update b i b')) →
    GameSimulation (G.finiteMixedExtension.comapActions f).nashProblem
      G.finiteMixedExtension.nashProblem :=
  @StrategicGame.dominatedFiniteMixedSimulation

example : ∀ {I : Type uI} {A : I → Type uA} {B : I → Type uB} [DecidableEq I] [Fintype I]
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (G : StrategicGame I A ℝ) (f : ∀ i, B i → FinDist (A i)) (b : ∀ i, B i),
    (∀ i a, ∃ b', G.finiteExpectedPayoff i
      (Function.update (fun j ↦ f j (b j)) i (FinDist.pure a)) ≤
        (G.finiteMixedExtension.comapActions f).payoff i (Function.update b i b')) →
    ((G.finiteMixedExtension.comapActions f).IsNash b ↔
      G.IsFiniteMixedNash (fun i ↦ f i (b i))) :=
  @StrategicGame.isNash_comapFiniteMixed_iff_of_dominated

example : ∀ {I : Type uI} {A : I → Type uA} {V : Type uV} [∀ i, Fintype (A i)] [Fintype I]
    [DecidableEq I] [AddCommMonoid V] [Module ℝ V] [∀ i, DecidableEq (A i)]
    (G : StrategicGame I A V) (σ : StrategicGame.FiniteMixedStrategy A) (i : I)
    (τ : FinDist (A i)),
    G.finiteExpectedPayoff i (Function.update σ i τ) =
      τ.expect (fun a ↦ G.finiteExpectedPayoff i (Function.update σ i (FinDist.pure a))) :=
  @StrategicGame.finiteExpectedPayoff_update_eq_expect

end MathEconLibTest.GameTheory.SimulationApi

end
