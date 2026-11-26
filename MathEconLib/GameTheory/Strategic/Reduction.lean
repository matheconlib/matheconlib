/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Simulation
public import MathEconLib.GameTheory.Strategic.Mixed.Finite

/-!
# Nash equilibrium under dominated-strategy reductions

An action translation includes a reduced game in a larger game. If every omitted deviation is
weakly dominated by a retained deviation against the translated opponents, the inclusion is a
`GameSimulation`. Equilibria of the reduced game therefore remain equilibria in the larger game.
Together with `StrategicGame.IsNash.comapActions`, this gives an equivalence at included profiles.

The simulation needs domination at every reduced profile. To lift a single equilibrium, use the
pointwise iff theorems, which need domination only at that profile.

Actions may themselves be mixed strategies. In a finite mixed extension with real-valued payoffs,
it suffices to dominate each pure deviation by a retained strategy, which may be a mixture: a
mixed deviation is worth at most its best pure deviation. This step needs a linear order on
payoffs and fails for vector payoffs, where a mixture of two incomparable payoffs need not be
dominated by either. No exact payoff or outcome match is required for omitted deviations.
Simulations compose, so successive reductions lift equilibria through the same transport API.

## Main statements

* `StrategicGame.dominatedActionSimulation`: Local domination supplies a simulation of an action
  reduction, without requiring the action maps to be injective.
* `StrategicGame.isNash_comapActions_iff_of_dominated`: Reduced and full Nash agree at translated
  profiles when all full deviations are covered by domination.
* `StrategicGame.exists_retained_deviation_ge`: With real payoffs, domination of pure deviations
  at one profile bounds every mixed deviation there by a retained strategy.
* `StrategicGame.dominatedFiniteMixedSimulation`: Domination of pure deviations suffices for
  arbitrary mixed deviations, including mixed strategies on the retained actions.
* `StrategicGame.isNash_comapFiniteMixed_iff_of_dominated`: Reduced and full mixed Nash agree at a
  retained profile when every pure deviation there is dominated.

## Tags

nash equilibrium, dominated strategies, mixed strategies, game reduction
-/

@[expose] public noncomputable section

open MathEconLib.Probability

namespace MathEconLib.GameTheory.StrategicGame

variable {I : Type*} {A B : I → Type*} {V : Type*} [DecidableEq I]

/-- A reduction preserves Nash when every full deviation is weakly dominated by a retained one.
The dominating action may depend on the opponents' incumbent strategies. Domination is required at
every reduced profile; for a single profile, use `isNash_comapActions_iff_of_dominated`. -/
def dominatedActionSimulation [Preorder V] (G : StrategicGame I A V) (f : ∀ i, B i → A i)
    (hdom : ∀ b i a, ∃ b', G.payoff i (Function.update (fun j ↦ f j (b j)) i a) ≤
      (G.comapActions f).payoff i (Function.update b i b')) :
    GameSimulation (G.comapActions f).nashProblem G.nashProblem where
  toFun b j := f j (b j)
  deviatorMap := id
  valueMap _ := OrderHom.id
  incumbent_value_le _ _ := le_rfl
  deviation_dominated i b _ ht := by
    obtain ⟨a, rfl⟩ := ht
    obtain ⟨b', hb'⟩ := hdom b i a
    exact ⟨Function.update b i b', ⟨b', rfl⟩, hb'⟩
  valid_preserves _ _ := trivial

/-- Domination at one reduced profile gives the converse of `IsNash.comapActions` there. Only
that profile's image is covered; equilibria of the larger game outside the image of `f` are not. -/
theorem isNash_comapActions_iff_of_dominated [Preorder V] (G : StrategicGame I A V)
    (f : ∀ i, B i → A i) (b : ∀ i, B i)
    (hdom : ∀ i a, ∃ b', G.payoff i (Function.update (fun j ↦ f j (b j)) i a) ≤
      (G.comapActions f).payoff i (Function.update b i b')) :
    (G.comapActions f).IsNash b ↔ G.IsNash (fun i ↦ f i (b i)) := by
  refine ⟨fun h ↦ ⟨trivial, h.deviation_le.of_dominated_deviations id
    (fun _ ↦ OrderHom.id) (fun _ ↦ le_rfl) ?_⟩, fun h ↦ h.comapActions f⟩
  rintro i _ ⟨a, rfl⟩
  obtain ⟨b', hb'⟩ := hdom i a
  exact ⟨Function.update b i b', ⟨b', rfl⟩, hb'⟩

section Finite

variable [Fintype I] [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- Pure-deviation domination at one incumbent supplies a retained strategy bounding any mixed
deviation's payoff. The retained action space need not be finite. -/
lemma exists_retained_deviation_ge (G : StrategicGame I A ℝ)
    (f : ∀ i, B i → FinDist (A i)) (b : ∀ i, B i)
    (hdom : ∀ i a, ∃ b', G.finiteExpectedPayoff i
      (Function.update (fun j ↦ f j (b j)) i (FinDist.pure a)) ≤
        (G.finiteMixedExtension.comapActions f).payoff i (Function.update b i b'))
    (i : I) (τ : FinDist (A i)) : ∃ b', G.finiteExpectedPayoff i
      (Function.update (fun j ↦ f j (b j)) i τ) ≤
        (G.finiteMixedExtension.comapActions f).payoff i (Function.update b i b') := by
  let value := fun a ↦ G.finiteExpectedPayoff i
    (Function.update (fun j ↦ f j (b j)) i (FinDist.pure a))
  obtain ⟨a₀, _⟩ := τ.exists_pmf_pos
  obtain ⟨a, _, hmax⟩ := Finset.exists_max_image Finset.univ value ⟨a₀, Finset.mem_univ _⟩
  obtain ⟨b', hb'⟩ := hdom i a
  refine ⟨b', ?_⟩
  rw [finiteExpectedPayoff_update_eq_expect]
  exact ((τ.expect_mono value (fun _ ↦ value a)
    (fun c ↦ hmax c (Finset.mem_univ _))).trans_eq (τ.expect_const _)).trans hb'

/-- In a finite mixed extension with real payoffs, it suffices to dominate pure deviations by
retained strategies at every reduced profile. The retained strategies may already be mixed; their
carriers need not be finite. -/
def dominatedFiniteMixedSimulation (G : StrategicGame I A ℝ)
    (f : ∀ i, B i → FinDist (A i))
    (hdom : ∀ b i a, ∃ b', G.finiteExpectedPayoff i
      (Function.update (fun j ↦ f j (b j)) i (FinDist.pure a)) ≤
        (G.finiteMixedExtension.comapActions f).payoff i (Function.update b i b')) :
    GameSimulation (G.finiteMixedExtension.comapActions f).nashProblem
      G.finiteMixedExtension.nashProblem :=
  G.finiteMixedExtension.dominatedActionSimulation f fun b ↦
    G.exists_retained_deviation_ge f b (hdom b)

/-- A finite mixed game's equilibria at retained profiles are exactly those of the reduction
when every pure deviation is dominated by a retained, possibly mixed, strategy. -/
theorem isNash_comapFiniteMixed_iff_of_dominated (G : StrategicGame I A ℝ)
    (f : ∀ i, B i → FinDist (A i)) (b : ∀ i, B i)
    (hdom : ∀ i a, ∃ b', G.finiteExpectedPayoff i
      (Function.update (fun j ↦ f j (b j)) i (FinDist.pure a)) ≤
        (G.finiteMixedExtension.comapActions f).payoff i (Function.update b i b')) :
    (G.finiteMixedExtension.comapActions f).IsNash b ↔
      G.IsFiniteMixedNash (fun i ↦ f i (b i)) :=
  G.finiteMixedExtension.isNash_comapActions_iff_of_dominated f b
    (G.exists_retained_deviation_ge f b hdom)

end Finite

end MathEconLib.GameTheory.StrategicGame
