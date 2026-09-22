/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Equilibrium under admissible deviations

An equilibrium problem specifies states, deviators, admissible changes, and real-valued rewards.
Equilibrium means that no admissible change increases its deviator's reward.

## Main definitions

* `EquilibriumProblem`: admissible deviations and rewards over a space of states.
* `EquilibriumProblem.IsEquilibrium`: states admitting no strictly profitable deviation.
* `GameMorphism`: reward-preserving maps that lift target deviations to source deviations.
* `GameComorphism`: reward-preserving maps that send source deviations to target deviations.

## Main statements

* `EquilibriumProblem.IsEquilibrium.of_deviation_subset` restricts admissible deviations.
* `GameMorphism.transport` and `GameComorphism.pullback` transport equilibrium.

## Tags

equilibrium, deviations, game theory
-/

@[expose] public section

namespace MathEconLib.GameTheory

universe u v w x y z

/-- States, admissible changes, and the reward evaluated by each deviator. -/
structure EquilibriumProblem (S : Type u) (I : Type v) where
  /-- Whether a deviator may change the first state to the second state. -/
  deviation : I → S → S → Prop
  /-- The reward of each deviator at each state. -/
  value : I → S → ℝ

namespace EquilibriumProblem

variable {S : Type u} {I : Type v} {P Q : EquilibriumProblem S I}

/-- No admissible deviation strictly improves its deviator's reward. -/
def IsEquilibrium (P : EquilibriumProblem S I) (s : S) : Prop :=
  ∀ i s', P.deviation i s s' → P.value i s' ≤ P.value i s

/-- Equilibrium holds exactly when every admissible deviation weakly lowers the deviator's
reward. -/
@[simp] lemma isEquilibrium_iff (P : EquilibriumProblem S I) (s : S) :
    P.IsEquilibrium s ↔ ∀ i s', P.deviation i s s' → P.value i s' ≤ P.value i s := Iff.rfl

/-- Removing admissible deviations preserves equilibrium when rewards agree. -/
lemma IsEquilibrium.of_deviation_subset {s : S} (h : P.IsEquilibrium s)
    (hd : ∀ i s t, Q.deviation i s t → P.deviation i s t)
    (hv : Q.value = P.value) : Q.IsEquilibrium s := by
  intro i t ht
  simpa [hv] using h i t (hd i s t ht)

end EquilibriumProblem

/-- A reward-preserving map under which every target deviation lifts to a source deviation. -/
structure GameMorphism {S : Type u} {I : Type v} {T : Type w} {J : Type x}
    (P : EquilibriumProblem S I) (Q : EquilibriumProblem T J) where
  /-- The map from source states to target states. -/
  toFun : S → T
  /-- The source deviator corresponding to each target deviator. -/
  deviatorMap : J → I
  /-- Every target deviation from an image state is the image of a source deviation. -/
  deviation_lifts : ∀ j s t, Q.deviation j (toFun s) t →
    ∃ s', P.deviation (deviatorMap j) s s' ∧ toFun s' = t
  /-- Corresponding deviators receive equal rewards at corresponding states. -/
  value_eq : ∀ j s, Q.value j (toFun s) = P.value (deviatorMap j) s

namespace GameMorphism

variable {S : Type u} {I : Type v} {T : Type w} {J : Type x} {U : Type y} {K : Type z}
    {P : EquilibriumProblem S I} {Q : EquilibriumProblem T J} {R : EquilibriumProblem U K}

/-- A deviation-lifting map sends equilibria to equilibria. -/
theorem transport (f : GameMorphism P Q) {s : S} (h : P.IsEquilibrium s) :
    Q.IsEquilibrium (f.toFun s) := by
  intro j t ht
  obtain ⟨s', hs', rfl⟩ := f.deviation_lifts j s t ht
  simpa only [f.value_eq] using h (f.deviatorMap j) s' hs'

/-- The identity map of an equilibrium problem. -/
def id (P : EquilibriumProblem S I) : GameMorphism P P where
  toFun := _root_.id
  deviatorMap := _root_.id
  deviation_lifts _ _ t ht := ⟨t, ht, rfl⟩
  value_eq _ _ := rfl

/-- Composition of deviation-lifting maps. -/
def comp (g : GameMorphism Q R) (f : GameMorphism P Q) : GameMorphism P R where
  toFun := g.toFun ∘ f.toFun
  deviatorMap := f.deviatorMap ∘ g.deviatorMap
  deviation_lifts k s u hu := by
    obtain ⟨t, ht, htu⟩ := g.deviation_lifts k (f.toFun s) u hu
    obtain ⟨s', hs', hst⟩ := f.deviation_lifts (g.deviatorMap k) s t ht
    exact ⟨s', hs', by simp [hst, htu]⟩
  value_eq k s := (g.value_eq k (f.toFun s)).trans (f.value_eq (g.deviatorMap k) s)

end GameMorphism

/-- A reward-preserving map that sends each source deviation to a target deviation. -/
structure GameComorphism {S : Type u} {I : Type v} {T : Type w} {J : Type x}
    (P : EquilibriumProblem S I) (Q : EquilibriumProblem T J) where
  /-- The map from source states to target states. -/
  toFun : S → T
  /-- The target deviator corresponding to each source deviator. -/
  deviatorMap : I → J
  /-- Every source deviation maps to an admissible target deviation. -/
  deviation_maps : ∀ i s s', P.deviation i s s' →
    Q.deviation (deviatorMap i) (toFun s) (toFun s')
  /-- Corresponding deviators receive equal rewards at corresponding states. -/
  value_eq : ∀ i s, Q.value (deviatorMap i) (toFun s) = P.value i s

namespace GameComorphism

variable {S : Type u} {I : Type v} {T : Type w} {J : Type x} {U : Type y} {K : Type z}
    {P : EquilibriumProblem S I} {Q : EquilibriumProblem T J} {R : EquilibriumProblem U K}

/-- Equilibrium pulls back along a deviation-preserving map. -/
theorem pullback (f : GameComorphism P Q) {s : S}
    (h : Q.IsEquilibrium (f.toFun s)) : P.IsEquilibrium s := by
  intro i s' hs'
  simpa only [f.value_eq] using h (f.deviatorMap i) (f.toFun s') (f.deviation_maps i s s' hs')

/-- The identity deviation-preserving map. -/
def id (P : EquilibriumProblem S I) : GameComorphism P P where
  toFun := _root_.id
  deviatorMap := _root_.id
  deviation_maps _ _ _ h := h
  value_eq _ _ := rfl

/-- Composition of deviation-preserving maps. -/
def comp (g : GameComorphism Q R) (f : GameComorphism P Q) : GameComorphism P R where
  toFun := g.toFun ∘ f.toFun
  deviatorMap := g.deviatorMap ∘ f.deviatorMap
  deviation_maps i s s' h := g.deviation_maps _ _ _ (f.deviation_maps i s s' h)
  value_eq i s := (g.value_eq (f.deviatorMap i) (f.toFun s)).trans (f.value_eq i s)

end GameComorphism

end MathEconLib.GameTheory
