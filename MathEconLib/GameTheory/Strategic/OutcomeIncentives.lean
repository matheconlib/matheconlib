/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.GameTheory.Strategic.Outcome

/-!
# Deterministic incentives under outcome comparisons

An outcome game supplies unilateral deviations, while comparisons evaluated at the full true
type profile supply preferences. Dominant intended play uses `IsOptimalWith`; ex-post play uses
`IsEquilibriumWith`. Every action profile is a valid candidate. Neither predicate requires
numerical utilities, completeness, private values, or a prior. These are weak comparisons;
absence of strict improvement alone is insufficient for incomplete preferences.

## Main definitions

* `OutcomeGame.nashProblem`: unilateral deviations with outcomes as values.
* `OutcomeGame.IsDominantStrategyWith`: intended play is optimal at every opponent profile.
* `OutcomeGame.IsExPostNashWith`: intended play is Nash at every true type profile.

## Main statements

* `OutcomeGame.isDominantStrategyWith_iff`: dominance at every opponent action profile.
* `OutcomeGame.isExPostNashWith_iff`: unilateral comparisons at intended play.
* `OutcomeGame.IsDominantStrategyWith.isExPostNashWith`: dominance implies ex-post Nash.
* The representation bridges recover the existing dominance and Nash predicates using only `LE`.

## Tags

outcome games, dominance, ex-post equilibrium, comparisons
-/

@[expose] public section

namespace MathEconLib.GameTheory.OutcomeGame

variable {I : Type*} {T : I → Type*} {A : I → Type*} {X V : Type*} [DecidableEq I]

/-- Every action profile is a valid candidate, and each player may replace its own action.
The value is the resulting outcome, shared by the players' supplied comparisons. -/
def nashProblem (g : OutcomeGame I A X) :
    EquilibriumProblem ((i : I) → A i) I X :=
  .ofDeviation (fun i a a' ↦ ∃ s, a' = Function.update a i s) (fun _ a ↦ g.outcome a)

/-- One player's outcome optimality is exactly its unilateral outcome comparisons. -/
theorem nashProblem_isOptimalWith_iff (g : OutcomeGame I A X)
    (R : I → X → X → Prop) (i : I) (a : (i : I) → A i) :
    g.nashProblem.IsOptimalWith R i a ↔
      ∀ ai, R i (g.outcome (Function.update a i ai)) (g.outcome a) :=
  ⟨fun h ai ↦ h (Function.update a i ai) ⟨ai, rfl⟩,
    fun h _ ⟨ai, heq⟩ ↦ heq.symm ▸ h ai⟩

/-- Outcome Nash equilibrium compares every unilateral deviation with the incumbent outcome. -/
theorem nashProblem_isEquilibriumWith_iff (g : OutcomeGame I A X)
    (R : I → X → X → Prop) (a : (i : I) → A i) :
    g.nashProblem.IsEquilibriumWith R a ↔
      ∀ i ai, R i (g.outcome (Function.update a i ai)) (g.outcome a) :=
  ⟨fun h i ai ↦ h.deviation_le i (Function.update a i ai) ⟨ai, rfl⟩,
    fun h ↦ ⟨trivial, fun i _ ⟨ai, heq⟩ ↦ heq.symm ▸ h i ai⟩⟩

/-- Each type's intended action is optimal at every opponent action profile. True preferences
stay fixed when actions change; no representation by an ordered utility is required. -/
def IsDominantStrategyWith (g : OutcomeGame I A X)
    (R : I → ((i : I) → T i) → X → X → Prop) (σ : (i : I) → T i → A i) : Prop :=
  ∀ θ i a, g.nashProblem.IsOptimalWith (fun j ↦ R j θ) i
    (Function.update a i (σ i (θ i)))

/-- The intended action profile is an outcome Nash equilibrium at every true type profile.
This is a prior-free condition, distinct from dominance at arbitrary opponent actions. -/
def IsExPostNashWith (g : OutcomeGame I A X)
    (R : I → ((i : I) → T i) → X → X → Prop) (σ : (i : I) → T i → A i) : Prop :=
  ∀ θ, g.nashProblem.IsEquilibriumWith (fun i ↦ R i θ) (fun i ↦ σ i (θ i))

/-- Dominant intended play compares every action profile with replacement by the intended action.
The full true type profile is the same on both sides of each comparison. -/
theorem isDominantStrategyWith_iff (g : OutcomeGame I A X)
    (R : I → ((i : I) → T i) → X → X → Prop) (σ : (i : I) → T i → A i) :
    g.IsDominantStrategyWith R σ ↔ ∀ θ i a,
      R i θ (g.outcome a) (g.outcome (Function.update a i (σ i (θ i)))) := by
  constructor
  · intro h θ i a
    simpa only [Function.update_idem, Function.update_eq_self] using
      (g.nashProblem_isOptimalWith_iff _ i _).1 (h θ i a) (a i)
  · intro h θ i a
    apply (g.nashProblem_isOptimalWith_iff (fun j ↦ R j θ) i
      (Function.update a i (σ i (θ i)))).2
    intro ai
    simpa only [Function.update_idem] using h θ i (Function.update a i ai)

/-- Ex-post play compares intended behavior only with unilateral deviations at that behavior. -/
theorem isExPostNashWith_iff (g : OutcomeGame I A X)
    (R : I → ((i : I) → T i) → X → X → Prop) (σ : (i : I) → T i → A i) :
    g.IsExPostNashWith R σ ↔ ∀ θ i ai,
      R i θ (g.outcome (Function.update (fun j ↦ σ j (θ j)) i ai))
        (g.outcome (fun j ↦ σ j (θ j))) :=
  forall_congr' fun θ ↦ g.nashProblem_isEquilibriumWith_iff (fun i ↦ R i θ) _

/-- Dominant intended play is ex-post Nash, without order or private-values hypotheses. -/
theorem IsDominantStrategyWith.isExPostNashWith {g : OutcomeGame I A X}
    {R : I → ((i : I) → T i) → X → X → Prop} {σ : (i : I) → T i → A i}
    (h : g.IsDominantStrategyWith R σ) : g.IsExPostNashWith R σ := by
  apply (g.isExPostNashWith_iff R σ).2
  intro θ i ai
  simpa only [Function.update_idem, Function.update_eq_self] using
    (g.isDominantStrategyWith_iff R σ).1 h θ i
      (Function.update (fun j ↦ σ j (θ j)) i ai)

/-- An exact utility representation recovers the existing weak-dominance predicate.
Only an `LE` instance on utility values is needed. -/
theorem isDominantStrategyWith_iff_isDominant_of_representation [LE V]
    (g : OutcomeGame I A X) (R : I → ((i : I) → T i) → X → X → Prop)
    (u : I → ((i : I) → T i) → X → V)
    (hrep : ∀ i θ x y, R i θ x y ↔ u i θ x ≤ u i θ y)
    (σ : (i : I) → T i → A i) :
    g.IsDominantStrategyWith R σ ↔ ∀ θ i,
      StrategicGame.Strategy.IsDominant
        (G := StrategicGame.ofOutcome g { payoff := fun j ↦ u j θ }) (σ i (θ i)) := by
  rw [isDominantStrategyWith_iff]
  constructor
  · intro h θ i ai
    apply StrategicGame.Strategy.le_iff'.2
    intro a
    have hcmp := (hrep i θ _ _).1 (h θ i (Function.update a i ai))
    erw [Function.update_idem] at hcmp
    exact hcmp
  · intro h θ i a
    apply (hrep i θ _ _).2
    simpa only [StrategicGame.ofOutcome_payoff, Function.update_eq_self] using
      StrategicGame.Strategy.le_iff'.1 (h θ i (a i)) a

/-- An exact utility representation recovers Nash equilibrium at each fixed true profile. -/
theorem isExPostNashWith_iff_isNash_of_representation [LE V]
    (g : OutcomeGame I A X) (R : I → ((i : I) → T i) → X → X → Prop)
    (u : I → ((i : I) → T i) → X → V)
    (hrep : ∀ i θ x y, R i θ x y ↔ u i θ x ≤ u i θ y)
    (σ : (i : I) → T i → A i) :
    g.IsExPostNashWith R σ ↔ ∀ θ,
      (StrategicGame.ofOutcome g { payoff := fun i ↦ u i θ }).IsNash
        (fun i ↦ σ i (θ i)) := by
  simp only [isExPostNashWith_iff, StrategicGame.isNash_iff,
    StrategicGame.ofOutcome_payoff, hrep]

end MathEconLib.GameTheory.OutcomeGame

end
