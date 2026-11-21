/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib
public import MathEconLibExamples.GameTheory.ExplicitComparisons
public import MathEconLibExamples.Mechanism.PostedPriceUtility
public import MathEconLibTest.Mechanism.TruthfulNash

/-!
# Deterministic IC core compatibility checks

The public umbrella exposes comparison incentives with dependent type and action carriers and
no order assumptions. Representation requires only `LE`, and quasilinear recovery permits
interdependent values. The existing nonlinear pricing, truthful-Nash and incomplete-comparison
clients exercise the new interfaces without duplicating their economic developments.
-/

@[expose] public section

open MathEconLib MathEconLib.GameTheory MathEconLib.Mechanism

namespace MathEconLibTest.Mechanism.DeterministicIC

universe uI uT uA uO uV

section Signatures

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {O : Type uO}
  {V : Type uV} [DecidableEq I]

example (g : OutcomeGame I A O) (a : Profile A) : g.nashProblem.valid a := trivial

example (g : OutcomeGame I A O) (R : I → Profile T → O → O → Prop)
    (σ : (i : I) → T i → A i) :
    g.IsDominantStrategyWith R σ ↔ ∀ θ i a,
      R i θ (g.outcome a) (g.outcome (Function.update a i (σ i (θ i)))) :=
  g.isDominantStrategyWith_iff R σ

example (g : OutcomeGame I A O) (R : I → Profile T → O → O → Prop)
    (σ : (i : I) → T i → A i) :
    g.IsExPostNashWith R σ ↔ ∀ θ i ai,
      R i θ (g.outcome (Function.update (fun j ↦ σ j (θ j)) i ai))
        (g.outcome (fun j ↦ σ j (θ j))) :=
  g.isExPostNashWith_iff R σ

example (M : MathEconLib.Mechanism I A O)
    (R : I → Profile T → (O × (I → ℝ)) → (O × (I → ℝ)) → Prop)
    (σ : (i : I) → T i → A i) (h : M.IsDSICWith R σ) : M.IsExPostICWith R σ :=
  h.isExPostICWith

-- Neither representation bridge assumes reflexivity, transitivity, or completeness of `LE V`.
example [LE V] (M : MathEconLib.Mechanism I A O)
    (R : I → Profile T → (O × (I → ℝ)) → (O × (I → ℝ)) → Prop)
    (u : I → Profile T → (O × (I → ℝ)) → V)
    (hrep : ∀ i θ c d, R i θ c d ↔ u i θ c ≤ u i θ d)
    (σ : (i : I) → T i → A i) :
    M.IsDSICWith R σ ↔ ∀ θ i,
      StrategicGame.Strategy.IsDominant (G := M.toStrategicGame u θ) (σ i (θ i)) :=
  M.isDSICWith_iff_isDominant_of_representation R u hrep σ

example [LE V] (M : MathEconLib.Mechanism I A O)
    (R : I → Profile T → (O × (I → ℝ)) → (O × (I → ℝ)) → Prop)
    (u : I → Profile T → (O × (I → ℝ)) → V)
    (hrep : ∀ i θ c d, R i θ c d ↔ u i θ c ≤ u i θ d)
    (σ : (i : I) → T i → A i) :
    M.IsExPostICWith R σ ↔ ∀ θ,
      (M.toStrategicGame u θ).IsNash (fun i ↦ σ i (θ i)) :=
  M.isExPostICWith_iff_isNash_of_representation R u hrep σ

example (M : DirectMechanism I T O) (E : QuasilinearEnvironment I T O) :
    M.IsDSICWith (fun i θ c d ↦ E.consequenceUtility i θ c ≤ E.consequenceUtility i θ d)
      (fun _ ↦ id) ↔ DirectMechanism.IsDSIC E M :=
  M.isDSICWith_iff_quasilinear E

end Signatures

section Pricing

open MathEconLibExamples.Mechanism.PostedPriceUtility

/-- The existing positive-wealth pricing client satisfies the general comparison IC interface. -/
theorem pricing_isDSICWith :
    mechanism.IsDSICWith (fun i θ c d ↦ utility i θ c ≤ utility i θ d) (fun _ ↦ id) := by
  apply (mechanism.isDSICWith_iff _ _).2
  rintro θ ⟨⟩ a
  change (mechanism.toStrategicGame utility θ).payoff () a ≤
    (mechanism.toStrategicGame utility θ).payoff () (Function.update a () (θ ()))
  have hupdate : Function.update a () (θ ()) = θ := by
    funext j
    cases j
    simp
  simpa only [hupdate] using truthful_payoff_ge θ a

example :
    mechanism.IsExPostICWith (fun i θ c d ↦ utility i θ c ≤ utility i θ d) (fun _ ↦ id) :=
  pricing_isDSICWith.isExPostICWith

example (θ a : Unit → Bool) :
    0 < 2 + environment.value () θ (mechanism.outcome a) + mechanism.transfer () a :=
  finalWealth_pos θ a

end Pricing

section InterdependentValues

open MathEconLib.Tests.MechanismTruthfulNash

/-- Existing truthful Nash recovers comparison ex-post IC without a private-values premise. -/
theorem interdependent_isExPostICWith :
    mechanism.IsExPostICWith
      (fun i θ c d ↦ environment.consequenceUtility i θ c ≤
        environment.consequenceUtility i θ d) (fun _ ↦ id) :=
  (mechanism.isExPostICWith_iff_quasilinear environment).2 truthful_isNash

/-- The same fixed-true-preference client still fails dominance at arbitrary opponents' reports. -/
theorem interdependent_not_isDSICWith :
    ¬ mechanism.IsDSICWith
      (fun i θ c d ↦ environment.consequenceUtility i θ c ≤
        environment.consequenceUtility i θ d) (fun _ ↦ id) :=
  fun h ↦ mechanism_not_isDSIC ((mechanism.isDSICWith_iff_quasilinear environment).1 h)

example :
    environment.utility mechanism false (fun _ ↦ false)
        (Function.update (fun _ ↦ true) false false) <
      environment.utility mechanism false (fun _ ↦ false) (fun _ ↦ true) :=
  lie_profitable

end InterdependentValues

section IncompleteComparisons

open MathEconLibExamples.GameTheory.ExplicitComparisons

-- Adapt the existing two-alternative client without replacing weak optimality by no strict gain.
example :
    ¬ ({ outcome := fun a : Unit → Bool ↦ problem.value () (a ()) } :
        OutcomeGame Unit (fun _ ↦ Bool) Bool).IsExPostNashWith
      (fun _ (_ : Unit → Unit) x y ↦ x = y) (fun _ _ ↦ false) := by
  intro h
  apply equality_not_isEquilibriumWith
  refine ⟨trivial, ?_⟩
  intro i t _
  exact (OutcomeGame.isExPostNashWith_iff _ _ _).1 h (fun _ ↦ ()) () t

end IncompleteComparisons

end MathEconLibTest.Mechanism.DeterministicIC

end
