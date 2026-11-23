/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Strategic.Reduction

/-!
# Eliminating a strategy dominated only by a mixture

Row's payoffs in a two-player zero-sum game are `(3, 0)`, `(0, 3)`, and `(1, 1)`.
The last row is strictly dominated by the half-half mixture of the first two, but neither retained
pure row dominates it. The reduced game's uniform equilibrium lifts through a `GameSimulation`.

The source already permits all mixed strategies on the retained rows. Against the uniform column
strategy, every source deviation pays `3 / 2`, while the deleted row pays `1`. Thus even allowing
mixed source deviations cannot supply an exact payoff match. This example demonstrates payoff
domination, rather than utility-independent equality of outcome laws.
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MathEconLib.Probability

namespace MathEconLibExamples.GameTheory.DominatedStrategies

/-- Player `false` chooses a row; player `true` chooses a column. -/
abbrev Actions : Bool → Type | false => Fin 3 | true => Fin 2

instance (i : Bool) : Fintype (Actions i) := match i with
  | false => inferInstance | true => inferInstance
instance (i : Bool) : DecidableEq (Actions i) := match i with
  | false => inferInstance | true => inferInstance

/-- The third row gives one regardless of the column. -/
def rowPayoff (r : Fin 3) (c : Fin 2) : ℝ :=
  if r = 2 then 1 else if r.val = c.val then 3 else 0

/-- The column player's payoff is the negative of the row player's payoff. -/
def game : StrategicGame Bool Actions ℝ where
  payoff i a := if i then -rowPayoff (a false) (a true) else rowPayoff (a false) (a true)

/-- Include a mixed strategy on the first two rows, assigning no mass to the deleted row. -/
def includeRows (σ : FinDist (Fin 2)) : FinDist (Fin 3) :=
  ⟨fun a ↦ if a = 0 then σ 0 else if a = 1 then σ 1 else 0,
    (by intro a; dsimp only; split_ifs <;> first | exact σ.nonneg _ | exact le_rfl), by
      simp [Fin.sum_univ_three]⟩

@[simp] lemma includeRows_apply (σ : FinDist (Fin 2)) (a : Fin 3) :
    includeRows σ a = if a = 0 then σ 0 else if a = 1 then σ 1 else 0 := rfl

/-- Include the retained row mixtures and leave the column mixtures unchanged. -/
def includeActions (i : Bool) : FinDist (Fin 2) → FinDist (Actions i) := match i with
  | false => includeRows | true => id

/-- The reduced game retains arbitrary mixtures on the first two rows and on both columns. -/
def reduced : StrategicGame Bool (fun _ ↦ FinDist (Fin 2)) ℝ :=
  game.finiteMixedExtension.comapActions includeActions

private def profileEquiv : (∀ i, Actions i) ≃ Fin 3 × Fin 2 where
  toFun a := (a false, a true)
  invFun p := fun i ↦ match i with | false => p.1 | true => p.2
  left_inv a := by funext i; cases i <;> rfl
  right_inv _ := rfl

private lemma sum_profiles (f : (∀ i, Actions i) → ℝ) :
    ∑ a, f a = ∑ r : Fin 3, ∑ c : Fin 2, f (profileEquiv.symm (r, c)) := by
  rw [← profileEquiv.symm.sum_comp f, Fintype.sum_prod_type]

lemma row_expected (σ : StrategicGame.FiniteMixedStrategy Actions) :
    game.finiteExpectedPayoff false σ =
      3 * σ false 0 * σ true 0 + 3 * σ false 1 * σ true 1 + σ false 2 := by
  rw [StrategicGame.finiteExpectedPayoff_eq_sum, sum_profiles]
  simp [Fin.sum_univ_three, Fin.sum_univ_two, profileEquiv, game, rowPayoff]
  linear_combination σ false 2 * (σ true).sum_pmf_two

lemma column_expected (σ : StrategicGame.FiniteMixedStrategy Actions) :
    game.finiteExpectedPayoff true σ = -game.finiteExpectedPayoff false σ := by
  simp [StrategicGame.finiteExpectedPayoff_eq_sum, game, Finset.sum_neg_distrib]

lemma reduced_row_payoff (σ : Bool → FinDist (Fin 2)) :
    reduced.payoff false σ = 3 * σ false 0 * σ true 0 + 3 * σ false 1 * σ true 1 := by
  change game.finiteExpectedPayoff false (fun i ↦ includeActions i (σ i)) = _
  simp [row_expected, includeActions]

lemma reduced_column_payoff (σ : Bool → FinDist (Fin 2)) :
    reduced.payoff true σ = -(3 * σ false 0 * σ true 0 + 3 * σ false 1 * σ true 1) := by
  change game.finiteExpectedPayoff true (fun i ↦ includeActions i (σ i)) = _
  simp [column_expected, row_expected, includeActions]

/-- Equal randomization strictly dominates the deleted row against either pure column. -/
theorem mixture_strictly_dominates (c : Fin 2) :
    rowPayoff 2 c < (FinDist.uniform : FinDist (Fin 2)).expect
      (fun r ↦ rowPayoff r.castSucc c) := by
  fin_cases c <;> norm_num [FinDist.expect, Fin.sum_univ_two, FinDist.uniform_apply, rowPayoff]

/-- Neither retained pure row dominates the deleted row. -/
theorem no_pure_dominator : ¬ ∃ r : Fin 2, ∀ c, rowPayoff 2 c ≤ rowPayoff r.castSucc c := by
  rintro ⟨r, h⟩
  fin_cases r
  · norm_num [rowPayoff] at h
  · have hh := h 0
    norm_num [rowPayoff] at hh

/-- Every full pure deviation is bounded by a retained strategy. The deleted row is covered by
the same half-half mixture for every retained opponents' profile. -/
theorem pure_deviations_dominated (σ : Bool → FinDist (Fin 2)) (i : Bool) (a : Actions i) :
    ∃ τ, game.finiteExpectedPayoff i (Function.update (fun j ↦ includeActions j (σ j)) i
      (FinDist.pure a)) ≤ reduced.payoff i (Function.update σ i τ) := by
  cases i with
  | false =>
    fin_cases a
    · exact ⟨FinDist.pure 0, by simp [row_expected, reduced_row_payoff, includeActions,
        FinDist.pure_apply]⟩
    · exact ⟨FinDist.pure 1, by simp [row_expected, reduced_row_payoff, includeActions,
        FinDist.pure_apply]⟩
    · refine ⟨FinDist.uniform, ?_⟩
      norm_num [row_expected, reduced_row_payoff, includeActions, FinDist.pure_apply,
        FinDist.uniform_apply]
      linarith [show σ true 0 + σ true 1 = 1 from (σ true).sum_pmf_two]
  | true =>
    exact ⟨FinDist.pure a, by simp [column_expected, row_expected, reduced_column_payoff,
      includeActions, FinDist.pure_apply]⟩

/-- A certificate that composes with other dominated-strategy reductions. -/
def simulation : GameSimulation reduced.nashProblem game.finiteMixedExtension.nashProblem :=
  game.dominatedFiniteMixedSimulation includeActions pure_deviations_dominated

/-- Both players independently mix equally between their two retained actions. -/
def uniformProfile : Bool → FinDist (Fin 2) := fun _ ↦ FinDist.uniform

lemma retained_row_deviation_payoff (τ : FinDist (Fin 2)) :
    reduced.payoff false (Function.update uniformProfile false τ) = 3 / 2 := by
  norm_num [reduced_row_payoff, uniformProfile, FinDist.uniform_apply]
  linarith [show τ 0 + τ 1 = 1 from τ.sum_pmf_two]

lemma retained_column_deviation_payoff (τ : FinDist (Fin 2)) :
    reduced.payoff true (Function.update uniformProfile true τ) = -(3 / 2) := by
  norm_num [reduced_column_payoff, uniformProfile, FinDist.uniform_apply]
  linarith [show τ 0 + τ 1 = 1 from τ.sum_pmf_two]

theorem reduced_equilibrium : reduced.IsNash uniformProfile := by
  rw [StrategicGame.isNash_iff]
  intro i τ
  cases i
  · rw [retained_row_deviation_payoff]
    norm_num [reduced_row_payoff, uniformProfile, FinDist.uniform_apply]
  · rw [retained_column_deviation_payoff]
    norm_num [reduced_column_payoff, uniformProfile, FinDist.uniform_apply]

/-- Reduced and full mixed equilibria agree at every retained profile, since every full pure
deviation is dominated there. -/
theorem reduced_isNash_iff (σ : Bool → FinDist (Fin 2)) :
    reduced.IsNash σ ↔ game.IsFiniteMixedNash (fun i ↦ includeActions i (σ i)) :=
  game.isNash_comapFiniteMixed_iff_of_dominated includeActions σ (pure_deviations_dominated σ)

/-- The named simulation theorem lifts an equilibrium after a genuinely mixed dominance step. -/
theorem full_equilibrium : game.IsFiniteMixedNash (fun i ↦ includeActions i (uniformProfile i)) :=
  simulation.transport reduced_equilibrium

lemma deleted_row_payoff : game.finiteExpectedPayoff false
    (Function.update (fun i ↦ includeActions i (uniformProfile i)) false (FinDist.pure 2)) = 1 := by
  simp [row_expected, FinDist.pure_apply]

/-- Exact reward matching fails even though the source admits every mixture of retained rows. -/
theorem no_exact_deviation_payoff : ¬ ∃ σ', reduced.nashProblem.deviation false uniformProfile σ' ∧
    reduced.payoff false σ' = game.finiteExpectedPayoff false
      (Function.update (fun i ↦ includeActions i (uniformProfile i)) false (FinDist.pure 2)) := by
  rintro ⟨_, ⟨τ, rfl⟩, h⟩
  rw [retained_row_deviation_payoff, deleted_row_payoff] at h
  norm_num at h

/-- The retained-strategy inclusion cannot be an exact transport morphism. -/
theorem no_exact_morphism : ¬ ∃ f : GameMorphism reduced.nashProblem
    game.finiteMixedExtension.nashProblem, f.toFun = simulation.toFun := by
  rintro ⟨f, hf⟩
  have hplayer : f.deviatorMap false = false := by
    by_contra h
    have htrue : f.deviatorMap false = true := Bool.eq_true_of_not_eq_false h
    have he := f.value_eq false uniformProfile
    rw [hf] at he
    change reduced.payoff false uniformProfile = reduced.payoff (f.deviatorMap false)
      uniformProfile at he
    rw [htrue] at he
    norm_num [reduced_row_payoff, reduced_column_payoff, uniformProfile,
      FinDist.uniform_apply] at he
  let t := Function.update (simulation.toFun uniformProfile) false (FinDist.pure 2)
  have ht : game.finiteMixedExtension.nashProblem.deviation false (f.toFun uniformProfile) t := by
    rw [hf]
    exact ⟨FinDist.pure 2, rfl⟩
  obtain ⟨σ', hσ', heq⟩ := f.deviation_lifts false uniformProfile t ht
  rw [hplayer] at hσ'
  have hvalue := f.value_eq false σ'
  rw [hplayer] at hvalue
  apply no_exact_deviation_payoff
  exact ⟨σ', hσ', hvalue.symm.trans (congrArg
    (game.finiteMixedExtension.nashProblem.value false) heq)⟩

end MathEconLibExamples.GameTheory.DominatedStrategies
