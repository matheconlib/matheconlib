/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Strategic.Bayesian.Finite
public import Auctionlib.GameTheory.Strategic.Bayesian.Measurable.PureBNE
public import Auctionlib.Probability.FinDist.Measure

/-!
# Finite and measurable Bayesian payoffs

On finite discrete type spaces every strategy is measurable and every payoff in a complete real
normed space is integrable. Finite conditional payoff sums and measurable ex-ante payoffs therefore
describe the same incentives, including at zero-probability types.

## Main definitions

* `BayesianGame.toMeasurableStrategy`: Measurable strategies from finite type-contingent actions.
* `BayesianGame.exAntePayoffFin`: Expected payoff under a finite common prior.

## Main statements

* `BayesianGame.exAntePayoffFin_eq_exAntePayoff`: Agreement between finite expectation and integral.
* `BayesianGame.isBNEFin_iff_isBNE`: Equivalence of finite and measurable Bayesian equilibria.

## Tags

bayesian game, finite types, measurable strategy, expectation, equilibrium
-/

@[expose] public noncomputable section

open Function BigOperators MeasureTheory Auctionlib.Probability

namespace Auctionlib.GameTheory.BayesianGame

variable {I : Type*} {Θ : I → Type*} {A : I → Type*} {V : Type*}
    [Fintype I] [DecidableEq I] [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)]
    (G : BayesianGame I Θ A V) (d : FinDist (∀ i, Θ i))

section Finite

variable [AddCommMonoid V] [Module ℝ V]

/-- Ex-ante payoff as a finite probability-weighted sum over type profiles. -/
def exAntePayoffFin (i : I) (s : G.PureStrategy) : V :=
  d.expect (fun θ => G.payoff i (G.actionProfile s θ) θ)

/-- Ex-ante payoff after a strategy deviation averages the corresponding interim action payoffs. -/
lemma exAntePayoffFin_update (i : I) (s : G.PureStrategy) (f : Θ i → A i) :
    G.exAntePayoffFin d i (update s i f) =
      ∑ t, d.marginalD i t • G.interimPayoffActionFin d i t (f t) s := by
  unfold exAntePayoffFin FinDist.expect interimPayoffActionFin
  simp_rw [Finset.smul_sum]
  conv_rhs =>
    arg 2
    ext t
    arg 2
    ext θ
    rw [← mul_smul, d.marginalD_mul_condProbD]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ _
  simp only [ite_smul, zero_smul]
  simp only [← ite_and, and_self]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  congr 2
  funext j
  by_cases h : j = i
  · subst j
    simp [actionProfile]
  · simp [actionProfile, Function.update_of_ne h]

/-- Ex-ante payoff is the marginal average of the player's interim payoffs. -/
lemma exAntePayoffFin_eq_sum (i : I) (s : G.PureStrategy) :
    G.exAntePayoffFin d i s =
      ∑ t, d.marginalD i t • G.interimPayoffActionFin d i t (s i t) s := by
  simpa only [Function.update_eq_self] using G.exAntePayoffFin_update d i s (s i)

end Finite

section Ordered

variable [AddCommGroup V] [Module ℝ V] [PartialOrder V]
  [IsOrderedAddMonoid V] [PosSMulMono ℝ V]

/-- Finite Bayesian equilibrium is equivalent to every unilateral strategy deviation weakly
lowering ex-ante payoff. -/
theorem isBNEFin_iff_exAntePayoff_update_le (s : G.PureStrategy) :
    G.IsBNEFin d s ↔ ∀ i (f : Θ i → A i),
      G.exAntePayoffFin d i (update s i f) ≤ G.exAntePayoffFin d i s := by
  rw [G.isBNEFin_iff]
  constructor
  · intro h i f
    rw [G.exAntePayoffFin_update, G.exAntePayoffFin_eq_sum]
    apply Finset.sum_le_sum
    intro t _
    by_cases hmarginal_pos : 0 < d.marginalD i t
    · exact smul_le_smul_of_nonneg_left (h i t hmarginal_pos (f t)) hmarginal_pos.le
    · have hmarginal_zero : d.marginalD i t = 0 :=
        le_antisymm (le_of_not_gt hmarginal_pos) (d.marginalD_nonneg i t)
      simp [hmarginal_zero]
  · intro h i t hp a
    have hdeviation_payoff := h i (update (s i) t a)
    rw [G.exAntePayoffFin_update, G.exAntePayoffFin_eq_sum] at hdeviation_payoff
    have hpayoff_diff :
        (∑ t', d.marginalD i t' • G.interimPayoffActionFin d i t'
          (update (s i) t a t') s) -
        (∑ t', d.marginalD i t' • G.interimPayoffActionFin d i t' (s i t') s) =
        d.marginalD i t • (G.interimPayoffActionFin d i t a s -
          G.interimPayoffActionFin d i t (s i t) s) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single t]
      · simp [smul_sub]
      · intro t' _ hne
        simp [Function.update_of_ne hne]
      · simp
    have hpayoff_diff_nonpos : d.marginalD i t • (G.interimPayoffActionFin d i t a s -
        G.interimPayoffActionFin d i t (s i t) s) ≤ 0 := by
      rw [← hpayoff_diff]
      exact sub_nonpos.mpr hdeviation_payoff
    apply sub_nonpos.mp
    exact (smul_le_smul_iff_of_pos_left hp).mp
      (by simpa only [smul_zero] using hpayoff_diff_nonpos)

end Ordered

section Measurable

variable [∀ i, MeasurableSpace (Θ i)] [∀ i, MeasurableSingletonClass (Θ i)]
    [∀ i, MeasurableSpace (A i)]

/-- Every strategy on finite discrete type spaces is measurable. -/
def toMeasurableStrategy (s : G.PureStrategy) : G.Strategy :=
  fun i => ⟨s i, measurable_of_countable _⟩

-- These finite-player and decidable-equality assumptions are not needed for the action equality.
omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (Θ i)] in
/-- Bundling measurability does not change the prescribed actions. -/
@[simp] lemma toMeasurableStrategy_apply (s : G.PureStrategy) (i : I) :
    (G.toMeasurableStrategy s i).1 = s i := rfl

-- The integral equality does not require decidable equality on type spaces.
omit [∀ i, DecidableEq (Θ i)] in
/-- Finite ex-ante expectations agree with the corresponding measurable-game integrals. -/
lemma exAntePayoffFin_eq_exAntePayoff [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (i : I) (s : G.PureStrategy) :
    G.exAntePayoffFin d i s = G.exAntePayoff d.toMeasure i (G.toMeasurableStrategy s) :=
  d.expect_eq_integral _

/-- Finite pure Bayesian equilibrium agrees with measurable equilibrium under the associated
probability measure. Neither finite action spaces nor full-support priors are required. -/
theorem isBNEFin_iff_isBNE [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [PartialOrder V] [IsOrderedAddMonoid V] [PosSMulMono ℝ V]
    (s : G.PureStrategy) :
    G.IsBNEFin d s ↔ G.IsBNE d.toMeasure (G.toMeasurableStrategy s) := by
  rw [G.isBNEFin_iff_exAntePayoff_update_le]
  constructor
  · intro h
    refine ⟨?_, fun i => d.integrable_toMeasure _⟩
    intro i s' hs'
    have hstrategy_eq : s' = G.toMeasurableStrategy (update s i (s' i).1) := by
      funext j
      by_cases hji : j = i
      · subst j
        apply Subtype.ext
        simp [toMeasurableStrategy]
      · rw [hs'.1 j hji]
        apply Subtype.ext
        simp [toMeasurableStrategy, Function.update_of_ne hji]
    change G.exAntePayoff d.toMeasure i s' ≤
      G.exAntePayoff d.toMeasure i (G.toMeasurableStrategy s)
    rw [hstrategy_eq, ← G.exAntePayoffFin_eq_exAntePayoff, ← G.exAntePayoffFin_eq_exAntePayoff]
    exact h i (s' i).1
  · intro h i f
    rw [G.exAntePayoffFin_eq_exAntePayoff, G.exAntePayoffFin_eq_exAntePayoff]
    apply h.isEquilibrium i _
    refine ⟨?_, d.integrable_toMeasure _⟩
    intro j hji
    apply Subtype.ext
    simp [toMeasurableStrategy, Function.update_of_ne hji]

end Measurable

end Auctionlib.GameTheory.BayesianGame
