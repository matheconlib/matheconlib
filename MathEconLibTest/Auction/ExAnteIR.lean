/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Auction
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Finite expected utility in ex-ante participation

A bidder with a uniform value on `(0, 1]` receives no allocation and pays the reciprocal of
their report. Truthful utility is at most `-1` almost surely and is not integrable. Its totalized
Bochner integral is zero, so the former participation inequality holds; `ExAnteIR` rejects it.
The auction's values lie in `[0, 1]` at every state. Zero and positive constant utilities provide
finite-expectation positive controls.
-/

@[expose] public noncomputable section

open MathEconLib MeasureTheory ProbabilityTheory Set

namespace MathEconLibTest.ExAnteIR

-- Pin the economic contract through the public auction umbrella.
example {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n : ℕ} (A : Auction Ω n) :
    A.ExAnteIR ↔
      (∀ i, Integrable (fun ω ↦ A.θ i ω * A.rules.outcome (A.θ · ω) i +
        A.rules.transfer i (A.θ · ω)) ℙ) ∧
      ∀ i, 0 ≤ 𝔼[fun ω ↦ A.θ i ω * A.rules.outcome (A.θ · ω) i +
        A.rules.transfer i (A.θ · ω)] := Iff.rfl

/-- The test's state space, carrying uniform probability on `(0, 1]`. -/
abbrev State := Ioc (0 : ℝ) 1

instance : MeasureSpace State := Measure.Subtype.measureSpace

instance : IsProbabilityMeasure (ℙ : Measure State) where
  measure_univ := by
    change Measure.comap (Subtype.val : State → ℝ) volume univ = 1
    rw [comap_subtype_coe_apply measurableSet_Ioc, Set.image_univ, Subtype.range_coe]
    simp

lemma not_integrable_inv : ¬ Integrable (fun v : State ↦ (v : ℝ)⁻¹) ℙ := by
  intro h
  have hinterval : IntervalIntegrable (fun v : ℝ ↦ v⁻¹) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((integrableOn_iff_comap_subtypeVal measurableSet_Ioc).mpr h)
  norm_num at hinterval

/-- A one-bidder auction with zero allocation, bounded values, and a supplied signed transfer. -/
def auction (transfer : ℝ → ℝ) : Auction State 1 where
  rules := {
    outcome := fun _ _ ↦ 0
    transfer := fun i bids ↦ transfer (bids i) }
  outcome_measurable := fun _ ↦ measurable_const
  θmin := fun _ ↦ 0
  θmax := fun _ ↦ 1
  θ := fun _ v ↦ v
  θ_measurable := fun _ ↦ measurable_subtype_coe

lemma bounded_types (transfer : ℝ → ℝ) (i : Fin 1) (v : State) :
    (auction transfer).θ i v ∈ (auction transfer).interval i := by
  exact ⟨v.property.1.le, v.property.2⟩

/-- No allocation and a charge of `1/v` at a positive report `v`. -/
def reciprocalAuction : Auction State 1 := auction (fun v ↦ -(v⁻¹))

lemma reciprocal_utility_eq_ae (i : Fin 1) :
    (fun v ↦ reciprocalAuction.θ i v *
      reciprocalAuction.rules.outcome (reciprocalAuction.θ · v) i +
        reciprocalAuction.rules.transfer i (reciprocalAuction.θ · v)) =ᵐ[ℙ]
      (fun v : State ↦ -((v : ℝ)⁻¹)) := by
  simp [reciprocalAuction, auction]

lemma not_integrable_reciprocal_utility (i : Fin 1) :
    ¬ Integrable (fun v ↦ reciprocalAuction.θ i v *
      reciprocalAuction.rules.outcome (reciprocalAuction.θ · v) i +
        reciprocalAuction.rules.transfer i (reciprocalAuction.θ · v)) ℙ := by
  intro h
  apply not_integrable_inv
  have hneg := ((integrable_congr (reciprocal_utility_eq_ae i)).mp h).neg
  convert hneg using 1
  ext v
  simp

lemma reciprocal_utility_le_neg_one (i : Fin 1) :
    ∀ᵐ v ∂ℙ, reciprocalAuction.θ i v *
      reciprocalAuction.rules.outcome (reciprocalAuction.θ · v) i +
        reciprocalAuction.rules.transfer i (reciprocalAuction.θ · v) ≤ -1 := by
  filter_upwards [reciprocal_utility_eq_ae i] with v heq
  rw [heq]
  exact neg_le_neg ((one_le_inv₀ v.property.1).mpr v.property.2)

/-- The former inequality alone accepts the divergent negative payoff. -/
theorem reciprocal_legacy_comparison :
    ∀ i, 0 ≤ 𝔼[fun v ↦ reciprocalAuction.θ i v *
      reciprocalAuction.rules.outcome (reciprocalAuction.θ · v) i +
        reciprocalAuction.rules.transfer i (reciprocalAuction.θ · v)] := by
  intro i
  rw [integral_undef (not_integrable_reciprocal_utility i)]

/-- Finite-expected-utility participation rejects the same auction. -/
theorem reciprocal_not_exAnteIR : ¬ reciprocalAuction.ExAnteIR :=
  fun h ↦ not_integrable_reciprocal_utility 0 (h.1 0)

example : (auction (fun _ ↦ 0)).ExAnteIR := by
  simp [Auction.ExAnteIR, auction]

example : (auction (fun _ ↦ 1)).ExAnteIR := by
  simp [Auction.ExAnteIR, auction]

example : ¬ (auction (fun _ ↦ -1)).ExAnteIR := by
  simp [Auction.ExAnteIR, auction]

end MathEconLibTest.ExAnteIR
