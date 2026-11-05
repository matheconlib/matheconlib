/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.DecisionTheory.Lottery
public import MathEconLib.Preferences.Relation

/-!
# Continuity of preferences over lotteries

A relation `≿` over lotteries is *continuous in mixtures* on `S` if, for `p ≻ q ≻ r` in `S`, some
`α · p ⊕ (1 − α) · r` with `0 < α < 1` is indifferent to `q` (von Neumann–Morgenstern continuity).

## Main definitions

* `IsMixtureContinuousOn`, `IsMixtureContinuous`, and their `Lottery` versions on `Lottery Z`.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Definition 3.2
-/

@[expose] public section

namespace MathEconLib.DecisionTheory

open Convexity MathEconLib.Preferences

universe u

namespace Lottery

variable {Z : Type u} {R : Lottery Z → Lottery Z → Prop} {S S' : Set (Lottery Z)}

/-- *Continuity in mixtures on `S`*: `p ≻ q ≻ r` in `S` give `q ∼ mix α p r` for a `0 < α < 1`. -/
def IsMixtureContinuousOn (S : Set (Lottery Z)) (R : Lottery Z → Lottery Z → Prop) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, StrictPart R p q → StrictPart R q r →
    ∃ α : unitInterval, 0 < (α : ℝ) ∧ (α : ℝ) < 1 ∧ Indiff R q (mix α p r)

/-- *Continuity in mixtures* on all lotteries. -/
def IsMixtureContinuous (R : Lottery Z → Lottery Z → Prop) : Prop :=
  IsMixtureContinuousOn Set.univ R

theorem isMixtureContinuousOn_iff : IsMixtureContinuousOn S R ↔
    ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, StrictPart R p q → StrictPart R q r →
      ∃ α : unitInterval, 0 < (α : ℝ) ∧ (α : ℝ) < 1 ∧ Indiff R q (mix α p r) :=
  Iff.rfl

theorem isMixtureContinuous_iff : IsMixtureContinuous R ↔
    ∀ p q r : Lottery Z, StrictPart R p q → StrictPart R q r →
      ∃ α : unitInterval, 0 < (α : ℝ) ∧ (α : ℝ) < 1 ∧ Indiff R q (mix α p r) :=
  ⟨fun h p q r => h p trivial q trivial r trivial, fun h p _ q _ r _ => h p q r⟩

theorem IsMixtureContinuousOn.mono (h : IsMixtureContinuousOn S R) (hS : S' ⊆ S) :
    IsMixtureContinuousOn S' R :=
  fun p hp q hq r hr => h p (hS hp) q (hS hq) r (hS hr)

theorem IsMixtureContinuous.isMixtureContinuousOn (h : IsMixtureContinuous R)
    (S : Set (Lottery Z)) : IsMixtureContinuousOn S R :=
  h.mono (Set.subset_univ S)

theorem isMixtureContinuousOn_of_not_exists
    (h : ¬ ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, StrictPart R p q ∧ StrictPart R q r) :
    IsMixtureContinuousOn S R :=
  fun p hp q hq r hr hpq hqr => absurd ⟨p, hp, q, hq, r, hr, hpq, hqr⟩ h

end Lottery

section FinDist

open MathEconLib.Probability

variable {Z : Type u} [Fintype Z] {R : FinDist Z → FinDist Z → Prop} {S : Set (FinDist Z)}

/-- *Continuity in mixtures on `S`*, for distributions. -/
def IsMixtureContinuousOn (S : Set (FinDist Z)) (R : FinDist Z → FinDist Z → Prop) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, StrictPart R p q → StrictPart R q r →
    ∃ α : unitInterval, 0 < (α : ℝ) ∧ (α : ℝ) < 1 ∧ Indiff R q (FinDist.mixture α p r)

/-- *Continuity in mixtures* on all distributions. -/
def IsMixtureContinuous (R : FinDist Z → FinDist Z → Prop) : Prop :=
  IsMixtureContinuousOn Set.univ R

/-- Continuity in mixtures on `S` is continuity on lotteries on the image of `S`. -/
theorem isMixtureContinuousOn_iff_lottery : IsMixtureContinuousOn S R ↔
    Lottery.IsMixtureContinuousOn (Lottery.ofFinDist '' S) (Lottery.ofFinDist.symm ⁻¹'o R) := by
  simp only [IsMixtureContinuousOn, Lottery.IsMixtureContinuousOn, Set.forall_mem_image,
    ← Lottery.ofFinDist_mixture, strictPart_iff, indiff_iff, Order.Preimage,
    Equiv.symm_apply_apply]

theorem isMixtureContinuous_iff_lottery :
    IsMixtureContinuous R ↔ Lottery.IsMixtureContinuous (Lottery.ofFinDist.symm ⁻¹'o R) := by
  rw [IsMixtureContinuous, Lottery.IsMixtureContinuous, isMixtureContinuousOn_iff_lottery,
    Set.image_univ, Equiv.range_eq_univ]

end FinDist

end MathEconLib.DecisionTheory

section Examples

open MathEconLib.DecisionTheory (Lottery)
open MathEconLib.DecisionTheory.Lottery MathEconLib.Preferences Convexity

example : IsMixtureContinuous fun _ _ : Lottery (Fin 3) => True :=
  isMixtureContinuousOn_of_not_exists fun ⟨_, _, _, _, _, _, h, _⟩ => h.2 trivial

/-- A relation with `[0] ≻ [1] ≻ [2]` that is not continuous in mixtures on degenerate lotteries. -/
example (u : Lottery (Fin 3) → ℝ) (hu0 : u (.single 0) = 2) (hu1 : u (.single 1) = 1)
    (hu : ∀ p, p ≠ .single 0 → p ≠ .single 1 → u p = 0) :
    ¬ IsMixtureContinuousOn degenerate (fun p q : Lottery (Fin 3) => u q ≤ u p) := by
  intro h
  have h20 : (StdSimplex.single 2 : Lottery (Fin 3)) ≠ .single 0 :=
    StdSimplex.single_injective.ne (by decide)
  have h21 : (StdSimplex.single 2 : Lottery (Fin 3)) ≠ .single 1 :=
    StdSimplex.single_injective.ne (by decide)
  have hu2 : u (.single 2) = 0 := hu _ h20 h21
  obtain ⟨α, -, hα1, hind⟩ := h _ (single_mem_degenerate 0) _ (single_mem_degenerate 1) _
    (single_mem_degenerate 2)
    ⟨by simp only [hu0, hu1]; norm_num, by simp only [hu0, hu1]; norm_num⟩
    ⟨by simp only [hu1, hu2]; norm_num, by simp only [hu1, hu2]; norm_num⟩
  have hm0 : mix α (.single 0) (.single 2) ≠ (.single 0 : Lottery (Fin 3)) := fun he => by
    have h0 := congrArg (fun p : Lottery (Fin 3) => p.weights 0) he
    simp only [weights_mix, StdSimplex.weights_single, Finsupp.single_eq_same,
      Finsupp.single_apply] at h0
    norm_num at h0
    rw [h0] at hα1
    exact lt_irrefl _ hα1
  have hm1 : mix α (.single 0) (.single 2) ≠ (.single 1 : Lottery (Fin 3)) := fun he => by
    have h1 := congrArg (fun p : Lottery (Fin 3) => p.weights 1) he
    simp only [weights_mix, StdSimplex.weights_single, Finsupp.single_eq_same,
      Finsupp.single_apply] at h1
    norm_num at h1
  have := hind.2
  simp only [hu1, hu _ hm0 hm1] at this
  norm_num at this

end Examples
