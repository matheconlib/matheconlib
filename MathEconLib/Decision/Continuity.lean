/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Decision.Lottery
public import MathEconLib.Preferences.Representation.Basic

/-!
# Continuity of preferences over lotteries

A preference `R` over lotteries is *continuous in mixtures* on `S` if, for `r ≺ q ≺ p` in `S`,
some `α · p ⊕ (1 − α) · r` with `0 < α < 1` is indifferent to `q` (von Neumann–Morgenstern
continuity).

## Main definitions

* `IsMixtureContinuousOn`, `IsMixtureContinuous`: continuity in mixtures on `S` and on all
  lotteries.

## Main statements

* `isMixtureContinuousOn_of_not_exists`: a preference without a chain `r ≺ q ≺ p` in `S` is
  continuous in mixtures on `S`.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Definition 3.2
-/

@[expose] public section

namespace MathEconLib.Decision

open MathEconLib.Probability MathEconLib.Preferences

universe u

variable {Z : Type u} [Fintype Z] {R : Preference (FinDist Z)} {S S' : Set (FinDist Z)}

/-- *Continuity in mixtures on `S`*: `r ≺ q ≺ p` in `S` give `q ∼ mix α p r` for a `0 < α < 1`. -/
def IsMixtureContinuousOn (S : Set (FinDist Z)) (R : Preference (FinDist Z)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, q ≺[R] p → r ≺[R] q →
    ∃ α : unitInterval, 0 < (α : ℝ) ∧ (α : ℝ) < 1 ∧ q ~[R] FinDist.mixture α p r

/-- *Continuity in mixtures* on all lotteries. -/
def IsMixtureContinuous (R : Preference (FinDist Z)) : Prop :=
  IsMixtureContinuousOn Set.univ R

theorem isMixtureContinuousOn_iff : IsMixtureContinuousOn S R ↔
    ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, q ≺[R] p → r ≺[R] q →
      ∃ α : unitInterval, 0 < (α : ℝ) ∧ (α : ℝ) < 1 ∧ q ~[R] FinDist.mixture α p r :=
  Iff.rfl

theorem isMixtureContinuous_iff : IsMixtureContinuous R ↔
    ∀ p q r : FinDist Z, q ≺[R] p → r ≺[R] q →
      ∃ α : unitInterval, 0 < (α : ℝ) ∧ (α : ℝ) < 1 ∧ q ~[R] FinDist.mixture α p r :=
  ⟨fun h p q r => h p trivial q trivial r trivial, fun h p _ q _ r _ => h p q r⟩

theorem IsMixtureContinuousOn.mono (h : IsMixtureContinuousOn S R) (hS : S' ⊆ S) :
    IsMixtureContinuousOn S' R :=
  fun p hp q hq r hr => h p (hS hp) q (hS hq) r (hS hr)

theorem IsMixtureContinuous.isMixtureContinuousOn (h : IsMixtureContinuous R)
    (S : Set (FinDist Z)) : IsMixtureContinuousOn S R :=
  h.mono (Set.subset_univ S)

theorem isMixtureContinuousOn_of_not_exists
    (h : ¬ ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, q ≺[R] p ∧ r ≺[R] q) :
    IsMixtureContinuousOn S R :=
  fun p hp q hq r hr hpq hqr => absurd ⟨p, hp, q, hq, r, hr, hpq, hqr⟩ h

end MathEconLib.Decision

section Examples

open MathEconLib.Probability MathEconLib.Decision MathEconLib.Preferences

/-- Indifference between all lotteries is continuous in mixtures. -/
example : IsMixtureContinuous (Preference.ofUtility fun _ : FinDist (Fin 3) => (0 : ℕ)) :=
  isMixtureContinuousOn_of_not_exists fun ⟨_, _, _, _, _, _, h, _⟩ =>
    lt_irrefl 0 ((Preference.ofUtility_lt_iff _ _ _).1 h)

/-- A preference with `[2] ≺ [1] ≺ [0]` that is not continuous in mixtures on degenerate
lotteries. -/
example (u : FinDist (Fin 3) → ℝ) (hu0 : u (FinDist.pure 0) = 2) (hu1 : u (FinDist.pure 1) = 1)
    (hu : ∀ p, p ≠ FinDist.pure 0 → p ≠ FinDist.pure 1 → u p = 0) :
    ¬ IsMixtureContinuousOn degenerate (Preference.ofUtility u) := by
  intro h
  have hne : ∀ {i j : Fin 3}, i ≠ j → FinDist.pure i ≠ (FinDist.pure j : FinDist (Fin 3)) :=
    fun {i j} hij he => by
      have := congrArg (fun d : FinDist (Fin 3) => d.pmf i) he
      simp [Ne.symm hij] at this
  have hu2 : u (FinDist.pure 2) = 0 := hu _ (hne (by decide)) (hne (by decide))
  obtain ⟨α, -, hα1, hind⟩ := h _ (pure_mem_degenerate 0) _ (pure_mem_degenerate 1) _
    (pure_mem_degenerate 2)
    ((Preference.ofUtility_lt_iff _ _ _).2 (by rw [hu0, hu1]; norm_num))
    ((Preference.ofUtility_lt_iff _ _ _).2 (by rw [hu1, hu2]; norm_num))
  have hm0 : FinDist.mixture α (FinDist.pure 0) (FinDist.pure 2) ≠
      (FinDist.pure 0 : FinDist (Fin 3)) := fun he => by
    have h0 := congrArg (fun p : FinDist (Fin 3) => p.pmf 0) he
    simp only [FinDist.mixture_pmf, FinDist.pure_pmf] at h0
    norm_num at h0
    rw [h0] at hα1
    exact lt_irrefl _ hα1
  have hm1 : FinDist.mixture α (FinDist.pure 0) (FinDist.pure 2) ≠
      (FinDist.pure 1 : FinDist (Fin 3)) := fun he => by
    have h1 := congrArg (fun p : FinDist (Fin 3) => p.pmf 1) he
    simp only [FinDist.mixture_pmf, FinDist.pure_pmf] at h1
    norm_num at h1
  have := (Preference.ofUtility_antisymmRel_iff u _ _).1 hind
  rw [hu1, hu _ hm0 hm1] at this
  norm_num at this

end Examples
