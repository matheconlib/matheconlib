/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLib.RevealedPreference

/-!
# Public WGARP contracts

This module imports only the public revealed-preference umbrella. The expanded
preference contract pins joint continuity, strict commodity dominance, both sign
asymmetry implications, and rationalization on every nonnegative observed budget.
The pairwise contract has no global finiteness or nonemptiness assumptions.
-/

set_option linter.privateModule false

open MathEconLib.RevealedPreference

example {L : ℕ} {T : Type*} (D : Dataset L T) :
    WGARP D ↔ ∀ s t, GARP (pairDataset D s t) :=
  wgarp_iff_pairwise_garp D

example {L : ℕ} {T : Type*} (D : Dataset L T) (h : WGARP D) (s t : T) :
    ∃ u : Utility L,
      Continuous u ∧ ConcaveOn ℝ Set.univ u ∧ StrictlyIncreasing u ∧
        (∀ y, Affordable D s y → u y ≤ u (D.choice s)) ∧
        (∀ y, Affordable D t y → u y ≤ u (D.choice t)) :=
  exists_regular_pairUtility D h s t

example {L : ℕ} {T : Type*} [Finite T] (D : Dataset L T) :
    WGARP D ↔ HasFiniteCoherentCMURationalization D :=
  wgarp_iff_hasFiniteCoherentCMURationalization D

example {L : ℕ} {T : Type*} [Finite T] (D : Dataset L T) :
    WGARP D ↔
      ∃ r : Bundle L → Bundle L → ℝ,
        Continuous (Function.uncurry r) ∧
        (∀ ⦃x z : Bundle L⦄ (y : Bundle L),
          ((∀ i, z i ≤ x i) ∧ x ≠ z) → r z y < r x y) ∧
        ((∀ x y, 0 ≤ r x y → r y x ≤ 0) ∧
          (∀ x y, 0 < r x y → r y x < 0)) ∧
        ∀ t y, (∀ i, 0 ≤ y i) →
          expenditure D t y ≤ expenditure D t (D.choice t) →
            0 ≤ r (D.choice t) y := by
  simpa only [HasRegularPreferenceRationalization, ContinuousPreference,
    StrictlyIncreasingFirst, StrictDominates, Asymmetric, PreferenceRationalizes,
    Affordable, Nonnegative, and_imp] using
      wgarp_iff_hasRegularPreferenceRationalization D

-- Necessity requires no finite sample, continuity, or concavity assumption.
example {L : ℕ} {T : Type*} (D : Dataset L T) (r : PreferenceFunction L)
    (hasym : Asymmetric r) (hinc : StrictlyIncreasingFirst r)
    (hrat : PreferenceRationalizes D r) : WGARP D :=
  wgarp_of_asymmetric_strictlyIncreasing_rationalization D r hasym hinc hrat

example {L : ℕ} {T : Type*} [Finite T] (D : Dataset L T) :
    WGARP D ↔ ∃ r : PreferenceFunction L,
      ContinuousPreference r ∧ StrictlyIncreasingFirst r ∧ Asymmetric r ∧
        ∀ t, D.choice t ∈ preferenceChoice r (budgetSet D t) :=
  wgarp_iff_exists_regular_preferenceChoice D

example {L : ℕ} {T : Type*} (D : Dataset L T) (r : PreferenceFunction L) :
    PreferenceRationalizes D r ↔ ∀ t, D.choice t ∈ preferenceChoice r (budgetSet D t) :=
  preferenceRationalizes_iff_mem_preferenceChoice D r

-- The CMU witness retains coherence and concavity of every component, rather than
-- merely assuming the resulting preference has the required properties.
example {L : ℕ} {T C I : Type*} [Fintype C] [Nonempty C]
    (D : Dataset L T) (coalitions : FiniteCoalitionSystem C I) (agents : I → Utility L) :
    FiniteCoherentCMURationalizes D coalitions agents ↔
      (∀ c d, ∃ i, i ∈ coalitions.members c ∧ i ∈ coalitions.members d) ∧
      (∀ i, Continuous (agents i)) ∧
      (∀ i, StrictlyIncreasing (agents i)) ∧
      (∀ i, ConcaveOn ℝ Set.univ (agents i)) ∧
      ∀ t y, Affordable D t y → 0 ≤ finiteCMU coalitions agents (D.choice t) y :=
  Iff.rfl

-- The converse accepts arbitrary supplied coalition and agent carriers; it does not
-- require observation-indexed coalitions or a pair-indexed utility family.
example {L : ℕ} {T C I : Type*} [Fintype C] [Nonempty C]
    (D : Dataset L T) (coalitions : FiniteCoalitionSystem C I) (agents : I → Utility L)
    (h : FiniteCoherentCMURationalizes D coalitions agents) : WGARP D :=
  h.wgarp D coalitions agents

-- Ordinary utility is included as a one-agent CMU with no observation-size restriction.
example {L : ℕ} {T : Type*} (D : Dataset L T)
    (h : HasRegularUtilityRationalization D) : HasFiniteCoherentCMURationalization D :=
  hasFiniteCoherentCMURationalization_of_hasRegularUtilityRationalization D h
