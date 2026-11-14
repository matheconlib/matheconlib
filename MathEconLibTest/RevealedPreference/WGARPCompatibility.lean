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

universe u

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
  have hnonnegative (y : Bundle L) : Nonnegative y ↔ ∀ i, 0 ≤ y i := Iff.rfl
  have hdominance (x z : Bundle L) :
      StrictDominates x z ↔ (∀ i, z i ≤ x i) ∧ x ≠ z := by
    rw [strictDominates_iff_lt, lt_iff_le_and_ne]
    exact ⟨fun h => ⟨h.1, Ne.symm h.2⟩, fun h => ⟨h.1, Ne.symm h.2⟩⟩
  simpa only [HasRegularPreferenceRationalization, ContinuousPreference,
    StrictlyIncreasingFirst, hdominance, SignAsymmetric, PreferenceRationalizes,
    Affordable, hnonnegative, and_imp] using
      wgarp_iff_hasRegularPreferenceRationalization D

-- Necessity requires no finite sample, continuity, or concavity assumption.
example {L : ℕ} {T : Type*} (D : Dataset L T) (r : PreferenceFunction L)
    (hasym : SignAsymmetric r) (hinc : StrictlyIncreasingFirst r)
    (hrat : PreferenceRationalizes D r) : WGARP D :=
  wgarp_of_asymmetric_strictlyIncreasing_rationalization D r hasym hinc hrat

example {L : ℕ} {T : Type*} [Finite T] (D : Dataset L T) :
    WGARP D ↔ ∃ r : PreferenceFunction L,
      ContinuousPreference r ∧ StrictlyIncreasingFirst r ∧ SignAsymmetric r ∧
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

-- Expand the existential package itself, including the nonempty finite coalitions.
-- There is no finiteness or nonemptiness requirement on observations or agents.
example {L : ℕ} {T : Type u} (D : Dataset L T) :
    HasFiniteCoherentCMURationalization D ↔
      ∃ (C I : Type u) (hC : Fintype C) (hne : Nonempty C)
        (members : C → Finset I) (hmembers : ∀ c, (members c).Nonempty)
        (agents : I → Bundle L → ℝ),
        (∀ c d, ∃ i, i ∈ members c ∧ i ∈ members d) ∧
        (∀ i, Continuous (agents i)) ∧
        (∀ i ⦃x z : Bundle L⦄, ((∀ k, z k ≤ x k) ∧ x ≠ z) → agents i z < agents i x) ∧
        (∀ i, ConcaveOn ℝ Set.univ (agents i)) ∧
        ∀ t y, (∀ k, 0 ≤ y k) →
          expenditure D t y ≤ expenditure D t (D.choice t) →
            0 ≤ @finiteCMU C I (Bundle L) hC hne ⟨members, hmembers⟩ agents (D.choice t) y := by
  have hinc (u : Utility L) : StrictlyIncreasing u ↔
      ∀ ⦃x z : Bundle L⦄, ((∀ k, z k ≤ x k) ∧ x ≠ z) → u z < u x := by
    rw [strictlyIncreasing_iff_strictMono]
    constructor
    · intro hu x z hxz
      exact hu (lt_iff_le_and_ne.mpr ⟨hxz.1, Ne.symm hxz.2⟩)
    · intro hu z x hzx
      exact hu ⟨le_of_lt hzx, ne_of_gt hzx⟩
  constructor
  · rintro ⟨C, I, hC, hne, ⟨members, hmembers⟩, agents, h⟩
    exact ⟨C, I, hC, hne, members, hmembers, agents,
      h.1, h.2.1, fun i => (hinc (agents i)).mp (h.2.2.1 i), h.2.2.2.1,
      fun t y hy hb => h.2.2.2.2 t y ⟨hy, hb⟩⟩
  · rintro ⟨C, I, hC, hne, members, hmembers, agents, hcoh, hc, hi, hconc, hr⟩
    exact ⟨C, I, hC, hne, ⟨members, hmembers⟩, agents,
      hcoh, hc, fun i => (hinc (agents i)).mpr (hi i), hconc,
      fun t y hy => hr t y hy.1 hy.2⟩

-- Public evaluation clients use economic comparisons without unfolding extrema.
example {C I X : Type*} (cs : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (c : C) (x y : X) :
    0 ≤ coalitionScore cs u c x y ↔ ∀ i ∈ cs.members c, u i y ≤ u i x :=
  coalitionScore_nonneg_iff cs u c x y

example {C I X : Type*} [Fintype C] [Nonempty C]
    (cs : FiniteCoalitionSystem C I) (u : I → X → ℝ) (x y : X) :
    0 ≤ finiteCMU cs u x y ↔ ∃ c, ∀ i ∈ cs.members c, u i y ≤ u i x :=
  finiteCMU_nonneg_iff cs u x y

example {C I X : Type*} [Fintype C] [Nonempty C]
    (cs : FiniteCoalitionSystem C I) (u : X → ℝ) (c : C) (x y : X) :
    coalitionScore cs (fun _ => u) c x y = u x - u y ∧
      finiteCMU cs (fun _ => u) x y = u x - u y := by
  simp

example {C I X : Type*} [Fintype C] [Nonempty C]
    (cs : FiniteCoalitionSystem C I) (u : I → X → ℝ) (c : C) (x : X) :
    coalitionScore cs u c x x = 0 ∧ finiteCMU cs u x x = 0 := by
  simp

example {L : ℕ} (u : Utility L) :
    preferenceChoice (fun x y => u x - u y) = utilityChoice u :=
  preferenceChoice_sub u

example {L : ℕ} {T : Type*} (D : Dataset L T) (u : Utility L) :
    PreferenceRationalizes D (fun x y => u x - u y) ↔ UtilityRationalizes D u :=
  preferenceRationalizes_sub_iff D u

example {L : ℕ} (u : Utility L) :
    StrictlyIncreasingFirst (fun x y => u x - u y) ↔ StrictlyIncreasing u :=
  strictlyIncreasingFirst_sub_iff u

-- Generic order and member-local hypotheses are part of the public API.
example {C I X : Type*} [Preorder X] (cs : FiniteCoalitionSystem C I)
    (u : I → X → ℝ) (c : C) (hu : ∀ i ∈ cs.members c, StrictMono (u i)) (y : X) :
    StrictMono (fun x => coalitionScore cs u c x y) :=
  coalitionScore_strictMono cs u c hu y

example {C I X : Type*} [Fintype C] [Nonempty C] [Preorder X]
    (cs : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (hu : ∀ c i, i ∈ cs.members c → StrictMono (u i)) (y : X) :
    StrictMono (fun x => finiteCMU cs u x y) :=
  finiteCMU_strictMono cs u hu y

private def singletonCoalition : FiniteCoalitionSystem Unit Bool where
  members := fun _ => {false}
  members_nonempty := fun _ => Finset.singleton_nonempty _

private def agentsWithUnusedConstant (i : Bool) (x : ℝ) : ℝ := if i then 0 else x

-- An unused constant agent does not obstruct strict monotonicity or continuity.
example (y : ℝ) :
    StrictMono (fun x => finiteCMU singletonCoalition agentsWithUnusedConstant x y) := by
  apply finiteCMU_strictMono
  intro c i hi
  have hi' : i = false := by simpa [singletonCoalition] using hi
  subst i
  exact strictMono_id

example : Continuous (fun q : ℝ × ℝ =>
    finiteCMU singletonCoalition agentsWithUnusedConstant q.1 q.2) := by
  apply finiteCMU_continuous
  intro c i hi
  have hi' : i = false := by simpa [singletonCoalition] using hi
  subst i
  exact continuous_id
