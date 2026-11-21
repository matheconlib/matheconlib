/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.WGARP.Basic

/-!
# Finite coherent coalitional multi-utility

A coalition evaluates a pair by its minimum utility difference; the family of
coalitions evaluates it by the maximum coalition score. Nonempty finite extrema
preserve joint continuity and strict increase. Pairwise intersection of coalitions
implies that the two reversed scores sum to a nonpositive number, and hence both
sign-asymmetry implications. It does not imply numerical skew symmetry.

## References and provenance

Victor H. Aguiar, Per Hjertstrand, Roberto Serrano, and Özgür Evren (2026),
*A Rationalization of the Weak Axiom of Revealed Preference*,
[arXiv:1906.00296v2](https://arxiv.org/abs/1906.00296v2), revised August 12, 2026,
Theorem 1(ii) and the finite coherent-CMU construction. Adapted from its Apache-2.0
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean) module `FiniteCMU`.
The alternative space is arbitrary for the algebraic and continuity lemmas and
preordered for monotonicity. Only agents belonging to the relevant coalitions need
continuity or strict monotonicity; unused agents impose no regularity restrictions.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

/-- A family of nonempty finite coalitions. The type `C` indexes coalitions and
`I` indexes utility functions. Finiteness and nonemptiness of the family are
separate hypotheses when its scores are aggregated. -/
structure FiniteCoalitionSystem (C I : Type*) where
  members : C → Finset I
  members_nonempty : ∀ c, (members c).Nonempty

/-- Pairwise coherence: any two admissible coalitions have a common
member. -/
def FiniteCoalitionSystem.IsCoherent {C I : Type*}
    (coalitions : FiniteCoalitionSystem C I) : Prop :=
  ∀ c d, ∃ i, i ∈ coalitions.members c ∧ i ∈ coalitions.members d

/-- The unanimous score of one coalition. -/
noncomputable def coalitionScore
    {C I X : Type*} (coalitions : FiniteCoalitionSystem C I)
    (u : I → X → ℝ) (c : C) (x y : X) : ℝ :=
  (coalitions.members c).inf' (coalitions.members_nonempty c)
    (fun i ↦ u i x - u i y)

/-- The maximum, over admissible coalitions, of their unanimous scores. -/
noncomputable def finiteCMU
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (x y : X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun c ↦ coalitionScore coalitions u c x y)

@[simp]
theorem coalitionScore_self
    {C I X : Type*} (coalitions : FiniteCoalitionSystem C I)
    (u : I → X → ℝ) (c : C) (x : X) :
    coalitionScore coalitions u c x x = 0 := by
  simp [coalitionScore]

/-- A finite CMU is exactly zero on the diagonal. -/
@[simp]
theorem finiteCMU_self
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (x : X) :
    finiteCMU coalitions u x x = 0 := by
  simp [finiteCMU, coalitionScore]

/-- A coalition has a nonnegative score exactly when all its members
weakly favor the first bundle. -/
theorem coalitionScore_nonneg_iff
    {C I X : Type*} (coalitions : FiniteCoalitionSystem C I)
    (u : I → X → ℝ) (c : C) (x y : X) :
    0 ≤ coalitionScore coalitions u c x y ↔
      ∀ i ∈ coalitions.members c, u i y ≤ u i x := by
  simp [coalitionScore, Finset.le_inf'_iff, sub_nonneg]

/-- A nonnegative CMU comparison means that some coalition unanimously
weakly favors the first bundle. -/
theorem finiteCMU_nonneg_iff
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ) (x y : X) :
    0 ≤ finiteCMU coalitions u x y ↔
      ∃ c, ∀ i ∈ coalitions.members c, u i y ≤ u i x := by
  simp [finiteCMU, Finset.le_sup'_iff, coalitionScore_nonneg_iff]

/-- Identical agents reduce a coalition score to the common utility difference. -/
@[simp]
theorem coalitionScore_const
    {C I X : Type*} (coalitions : FiniteCoalitionSystem C I)
    (u : X → ℝ) (c : C) (x y : X) :
    coalitionScore coalitions (fun _ => u) c x y = u x - u y := by
  simp [coalitionScore]

/-- Identical agents reduce every nonempty finite CMU to the common utility difference. -/
@[simp]
theorem finiteCMU_const
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : X → ℝ) (x y : X) :
    finiteCMU coalitions (fun _ => u) x y = u x - u y := by
  simp [finiteCMU]

/-- Joint continuity requires continuity only of agents participating in a coalition. -/
theorem finiteCMU_continuous
    {C I X : Type*} [Fintype C] [Nonempty C] [TopologicalSpace X]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (hu : ∀ c i, i ∈ coalitions.members c → Continuous (u i)) :
    Continuous (fun q : X × X ↦ finiteCMU coalitions u q.1 q.2) := by
  classical
  unfold finiteCMU
  apply Continuous.finset_sup'_apply
  intro c _hc
  unfold coalitionScore
  apply Continuous.finset_inf'_apply
  intro i hi
  exact ((hu c i hi).comp continuous_fst).sub ((hu c i hi).comp continuous_snd)

/-- Every component utility is strictly increasing for the paper's
dominance relation: coordinatewise weak dominance together with inequality. -/
def ComponentsStrictlyIncreasing
    {L : ℕ} {I : Type*} (u : I → Bundle L → ℝ) : Prop :=
  ∀ i, StrictlyIncreasing (u i)

/-- A coalition score is strictly monotone if every member of that coalition is.
The minimum is attained at the improved alternative. -/
theorem coalitionScore_strictMono
    {C I X : Type*} [Preorder X] (coalitions : FiniteCoalitionSystem C I)
    (u : I → X → ℝ) (c : C)
    (hu : ∀ i ∈ coalitions.members c, StrictMono (u i)) (y : X) :
    StrictMono (fun x => coalitionScore coalitions u c x y) := by
  classical
  intro x z hxz
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_mem_eq_inf' (coalitions.members_nonempty c)
      (fun j ↦ u j z - u j y)
  have hleft : coalitionScore coalitions u c x y ≤ u i x - u i y :=
    Finset.inf'_le (fun j ↦ u j x - u j y) hi
  exact hleft.trans_lt ((sub_lt_sub_right (hu i hi hxz) (u i y)).trans_eq hmin.symm)

/-- Strict monotonicity of participating agents suffices for strict monotonicity of the CMU.
The maximizing coalition is selected at the smaller alternative. -/
theorem finiteCMU_strictMono
    {C I X : Type*} [Fintype C] [Nonempty C] [Preorder X]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (hu : ∀ c i, i ∈ coalitions.members c → StrictMono (u i)) (y : X) :
    StrictMono (fun x => finiteCMU coalitions u x y) := by
  classical
  intro x z hxz
  obtain ⟨c, hc, hmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun d ↦ coalitionScore coalitions u d x y)
  have hcoalition := coalitionScore_strictMono coalitions u c (hu c) y hxz
  have hright : coalitionScore coalitions u c z y ≤ finiteCMU coalitions u z y :=
    Finset.le_sup' (fun d ↦ coalitionScore coalitions u d z y) hc
  have hleft : finiteCMU coalitions u x y = coalitionScore coalitions u c x y := by
    simpa [finiteCMU] using hmax
  exact hleft.trans_lt (hcoalition.trans_le hright)

/-- Bundle-facing strict increase requires only the selected coalition's members. -/
theorem coalitionScore_strictlyIncreasingFirst
    {C I : Type*} {L : ℕ}
    (coalitions : FiniteCoalitionSystem C I) (u : I → Bundle L → ℝ) (c : C)
    (hu : ∀ i ∈ coalitions.members c, StrictlyIncreasing (u i)) :
    StrictlyIncreasingFirst (coalitionScore coalitions u c) := by
  intro x z y hxz
  exact coalitionScore_strictMono coalitions u c
    (fun i hi => strictlyIncreasing_iff_strictMono.mp (hu i hi)) y
    (strictDominates_iff_lt.mp hxz)

/-- Bundle-facing strict increase requires only agents participating in a coalition. -/
theorem finiteCMU_strictlyIncreasingFirst
    {C I : Type*} [Fintype C] [Nonempty C] {L : ℕ}
    (coalitions : FiniteCoalitionSystem C I) (u : I → Bundle L → ℝ)
    (hu : ∀ c i, i ∈ coalitions.members c → StrictlyIncreasing (u i)) :
    StrictlyIncreasingFirst (finiteCMU coalitions u) := by
  intro x z y hxz
  exact finiteCMU_strictMono coalitions u
    (fun c i hi => strictlyIncreasing_iff_strictMono.mp (hu c i hi)) y
    (strictDominates_iff_lt.mp hxz)

/-- The strong numerical consequence of coherence.  Selecting an
attaining coalition in each direction and a common member bounds the two
coalition scores by opposite utility differences. -/
theorem finiteCMU_add_swap_nonpos
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (hcoherent : coalitions.IsCoherent) (x y : X) :
    finiteCMU coalitions u x y + finiteCMU coalitions u y x ≤ 0 := by
  classical
  obtain ⟨c, hc, hcmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun e ↦ coalitionScore coalitions u e x y)
  obtain ⟨d, hd, hdmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun e ↦ coalitionScore coalitions u e y x)
  obtain ⟨i, hic, hid⟩ := hcoherent c d
  have hc_le : coalitionScore coalitions u c x y ≤ u i x - u i y :=
    Finset.inf'_le (fun j ↦ u j x - u j y) hic
  have hd_le : coalitionScore coalitions u d y x ≤ u i y - u i x :=
    Finset.inf'_le (fun j ↦ u j y - u j x) hid
  have hxy :
      finiteCMU coalitions u x y = coalitionScore coalitions u c x y := by
    simpa [finiteCMU] using hcmax
  have hyx :
      finiteCMU coalitions u y x = coalitionScore coalitions u d y x := by
    simpa [finiteCMU] using hdmax
  rw [hxy, hyx]
  linarith

/-- Coherence implies weak sign asymmetry, including the equality case. -/
theorem finiteCMU_weakSignAsymmetry
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (hcoherent : coalitions.IsCoherent) :
    ∀ ⦃x y⦄, 0 ≤ finiteCMU coalitions u x y →
      finiteCMU coalitions u y x ≤ 0 := by
  intro x y hxy
  linarith [finiteCMU_add_swap_nonpos coalitions u hcoherent x y]

/-- Coherence implies strict sign asymmetry. -/
theorem finiteCMU_signAsymmetry
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (hcoherent : coalitions.IsCoherent) :
    ∀ ⦃x y⦄, 0 < finiteCMU coalitions u x y →
      finiteCMU coalitions u y x < 0 := by
  intro x y hxy
  linarith [finiteCMU_add_swap_nonpos coalitions u hcoherent x y]

end MathEconLib.RevealedPreference
