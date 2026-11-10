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
The alternative space is arbitrary for the algebraic and continuity lemmas;
monotonicity specializes to the existing consumer bundle order.
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

theorem coalitionScore_self
    {C I X : Type*} (coalitions : FiniteCoalitionSystem C I)
    (u : I → X → ℝ) (c : C) (x : X) :
    coalitionScore coalitions u c x x = 0 := by
  simp [coalitionScore]

/-- A finite CMU is exactly zero on the diagonal. -/
theorem finiteCMU_self
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (x : X) :
    finiteCMU coalitions u x x = 0 := by
  simp [finiteCMU, coalitionScore]

/-- Joint continuity is preserved by both finite, attained extrema. -/
theorem finiteCMU_continuous
    {C I X : Type*} [Fintype C] [Nonempty C] [TopologicalSpace X]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (hu : ∀ i, Continuous (u i)) :
    Continuous (fun q : X × X ↦ finiteCMU coalitions u q.1 q.2) := by
  classical
  unfold finiteCMU
  apply Continuous.finset_sup'_apply
  intro c _hc
  unfold coalitionScore
  apply Continuous.finset_inf'_apply
  intro i _hi
  exact ((hu i).comp continuous_fst).sub ((hu i).comp continuous_snd)

/-- Every component utility is strictly increasing for the paper's
dominance relation: coordinatewise weak dominance together with inequality. -/
def ComponentsStrictlyIncreasing
    {L : ℕ} {I : Type*} (u : I → Bundle L → ℝ) : Prop :=
  ∀ i, StrictlyIncreasing (u i)

/-- The inner minimum is strictly increasing in its first argument.

The minimizing member is chosen at the *improved* bundle.  This witness
is the finite attained-extremum step that makes the strict inequality
valid. -/
theorem coalitionScore_strictlyIncreasingFirst
    {C I : Type*} {L : ℕ}
    (coalitions : FiniteCoalitionSystem C I)
    (u : I → Bundle L → ℝ)
    (hu : ComponentsStrictlyIncreasing u) (c : C) :
    ∀ ⦃x z y⦄, StrictDominates z x →
      coalitionScore coalitions u c x y <
        coalitionScore coalitions u c z y := by
  classical
  intro x z y hxz
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_mem_eq_inf' (coalitions.members_nonempty c)
      (fun j ↦ u j z - u j y)
  have hleft :
      coalitionScore coalitions u c x y ≤ u i x - u i y :=
    Finset.inf'_le (fun j ↦ u j x - u j y) hi
  have hcomponent : u i x - u i y < u i z - u i y := by
    exact sub_lt_sub_right (hu i hxz) (u i y)
  have hright :
      coalitionScore coalitions u c z y = u i z - u i y := hmin
  exact hleft.trans_lt (hcomponent.trans_eq hright.symm)

/-- Strictly increasing agents make the finite CMU strictly increasing
in its first argument.

Here the outer maximizing coalition is chosen at the *smaller* bundle,
the complementary attained-extremum witness to the preceding lemma. -/
theorem finiteCMU_strictlyIncreasingFirst
    {C I : Type*} [Fintype C] [Nonempty C] {L : ℕ}
    (coalitions : FiniteCoalitionSystem C I)
    (u : I → Bundle L → ℝ)
    (hu : ComponentsStrictlyIncreasing u) :
    StrictlyIncreasingFirst (finiteCMU coalitions u) := by
  classical
  intro x z y hxz
  obtain ⟨c, hc, hmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun d ↦ coalitionScore coalitions u d z y)
  have hcoalition :
      coalitionScore coalitions u c z y <
        coalitionScore coalitions u c x y :=
    coalitionScore_strictlyIncreasingFirst coalitions u hu c hxz
  have hright :
      coalitionScore coalitions u c x y ≤ finiteCMU coalitions u x y :=
    Finset.le_sup' (fun d ↦ coalitionScore coalitions u d x y) hc
  have hleft :
      finiteCMU coalitions u z y = coalitionScore coalitions u c z y := by
    simpa [finiteCMU] using hmax
  rw [hleft]
  exact hcoalition.trans_le hright

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
