/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.WGARP.Pairwise
public import MathEconLib.RevealedPreference.WGARP.FiniteCMU
public import Mathlib.Tactic.Choose

/-!
# WGARP and finite coherent-CMU rationalization

Apply the ordinary finite Afriat theorem to each pair of observations. The coalition
for observation `s` consists of ordered pairs having `s` as either endpoint. Any two
coalitions share the pair joining them. Every member of coalition `s` rationalizes
its budget, so the finite maximum of coalition minima rationalizes all observations.

The representation predicate allows arbitrary finite nonempty coalition families;
it does not require nonempty observations. The constructive equivalences use
a row/column witness for nonempty finite observations and a singleton coalition for
empty observations. Repeated observations, a singleton sample, zero choices, and
zero commodities are allowed.

This proves the equivalence between WGARP, finite coherent-CMU rationalization with
continuous strictly increasing concave components, and continuous strictly increasing
sign-asymmetric preference rationalization. It does not assert numerical skew symmetry,
transitivity, unique demand, or choice existence on unobserved budgets.

## References and provenance

Victor H. Aguiar, Per Hjertstrand, Roberto Serrano, and Özgür Evren (2026),
*A Rationalization of the Weak Axiom of Revealed Preference*,
[arXiv:1906.00296v2](https://arxiv.org/abs/1906.00296v2), revised August 12, 2026,
Theorem 1(i), (ii), and (iv). The finite witness strengthens (ii) by giving concave
component utilities. Adapted from the Apache-2.0
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean) module `FiniteConstruction`;
the pairwise step here calls the existing finite Afriat theorem. The full six-way
statement and its matrix/simplex normal form are outside this module's scope.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

universe u

variable {L : ℕ} {T : Type u}

/-- A supplied finite coherent coalition system and regular utilities rationalize the data. -/
def FiniteCoherentCMURationalizes {C I : Type*} [Fintype C] [Nonempty C]
    (D : Dataset L T) (coalitions : FiniteCoalitionSystem C I) (agents : I → Utility L) :
    Prop :=
  coalitions.IsCoherent ∧ (∀ i, Continuous (agents i)) ∧
    ComponentsStrictlyIncreasing agents ∧ (∀ i, ConcaveOn ℝ Set.univ (agents i)) ∧
    PreferenceRationalizes D (finiteCMU coalitions agents)

/-- Existence of a finite coherent-CMU rationalization. Carrier types are unrestricted
within the observation universe; finiteness and nonemptiness concern coalitions,
not observations. Each coalition itself is a nonempty finite set of agents. -/
def HasFiniteCoherentCMURationalization (D : Dataset L T) : Prop :=
  ∃ (C I : Type u) (hC : Fintype C) (hne : Nonempty C)
    (coalitions : FiniteCoalitionSystem C I) (agents : I → Utility L),
    @FiniteCoherentCMURationalizes L T C I hC hne D coalitions agents

/-- Any supplied finite coherent-CMU witness has the regular preference properties. -/
theorem FiniteCoherentCMURationalizes.hasRegularPreferenceRationalization
    {C I : Type*} [Fintype C] [Nonempty C]
    (D : Dataset L T) (coalitions : FiniteCoalitionSystem C I) (agents : I → Utility L)
    (h : FiniteCoherentCMURationalizes D coalitions agents) :
    HasRegularPreferenceRationalization D := by
  rcases h with ⟨hcoh, hc, hi, _hconc, hr⟩
  exact ⟨finiteCMU coalitions agents,
    finiteCMU_continuous coalitions agents hc,
    finiteCMU_strictlyIncreasingFirst coalitions agents hi,
    ⟨fun _ _ hxy => finiteCMU_weakSignAsymmetry coalitions agents hcoh hxy,
      fun _ _ hxy => finiteCMU_signAsymmetry coalitions agents hcoh hxy⟩, hr⟩

/-- The necessity direction is independent of the observation and agent cardinalities. -/
theorem FiniteCoherentCMURationalizes.wgarp
    {C I : Type*} [Fintype C] [Nonempty C]
    (D : Dataset L T) (coalitions : FiniteCoalitionSystem C I) (agents : I → Utility L)
    (h : FiniteCoherentCMURationalizes D coalitions agents) : WGARP D := by
  obtain ⟨r, _hc, hi, ha, hr⟩ := h.hasRegularPreferenceRationalization D coalitions agents
  exact wgarp_of_asymmetric_strictlyIncreasing_rationalization D r ha hi hr

/-- Existence of a finite coherent-CMU witness implies WGARP without sample-size assumptions. -/
theorem wgarp_of_hasFiniteCoherentCMURationalization (D : Dataset L T)
    (h : HasFiniteCoherentCMURationalization D) : WGARP D := by
  obtain ⟨C, I, hC, hne, coalitions, agents, hr⟩ := h
  let := hC
  let := hne
  exact hr.wgarp D coalitions agents

/-- The row/column coalition attached to each observation. -/
noncomputable def rowCoalitions [Fintype T] : FiniteCoalitionSystem T (T × T) := by
  classical
  exact
    { members := fun s => Finset.univ.filter fun ij => ij.1 = s ∨ ij.2 = s
      members_nonempty := fun s => ⟨(s, s), by simp⟩ }

/-- Any two row/column coalitions share their joining ordered pair, including the diagonal. -/
theorem rowCoalitions_isCoherent [Fintype T] :
    (rowCoalitions (T := T)).IsCoherent := by
  classical
  intro s t
  exact ⟨(s, t), by simp [rowCoalitions], by simp [rowCoalitions]⟩

/-- A coalition of utilities all maximizing the observed choice gives its nonnegative score. -/
theorem finiteCMU_rationalizes_of_coalitions
    {C I : Type*} [Fintype C] [Nonempty C]
    (D : Dataset L T) (coalitions : FiniteCoalitionSystem C I) (agents : I → Utility L)
    (h : ∀ s, ∃ c, ∀ i ∈ coalitions.members c, ∀ y, Affordable D s y →
      agents i y ≤ agents i (D.choice s)) :
    PreferenceRationalizes D (finiteCMU coalitions agents) := by
  intro s y hy
  obtain ⟨c, hc⟩ := h s
  have hscore : 0 ≤ coalitionScore coalitions agents c (D.choice s) y := by
    apply Finset.le_inf'
    intro i hi
    exact sub_nonneg.mpr (hc i hi y hy)
  exact hscore.trans (Finset.le_sup'
    (fun d => coalitionScore coalitions agents d (D.choice s) y) (Finset.mem_univ c))

/-- Pair utilities need only rationalize their two endpoints; no symmetry is required. -/
theorem rowFiniteCMU_rationalizes [Fintype T] [Nonempty T]
    (D : Dataset L T) (agents : (T × T) → Utility L)
    (h : ∀ s t, (∀ y, Affordable D s y → agents (s, t) y ≤ agents (s, t) (D.choice s)) ∧
      (∀ y, Affordable D t y → agents (s, t) y ≤ agents (s, t) (D.choice t))) :
    PreferenceRationalizes D (finiteCMU rowCoalitions agents) := by
  classical
  apply finiteCMU_rationalizes_of_coalitions
  intro s
  refine ⟨s, ?_⟩
  rintro ⟨a, b⟩ hab
  simp only [rowCoalitions, Finset.mem_filter, Finset.mem_univ, true_and] at hab
  rcases hab with ha | hb
  · subst a
    exact (h s b).1
  · subst b
    exact (h a s).2

/-- The row/column construction for nonempty finite observations. -/
private theorem hasFiniteCoherentCMURationalization_of_wgarp_nonempty [Finite T] [Nonempty T]
    (D : Dataset L T) (h : WGARP D) : HasFiniteCoherentCMURationalization D := by
  classical
  let := Fintype.ofFinite T
  have hex := fun ij : T × T => exists_regular_pairUtility D h ij.1 ij.2
  choose agents hc hconc hi hfirst hsecond using hex
  refine ⟨T, T × T, inferInstance, inferInstance, rowCoalitions, agents,
    rowCoalitions_isCoherent, hc, hi, hconc, ?_⟩
  exact rowFiniteCMU_rationalizes D agents (fun s t => ⟨hfirst (s, t), hsecond (s, t)⟩)

/-- Ordinary regular utility rationalization is the one-agent, one-coalition special case. -/
theorem hasFiniteCoherentCMURationalization_of_hasRegularUtilityRationalization
    (D : Dataset L T) (h : HasRegularUtilityRationalization D) :
    HasFiniteCoherentCMURationalization D := by
  classical
  obtain ⟨u, hc, hconc, hi, hr⟩ := h
  let coalitions : FiniteCoalitionSystem (ULift.{u} Unit) (ULift.{u} Unit) :=
    { members := fun _ => {⟨()⟩}
      members_nonempty := fun _ => Finset.singleton_nonempty _ }
  have heq : finiteCMU coalitions (fun _ => u) = fun x y => u x - u y := by
    funext x y
    simp [finiteCMU, coalitionScore, coalitions]
  refine ⟨ULift.{u} Unit, ULift.{u} Unit, inferInstance, inferInstance,
    coalitions, (fun _ => u), ?_, (fun _ => hc), (fun _ => hi), (fun _ => hconc), ?_⟩
  · intro c d
    exact ⟨⟨()⟩, by simp [coalitions], by simp [coalitions]⟩
  · rw [heq]
    exact fun t y hy => sub_nonneg.mpr (hr t y hy)

/-- Empty observations impose no rationalization restrictions. A duplicate zero observation
supplies a regular utility through the same pairwise Afriat API. -/
private theorem hasRegularUtilityRationalization_of_isEmpty [IsEmpty T]
    (D : Dataset L T) : HasRegularUtilityRationalization D := by
  let D₀ : Dataset L Unit :=
    { price := fun _ _ => 1
      choice := fun _ _ => 0
      price_pos := fun _ _ => zero_lt_one
      choice_nonneg := fun _ _ => le_rfl }
  obtain ⟨u, hc, hconc, hi, _hr⟩ :=
    exists_regular_pairUtility D₀ (wgarp_of_subsingleton D₀) () ()
  exact ⟨u, hc, hconc, hi, fun t => isEmptyElim t⟩

/-- Ordinary Afriat on each pair and finite coherent aggregation give a global CMU witness.
For empty data a singleton coalition suffices. -/
theorem hasFiniteCoherentCMURationalization_of_wgarp [Finite T]
    (D : Dataset L T) (h : WGARP D) : HasFiniteCoherentCMURationalization D := by
  cases isEmpty_or_nonempty T with
  | inl hT =>
    let := hT
    exact hasFiniteCoherentCMURationalization_of_hasRegularUtilityRationalization D
      (hasRegularUtilityRationalization_of_isEmpty D)
  | inr hT =>
    let := hT
    exact hasFiniteCoherentCMURationalization_of_wgarp_nonempty D h

/-- The finite coherent-CMU characterization of WGARP for finite observations. -/
theorem wgarp_iff_hasFiniteCoherentCMURationalization [Finite T]
    (D : Dataset L T) : WGARP D ↔ HasFiniteCoherentCMURationalization D :=
  ⟨hasFiniteCoherentCMURationalization_of_wgarp D,
    wgarp_of_hasFiniteCoherentCMURationalization D⟩

/-- The preference-function characterization retains both sign-asymmetry clauses. -/
theorem wgarp_iff_hasRegularPreferenceRationalization [Finite T]
    (D : Dataset L T) : WGARP D ↔ HasRegularPreferenceRationalization D := by
  constructor
  · intro h
    obtain ⟨C, I, hC, hne, coalitions, agents, hr⟩ :=
      hasFiniteCoherentCMURationalization_of_wgarp D h
    let := hC
    let := hne
    exact hr.hasRegularPreferenceRationalization D coalitions agents
  · rintro ⟨r, _hc, hi, ha, hr⟩
    exact wgarp_of_asymmetric_strictlyIncreasing_rationalization D r ha hi hr

end MathEconLib.RevealedPreference
