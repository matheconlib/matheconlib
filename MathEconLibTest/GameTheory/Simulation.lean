/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Simulation
public import MathEconLibTest.GameTheory.CandidateValidity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Applications and boundaries of equilibrium simulation

A coin action lies outside a compiler's image, so no exact morphism reaches it, but its value is
bounded by a legal source action. Simulation transports equilibrium to the enlarged game. The
tests also check composition, reflection, value recodings across different value spaces and
player sets, additive errors, and comparison transport where no global value map exists.

The candidate-validity fixtures check that validity is not weakened by domination: an invalid
incumbent stays excluded, an admitted improving deviation to an invalid candidate still counts,
and preserving validity and equilibrium does not reflect it. Chained additive errors are
transported one step at a time, because the step premises need not imply the composite's premise
once the first step raises the incumbent.

Signature pins for this layer live in `MathEconLibTest.GameTheory.SimulationApi`.
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory

namespace MathEconLibTest.GameTheory.Simulation

/-- Two source actions earn zero or one. -/
def source : EquilibriumProblem Bool Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun _ b ↦ if b then 1 else 0)

/-- The added action earns one half. -/
def target : EquilibriumProblem (Fin 3) Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun _ q ↦ (q.val : ℝ) / 2)

/-- Compilation includes the two deterministic actions. -/
def compile (b : Bool) : Fin 3 := if b then 2 else 0

lemma target_value_le_one (q : Fin 3) : target.value () q ≤ 1 := by
  change (q.val : ℝ) / 2 ≤ 1
  have hq : (q.val : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ q.isLt
  linarith

/-- The added coin action is bounded by the best source action. -/
def domination : GameSimulation source target where
  toFun := compile
  deviatorMap := id
  valueMap _ := OrderHom.id
  incumbent_value_le _ b := by cases b <;> norm_num [source, target, compile,
    EquilibriumProblem.ofDeviation]
  deviation_dominated _ _ q _ := ⟨true, trivial, target_value_le_one q⟩
  valid_preserves _ _ := trivial

theorem source_equilibrium : source.IsEquilibrium true := by
  refine ⟨trivial, ?_⟩
  intro _ b _
  cases b <;> norm_num [source, EquilibriumProblem.ofDeviation]

/-- The public simulation theorem establishes equilibrium in the enlarged game. -/
theorem target_equilibrium : target.IsEquilibrium (compile true) :=
  domination.transport source_equilibrium

/-- The chosen compiler cannot lift the new target action exactly. -/
theorem no_exact_morphism : ¬ ∃ f : GameMorphism source target, f.toFun = compile := by
  rintro ⟨f, hf⟩
  obtain ⟨b, _, hb⟩ := f.deviation_lifts () false 1 trivial
  rw [hf] at hb
  cases b <;> norm_num [compile] at hb

/-- Honest compilation maps source deviations, giving independent reflection. -/
def reflection : GameComorphism source target where
  toFun := compile
  deviatorMap := id
  deviation_maps _ _ _ _ := trivial
  value_eq _ b := by cases b <;> norm_num [source, target, compile,
    EquilibriumProblem.ofDeviation]
  valid_reflects _ _ := trivial

theorem equilibrium_iff (b : Bool) : target.IsEquilibrium (compile b) ↔ source.IsEquilibrium b :=
  domination.isEquilibrium_iff reflection rfl b

/-- Coarsening all target states to one state can improve incumbent values. -/
def terminal : EquilibriumProblem Unit Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun _ _ ↦ 1)

def coarsening : GameSimulation target terminal where
  toFun _ := ()
  deviatorMap := id
  valueMap _ := OrderHom.id
  incumbent_value_le _ q := target_value_le_one q
  deviation_dominated _ _ _ _ := by
    refine ⟨2, trivial, ?_⟩
    norm_num [terminal, target, EquilibriumProblem.ofDeviation]
  valid_preserves _ _ := trivial

theorem composed_equilibrium : terminal.IsEquilibrium () :=
  (coarsening.comp domination).transport source_equilibrium

/-! ## Value coordinates and comparison transport -/

/-- Two target players share one source player but use different value coordinates. -/
def vectorRecoding (j : Bool) : ℝ →o ℝ × ℝ where
  toFun x := (if j then 2 * x + 3 else x + 1, x + 7)
  monotone' := by
    intro x y h
    constructor
    · cases j <;> dsimp <;> linarith
    · exact add_le_add_left h 7

def vectorTarget : EquilibriumProblem (Fin 3) Bool (ℝ × ℝ) :=
  .ofDeviation (fun _ _ _ ↦ True) (fun j q ↦ vectorRecoding j (target.value () q))

def recoding : GameSimulation target vectorTarget :=
  .ofExactLifts id (fun _ ↦ ()) vectorRecoding (fun _ _ ↦ rfl)
    (fun _ _ t _ ↦ ⟨t, trivial, rfl⟩) (fun _ _ ↦ trivial)

/-- Reflection works across value spaces even when the compiler omits a target state. -/
theorem cross_value_equilibrium_iff (b : Bool) :
    vectorTarget.IsEquilibrium (compile b) ↔ source.IsEquilibrium b := by
  apply (recoding.comp domination).isEquilibrium_iff_of_deviation_comparisons
    (fun _ ↦ false) (fun _ ↦ trivial)
  intro i b' _
  refine ⟨compile b', trivial, fun hle ↦ ?_⟩
  have hscalar := (add_le_add_iff_right (7 : ℝ)).mp hle.2
  exact (reflection.value_eq () b').ge.trans (hscalar.trans (reflection.value_eq () b).le)

def firstCoordinate : (ℝ × ℝ) →o ℝ :=
  ⟨fun v ↦ v.1 + 11, fun _ _ h ↦ add_le_add_left h.1 11⟩

def finalTarget : EquilibriumProblem (Fin 3) Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun _ q ↦ firstCoordinate (vectorTarget.value true q))

def projecting : GameSimulation vectorTarget finalTarget :=
  .ofExactLifts id (fun _ ↦ true) (fun _ ↦ firstCoordinate) (fun _ _ ↦ rfl)
    (fun _ _ t _ ↦ ⟨t, trivial, rfl⟩) (fun _ _ ↦ trivial)

/-- Nontrivial value maps compose across different value spaces and player sets. -/
theorem recoded_equilibrium : finalTarget.IsEquilibrium (compile true) :=
  (projecting.comp (recoding.comp domination)).transport source_equilibrium

def affineRecoding : ℝ →o ℝ :=
  ⟨fun x ↦ 3 * x + 7, fun _ _ h ↦ by linarith⟩

def rescaled : EquilibriumProblem Bool Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun j b ↦ affineRecoding (source.value j b))

def rescaling : GameSimulation source rescaled :=
  .ofExactLifts id id (fun _ ↦ affineRecoding) (fun _ _ ↦ rfl)
    (fun _ _ t ht ↦ ⟨t, ht, rfl⟩) (fun _ ht ↦ ht)

/-- The compatibility premise scales errors by the affine slope, not by the offset. -/
theorem rescaled_error {s : Bool} (ε : ℝ)
    (h : ∀ i b, source.deviation i s b → source.value i b ≤ source.value i s + ε) :
    ∀ j b, rescaled.deviation j s b → rescaled.value j b ≤ rescaled.value j s + 3 * ε := by
  apply rescaling.transport_le_add (fun _ ↦ ε) (fun _ ↦ 3 * ε) _ h
  intro j
  change 3 * (source.value () s + ε) + 7 ≤ (3 * source.value () s + 7) + 3 * ε
  linarith

theorem rescaled_approximate_false :
    ∀ j b, rescaled.deviation j false b → rescaled.value j b ≤ rescaled.value j false + 3 := by
  simpa only [mul_one] using rescaled_error (s := false) 1
    (by intro i b _; cases b <;> norm_num [source, EquilibriumProblem.ofDeviation])

/-- Monotonicity alone does not preserve the numerical size of an error. -/
theorem same_error_fails : ¬ ∀ j b, rescaled.deviation j false b →
    rescaled.value j b ≤ rescaled.value j false + 1 := by
  intro h
  have := h () true trivial
  change 3 * 1 + 7 ≤ (3 * 0 + 7 : ℝ) + 1 at this
  norm_num at this

/-- The second coordinate is fixed during every admitted deviation. -/
def contextualSource : EquilibriumProblem (Bool × Bool) Unit ℝ :=
  .ofDeviation (fun _ s t ↦ t.2 = s.2) (fun _ s ↦ if s.1 then 1 else 0)

def contextualTarget : EquilibriumProblem (Bool × Bool) Unit ℝ :=
  .ofDeviation contextualSource.deviation
    (fun i s ↦ contextualSource.value i s + if s.2 then 10 else 0)

/-- Offsets constant along legal deviations need no global function of source values. -/
theorem contextual_transport {s : Bool × Bool} (h : contextualSource.IsEquilibrium s) :
    contextualTarget.IsEquilibrium s := by
  apply h.of_deviation_comparisons id trivial
  intro i t ht
  refine ⟨t, ht, fun hle ↦ ?_⟩
  change t.2 = s.2 at ht
  change contextualSource.value i t + _ ≤ contextualSource.value i s + _
  rw [ht]
  exact add_le_add_left hle _

example : contextualTarget.IsEquilibrium (true, false) :=
  contextual_transport ⟨trivial, by
    intro i t _
    change (if t.1 then (1 : ℝ) else 0) ≤ 1
    split <;> norm_num⟩

theorem no_global_value_map : ¬ ∃ φ : ℝ → ℝ,
    ∀ s, contextualTarget.value () s = φ (contextualSource.value () s) := by
  rintro ⟨φ, hφ⟩
  have h0 := hφ (true, false)
  have h1 := hφ (true, true)
  norm_num [contextualSource, contextualTarget, EquilibriumProblem.ofDeviation] at h0 h1
  linarith

/-- The target player minimizes a cost: it weakly prefers `y` to `x` when `y ≤ x`. -/
def costTarget : EquilibriumProblem (Fin 3) Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun _ q ↦ -target.value () q)

/-- Explicit comparisons transport an ordered equilibrium to a cost-minimizing reading. -/
theorem cost_equilibrium :
    costTarget.IsEquilibriumWith (fun _ x y ↦ y ≤ x) (compile true) :=
  ((target.isEquilibriumWith_le_iff _).2 target_equilibrium).of_deviation_comparisons id trivial
    fun _ q _ ↦ ⟨q, trivial, fun hle ↦ neg_le_neg hle⟩

/-! ## Candidate validity -/

section CandidateValidity

open MathEconLibTest.GameTheory.CandidateValidity

/-- Coarsening, as a simulation, transports with a nonconstant validity condition. -/
def coarsening' : GameSimulation descendingSource descendingTarget :=
  coarseningMorphism.toSimulation

example : descendingTarget.IsEquilibrium 1 :=
  coarsening'.transport source_isEquilibrium

/-- The invalid source state one has no improving deviation. -/
theorem source_one_isDeviationOptimal : descendingSource.IsDeviationOptimal 1 := by
  intro _ t ht
  change t < 1 at ht
  change t / 2 ≤ 1 / 2
  omega

/-- Domination carries deviation optimality from an invalid incumbent, but the incumbent stays
excluded on both sides: it is not a source equilibrium, and its image is not a target one. -/
theorem invalid_incumbent_excluded :
    descendingTarget.IsDeviationOptimal (coarsening'.toFun 1) ∧
      ¬ descendingSource.IsEquilibrium 1 ∧
      ¬ descendingTarget.IsEquilibrium (coarsening'.toFun 1) := by
  refine ⟨coarsening'.transport_isDeviationOptimal source_one_isDeviationOptimal, ?_, ?_⟩
  · intro h
    have : 2 ≤ 1 := h.valid
    omega
  · intro h
    have : 1 ≤ 1 / 2 := h.valid
    omega

/-- No simulation from a problem without deviations reaches the valid state of
`improvingDeviation`: domination must cover its improving deviation even though that deviation
leads to an invalid candidate. -/
theorem no_simulation_to_improvingDeviation :
    ¬ ∃ f : GameSimulation noDeviations improvingDeviation, f.toFun true = true := by
  rintro ⟨f, hf⟩
  apply improving_invalid_target_not_isEquilibrium
  rw [← hf]
  exact f.transport ⟨rfl, fun _ _ h ↦ h.elim⟩

/-- Forgetting all deviations is a simulation that preserves validity, since both problems
admit only `true`, and bounds incumbent values by recoding them to zero. -/
def forgetDeviations : GameSimulation improvingDeviation noDeviations where
  toFun := id
  deviatorMap := id
  valueMap _ := OrderHom.const ℕ 0
  incumbent_value_le _ _ := le_rfl
  deviation_dominated _ _ _ h := h.elim
  valid_preserves _ h := h

/-- Preservation alone does not give reflection: the image of `true` is an equilibrium, its
validity reflects, and yet the source incumbent is not an equilibrium. -/
theorem forgetDeviations_not_reflect :
    noDeviations.IsEquilibrium (forgetDeviations.toFun true) ∧
      (noDeviations.valid (forgetDeviations.toFun true) → improvingDeviation.valid true) ∧
      ¬ improvingDeviation.IsEquilibrium true :=
  ⟨⟨rfl, fun _ _ h ↦ h.elim⟩, id, improving_invalid_target_not_isEquilibrium⟩

end CandidateValidity

/-! ## Chained additive errors -/

/-- The first step raises the incumbent `false` from `0` to `1 / 2`. -/
def raised : EquilibriumProblem Bool Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun _ b ↦ if b then 1 else 1 / 2)

def raising : GameSimulation source raised where
  toFun := id
  deviatorMap := id
  valueMap _ := OrderHom.id
  incumbent_value_le _ b := by
    cases b <;> norm_num [source, raised, EquilibriumProblem.ofDeviation]
  deviation_dominated _ _ b _ := ⟨true, trivial, by
    cases b <;> norm_num [source, raised, EquilibriumProblem.ofDeviation]⟩
  valid_preserves _ _ := trivial

/-- A concave recoding with slope three below `1 / 2` and slope one above it. -/
def concave : ℝ →o ℝ :=
  ⟨fun x ↦ min (3 * x) (x + 1), fun _ _ h ↦ min_le_min (by linarith) (by linarith)⟩

@[simp] lemma concave_apply (x : ℝ) : concave x = min (3 * x) (x + 1) := rfl

def concaveTarget : EquilibriumProblem Bool Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun j b ↦ concave (raised.value j b))

def concaving : GameSimulation raised concaveTarget :=
  .ofExactLifts id id (fun _ ↦ concave) (fun _ _ ↦ rfl)
    (fun _ _ t ht ↦ ⟨t, ht, rfl⟩) (fun _ ht ↦ ht)

theorem source_error_false :
    ∀ i b, source.deviation i false b → source.value i b ≤ source.value i false + 1 := by
  intro i b _
  cases b <;> norm_num [source, EquilibriumProblem.ofDeviation]

/-- Applying `transport_le_add` once per step keeps the error at one. The second premise is
checked at the raised incumbent `1 / 2`, where the recoding has slope one. -/
theorem chained_error :
    ∀ j b, concaveTarget.deviation j false b →
      concaveTarget.value j b ≤ concaveTarget.value j false + 1 :=
  concaving.transport_le_add (s := false) (fun _ ↦ 1) (fun _ ↦ 1)
    (fun _ ↦ by norm_num [concaving, GameSimulation.ofExactLifts, raised,
      EquilibriumProblem.ofDeviation])
    (raising.transport_le_add (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ le_rfl) source_error_false)

/-- The step premises do not yield the composite's premise with the same error. The composite is
evaluated at the source incumbent `0`, below the kink, where the recoding has slope three. -/
theorem composite_premise_fails :
    ¬ ∀ j, (concaving.comp raising).valueMap j
        (source.value ((concaving.comp raising).deviatorMap j) false + 1) ≤
      (concaving.comp raising).valueMap j
        (source.value ((concaving.comp raising).deviatorMap j) false) + 1 := by
  intro h
  have h' := h ()
  norm_num [GameSimulation.comp, concaving, raising, GameSimulation.ofExactLifts, source,
    EquilibriumProblem.ofDeviation] at h'

end MathEconLibTest.GameTheory.Simulation
