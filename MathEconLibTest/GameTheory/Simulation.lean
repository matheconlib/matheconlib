/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Simulation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Applications and boundaries of equilibrium simulation

A coin action lies outside a compiler's image, so no exact morphism reaches it, but its value is
bounded by a legal source action. Simulation transports equilibrium to the enlarged game. The
tests also check composition, reflection, value recodings across different value spaces and
player sets, additive errors, and comparison transport where no global value map exists.
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
  value_le _ b := by cases b <;> norm_num [source, target, compile,
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
  value_le _ q := target_value_le_one q
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

end MathEconLibTest.GameTheory.Simulation

/-! ## Signatures -/

section Signatures

open MathEconLib.GameTheory

example {S I T J V W : Type*} [Preorder V] [Preorder W]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    (f : GameSimulation P Q) {s : S} (h : P.IsEquilibrium s) :
    Q.IsEquilibrium (f.toFun s) := f.transport h

example {S I T J V W : Type*} [Preorder V] [Preorder W] [Add V] [Add W] [AddRightMono W]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    (f : GameSimulation P Q) (ε : I → V) (δ : J → W) {s : S}
    (herror : ∀ j, f.valueMap j (P.value (f.deviatorMap j) s + ε (f.deviatorMap j)) ≤
      f.valueMap j (P.value (f.deviatorMap j) s) + δ j)
    (h : ∀ i s', P.deviation i s s' → P.value i s' ≤ P.value i s + ε i) :
    ∀ j t, Q.deviation j (f.toFun s) t → Q.value j t ≤ Q.value j (f.toFun s) + δ j :=
  f.transport_le_add ε δ herror h

/-- The ordered comparison core requires no order laws and permits different value spaces. -/
example {S I T J V W : Type*} [LE V] [LE W]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W} {s : S} {t : T}
    (h : P.IsEquilibrium s) (g : J → I) (hvalid : Q.valid t)
    (hdev : ∀ j t', Q.deviation j t t' → ∃ s', P.deviation (g j) s s' ∧
      (P.value (g j) s' ≤ P.value (g j) s → Q.value j t' ≤ Q.value j t)) :
    Q.IsEquilibrium t := h.of_deviation_comparisons g hvalid hdev

/-- The explicit comparison core needs no order instance at all. -/
example {S I T J V W : Type*}
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W} {s : S} {t : T}
    {R : I → V → V → Prop} {R' : J → W → W → Prop}
    (h : P.IsEquilibriumWith R s) (g : J → I) (hvalid : Q.valid t)
    (hdev : ∀ j t', Q.deviation j t t' → ∃ s', P.deviation (g j) s s' ∧
      (R (g j) (P.value (g j) s') (P.value (g j) s) → R' j (Q.value j t') (Q.value j t))) :
    Q.IsEquilibriumWith R' t := h.of_deviation_comparisons g hvalid hdev

end Signatures
