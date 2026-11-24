/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Problem
public import Mathlib.Order.Hom.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Equilibrium transport by deviation domination

A simulation bounds every target deviation by an admissible source deviation,
measured through a monotone value map for each target deviator. Source and target
values may live in different preorders. The translated incumbent may have a larger
value than its recoding. Exact reward-preserving morphisms use identity value maps.

The record is for maps that are composed or reused. A one-off transport at a single incumbent
needs no record: use `EquilibriumProblem.IsEquilibrium.of_deviation_comparisons`, or
`EquilibriumProblem.IsDeviationOptimal.of_dominated_deviations` for a domination bound.
Additive errors require a separate compatibility bound for the value maps;
monotonicity alone does not preserve a numerical error. Reflection requires
an independent contract; preservation alone does not imply it.

## Main definitions

* `GameSimulation`: A validity-preserving state translation whose target deviations are each
  dominated by an admissible source deviation after a monotone value recoding.
* `GameSimulation.id` and `GameSimulation.comp`: Identity and composition.
* `GameSimulation.ofExactLifts`: Simulations from exact deviation lifts and value recodings.
* `GameMorphism.toSimulation`: Reward-preserving morphisms as simulations.

## Main statements

* `EquilibriumProblem.IsDeviationOptimal.of_dominated_deviations`: Pointwise domination
  transports optimality at one incumbent.
* `GameSimulation.transport`: Simulations send equilibria to equilibria.
* `GameSimulation.transport_le_add`: Additive deviation errors transport under a compatible
  bound on the value maps. Chains apply it once per simulation, not to the composite.
* `GameSimulation.isEquilibrium_iff_of_deviation_comparisons` and
  `GameSimulation.isEquilibrium_iff`: Reflection conditions giving an iff.

## Tags

equilibrium, simulation, deviations, game theory
-/

@[expose] public section

namespace MathEconLib.GameTheory

universe u v w x y z r

/-- A state translation preserving validity and bounding each target deviation
by a source deviation after a playerwise monotone change of value coordinates. -/
structure GameSimulation {V W : Type*} [Preorder V] [Preorder W] {S : Type u} {I : Type v}
    {T : Type w} {J : Type x}
    (P : EquilibriumProblem S I V) (Q : EquilibriumProblem T J W) where
  /-- Translate source candidates into target candidates. -/
  toFun : S → T
  /-- The source deviator representing each target deviator. -/
  deviatorMap : J → I
  /-- Recoding source values into each target deviator's value coordinates. -/
  valueMap : J → V →o W
  /-- Translation weakly increases the recoded incumbent value. -/
  incumbent_value_le : ∀ j s, valueMap j (P.value (deviatorMap j) s) ≤ Q.value j (toFun s)
  /-- Every target deviation is bounded by one admissible source deviation. -/
  deviation_dominated : ∀ j s t, Q.deviation j (toFun s) t →
    ∃ s', P.deviation (deviatorMap j) s s' ∧
      Q.value j t ≤ valueMap j (P.value (deviatorMap j) s')
  /-- Valid source candidates have valid images. -/
  valid_preserves : ∀ s, P.valid s → Q.valid (toFun s)

namespace EquilibriumProblem

variable {V W : Type*} [Preorder V] [Preorder W] {S : Type u} {I : Type v}
    {T : Type w} {J : Type x} {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}

/-- Pointwise domination transports optimality without requiring a bundled map
or any hypothesis about candidates other than the one under consideration. -/
theorem IsDeviationOptimal.of_dominated_deviations {s : S} {t : T}
    (h : P.IsDeviationOptimal s) (g : J → I) (φ : J → V →o W)
    (hbase : ∀ j, φ j (P.value (g j) s) ≤ Q.value j t)
    (hdev : ∀ j t', Q.deviation j t t' →
      ∃ s', P.deviation (g j) s s' ∧ Q.value j t' ≤ φ j (P.value (g j) s')) :
    Q.IsDeviationOptimal t := by
  apply h.of_deviation_comparisons g
  intro j t' ht'
  obtain ⟨s', hs', hbound⟩ := hdev j t' ht'
  exact ⟨s', hs', fun hle ↦ hbound.trans (((φ j).monotone hle).trans (hbase j))⟩

end EquilibriumProblem

namespace GameSimulation

section Extensionality

variable {V W : Type*} [Preorder V] [Preorder W] {S : Type u} {I : Type v}
    {T : Type w} {J : Type x} {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}

/-- Certificates with the same state, deviator, and value maps are equal by proof irrelevance. -/
@[ext] theorem ext {f g : GameSimulation P Q} (hf : f.toFun = g.toFun)
    (hg : f.deviatorMap = g.deviatorMap) (hv : f.valueMap = g.valueMap) : f = g := by
  cases f
  cases g
  cases hf
  cases hg
  cases hv
  rfl

end Extensionality

variable {V W X : Type*} [Preorder V] [Preorder W] [Preorder X] {S : Type u} {I : Type v}
    {T : Type w} {J : Type x} {U : Type y} {K : Type z}
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    {R : EquilibriumProblem U K X}

/-- Domination transports deviation optimality without a validity assumption. -/
theorem transport_isDeviationOptimal (f : GameSimulation P Q) {s : S}
    (h : P.IsDeviationOptimal s) : Q.IsDeviationOptimal (f.toFun s) :=
  h.of_dominated_deviations f.deviatorMap f.valueMap (fun j ↦ f.incumbent_value_le j s)
    (fun j t ↦ f.deviation_dominated j s t)

/-- A simulation sends equilibria to equilibria. -/
theorem transport (f : GameSimulation P Q) {s : S} (h : P.IsEquilibrium s) :
    Q.IsEquilibrium (f.toFun s) :=
  ⟨f.valid_preserves s h.valid, f.transport_isDeviationOptimal h.deviation_le⟩

/-- The identity simulation. -/
def id (P : EquilibriumProblem S I V) : GameSimulation P P where
  toFun := _root_.id
  deviatorMap := _root_.id
  valueMap _ := OrderHom.id
  incumbent_value_le _ _ := le_rfl
  deviation_dominated _ _ t ht := ⟨t, ht, le_rfl⟩
  valid_preserves _ h := h

/-- Simulations compose by composing maps and chaining the deviation bounds.

The local error premises of `transport_le_add` do not compose. The second simulation's premise is
evaluated at the translated incumbent, which may lie strictly above the recoded source incumbent
where the composite's premise is evaluated, so the two step premises need not imply the composite
one. To chain approximate equilibria from the step premises, apply `transport_le_add` to each
simulation in turn. -/
def comp (g : GameSimulation Q R) (f : GameSimulation P Q) : GameSimulation P R where
  toFun := g.toFun ∘ f.toFun
  deviatorMap := f.deviatorMap ∘ g.deviatorMap
  valueMap k := (g.valueMap k).comp (f.valueMap (g.deviatorMap k))
  incumbent_value_le k s :=
    ((g.valueMap k).monotone (f.incumbent_value_le (g.deviatorMap k) s)).trans
      (g.incumbent_value_le k (f.toFun s))
  deviation_dominated k s t ht := by
    obtain ⟨q, hq, hb⟩ := g.deviation_dominated k (f.toFun s) t ht
    obtain ⟨p, hp, hc⟩ := f.deviation_dominated (g.deviatorMap k) s q hq
    exact ⟨p, hp, hb.trans ((g.valueMap k).monotone hc)⟩
  valid_preserves s hs := g.valid_preserves (f.toFun s) (f.valid_preserves s hs)

@[simp] theorem id_comp (f : GameSimulation P Q) : (id Q).comp f = f := by
  ext <;> rfl

@[simp] theorem comp_id (f : GameSimulation P Q) : f.comp (id P) = f := by
  ext <;> rfl

theorem comp_assoc {A B Y : Type*} [Preorder Y] {Z : EquilibriumProblem A B Y}
    (h : GameSimulation R Z) (g : GameSimulation Q R) (f : GameSimulation P Q) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext <;> rfl

/-- Transport playerwise additive errors. If no deviation from `s` gains more than `ε`, validity
aside, then no deviation from its image gains more than `δ`, provided each value map turns an
`ε` gain at the recoded source incumbent into at most a `δ` gain (`herror`). An affine map with
slope `a` satisfies this with `δ = a • ε`; identity maps with `δ = ε`.

`herror` is evaluated at the recoded source incumbent, not at the translated incumbent. For a chain
of simulations, apply this theorem once per step, so each step's bound is evaluated at that step's
own incumbent; see `comp`. -/
theorem transport_le_add [Add V] [Add W] [AddRightMono W]
    (f : GameSimulation P Q) (ε : I → V) (δ : J → W) {s : S}
    (herror : ∀ j, f.valueMap j (P.value (f.deviatorMap j) s + ε (f.deviatorMap j)) ≤
      f.valueMap j (P.value (f.deviatorMap j) s) + δ j)
    (h : ∀ i s', P.deviation i s s' → P.value i s' ≤ P.value i s + ε i) :
    ∀ j t, Q.deviation j (f.toFun s) t → Q.value j t ≤ Q.value j (f.toFun s) + δ j := by
  intro j t ht
  obtain ⟨s', hs', hbound⟩ := f.deviation_dominated j s t ht
  exact hbound.trans (((f.valueMap j).monotone (h (f.deviatorMap j) s' hs')).trans
    ((herror j).trans (add_le_add_left (f.incumbent_value_le j s) (δ j))))

/-- Exact deviation lifts give a simulation after any monotone value recoding. -/
def ofExactLifts (f : S → T) (g : J → I) (φ : J → V →o W)
    (hvalue : ∀ j s, Q.value j (f s) = φ j (P.value (g j) s))
    (hlift : ∀ j s t, Q.deviation j (f s) t →
      ∃ s', P.deviation (g j) s s' ∧ f s' = t)
    (hvalid : ∀ s, P.valid s → Q.valid (f s)) : GameSimulation P Q where
  toFun := f
  deviatorMap := g
  valueMap := φ
  incumbent_value_le j s := (hvalue j s).symm.le
  deviation_dominated j s t ht := by
    obtain ⟨s', hs', rfl⟩ := hlift j s t ht
    exact ⟨s', hs', (hvalue j s').le⟩
  valid_preserves := hvalid

/-- A simulation gives an iff at an incumbent if validity and source deviation comparisons
reflect there. This allows different value spaces and requires no numerical value equality. -/
theorem isEquilibrium_iff_of_deviation_comparisons (f : GameSimulation P Q) {s : S}
    (g : I → J) (hvalid : Q.valid (f.toFun s) → P.valid s)
    (hdev : ∀ i s', P.deviation i s s' →
      ∃ t, Q.deviation (g i) (f.toFun s) t ∧
        (Q.value (g i) t ≤ Q.value (g i) (f.toFun s) → P.value i s' ≤ P.value i s)) :
    Q.IsEquilibrium (f.toFun s) ↔ P.IsEquilibrium s :=
  ⟨fun h ↦ h.of_deviation_comparisons g (hvalid h.valid) hdev, f.transport⟩

/-- A comorphism with the same state map supplies the converse, giving an iff. -/
theorem isEquilibrium_iff {Q : EquilibriumProblem T J V}
    (f : GameSimulation P Q) (g : GameComorphism P Q)
    (hmap : g.toFun = f.toFun) (s : S) :
    Q.IsEquilibrium (f.toFun s) ↔ P.IsEquilibrium s :=
  ⟨fun h ↦ g.pullback (hmap ▸ h), f.transport⟩

end GameSimulation

namespace GameMorphism

variable {V : Type r} [Preorder V] {S : Type u} {I : Type v}
    {T : Type w} {J : Type x} {U : Type y} {K : Type z}
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}
    {R : EquilibriumProblem U K V}

/-- Exact deviation lifting is a special case of deviation domination. -/
def toSimulation (f : GameMorphism P Q) : GameSimulation P Q :=
  .ofExactLifts f.toFun f.deviatorMap (fun _ ↦ OrderHom.id)
    f.value_eq f.deviation_lifts f.valid_preserves

@[simp] theorem toSimulation_id (P : EquilibriumProblem S I V) :
    (id P).toSimulation = GameSimulation.id P := by
  ext <;> rfl

@[simp] theorem toSimulation_comp (g : GameMorphism Q R) (f : GameMorphism P Q) :
    (g.comp f).toSimulation = g.toSimulation.comp f.toSimulation := by
  ext <;> rfl

end GameMorphism

end MathEconLib.GameTheory
