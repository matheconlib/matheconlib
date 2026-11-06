/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Order.Defs.LinearOrder

/-!
# Equilibrium under admissible deviations

An equilibrium problem specifies states, deviators, admissible changes, rewards, and candidate
validity. Equilibrium requires a valid incumbent whose reward weakly dominates every admissible
deviation. Deviation optimality consists of these reward inequalities alone. For a partial order,
this is stronger than absence of strict improvement: An incomparable reward also violates the
inequality. The two conditions agree for a linear order.

Validity is a condition on the incumbent candidate. Deviations are compared regardless of their
targets' validity, so an improving admissible deviation to an invalid target excludes equilibrium.

The state space and deviation relations are arbitrary: No product structure, reflexivity,
transitivity, or commutation of deviations is assumed. Equilibrium compares only the deviations
admitted directly by the supplied relation. A concept that compares endpoints of repeated moves
uses a relation closed under those moves, such as the transitive closure. Product action spaces and
other game-specific structure belong to the games that define these problems.

## Main definitions

* `EquilibriumProblem`: Admissible deviations, rewards, and candidate validity over states.
* `EquilibriumProblem.IsDeviationOptimal`: Rewards weakly dominate all admissible deviations.
* `EquilibriumProblem.IsEquilibrium`: Valid candidates satisfying deviation optimality.
* `EquilibriumProblem.ofDeviation`: An equilibrium problem with every candidate valid.
* `EquilibriumProblem.refine`: The same problem with an additional condition on candidates.
* `GameMorphism`: Reward-preserving maps that lift target deviations and preserve validity.
* `GameComorphism`: Reward-preserving maps that send source deviations to target deviations and
  reflect validity.

## Main statements

* `EquilibriumProblem.IsDeviationOptimal.of_deviation_subset` restricts admissible deviations.
* `EquilibriumProblem.IsEquilibrium.of_deviation_subset` also preserves candidate validity.
* `EquilibriumProblem.isEquilibrium_ofDeviation_iff` characterizes unrestricted candidates.
* `EquilibriumProblem.isEquilibrium_refine_iff` characterizes additional candidate conditions.
* `GameMorphism.transport` and `GameComorphism.pullback` transport equilibrium.
* `GameMorphism.transport_isDeviationOptimal` and `GameComorphism.pullback_isDeviationOptimal`
  transport deviation optimality.

## Tags

equilibrium, deviations, game theory
-/

@[expose] public section

namespace MathEconLib.GameTheory

universe u v w x y z r

/-- States, candidate validity, admissible changes, and each deviator's reward.

Deviation relations may be arbitrary; notably the supplied relation need not commute or be
transitive. Solution concepts should therefore take care to supply the correct relation. -/
structure EquilibriumProblem (S : Type u) (I : Type v) (V : Type r) where
  /-- Whether a deviator may change the first state to the second state. -/
  deviation : I → S → S → Prop
  /-- The reward of each deviator at each state. -/
  value : I → S → V
  /-- Whether a state is an admissible equilibrium candidate. -/
  valid : S → Prop

namespace EquilibriumProblem

variable {V : Type r} {S : Type u} {I : Type v} {P Q : EquilibriumProblem S I V}

/-- Every single admissible deviation gives its deviator a reward at most the incumbent reward.

Note that, in a partial order, this excludes incomparable rewards as well as strict improvements.
Also note that states are only compared if they are reachable through a single application of the
deviation relation. The predicate checks this relation as supplied, without adding paths of
successive deviations or its transitive closure. -/
def IsDeviationOptimal [LE V] (P : EquilibriumProblem S I V) (s : S) : Prop :=
  ∀ i s', P.deviation i s s' → P.value i s' ≤ P.value i s

/-- Deviation optimality holds exactly when every admissible deviation weakly lowers the
reward. -/
@[simp] lemma isDeviationOptimal_iff [LE V] (P : EquilibriumProblem S I V) (s : S) :
    P.IsDeviationOptimal s ↔ ∀ i s', P.deviation i s s' → P.value i s' ≤ P.value i s := Iff.rfl

/-- Removing admissible deviations preserves deviation optimality when rewards agree. -/
lemma IsDeviationOptimal.of_deviation_subset [LE V] {s : S} (h : P.IsDeviationOptimal s)
    (hd : ∀ i s t, Q.deviation i s t → P.deviation i s t)
    (hv : Q.value = P.value) : Q.IsDeviationOptimal s := by
  intro i t ht
  simpa [hv] using h i t (hd i s t ht)

/-- Deviation optimality excludes strictly profitable admissible deviations. -/
lemma IsDeviationOptimal.not_lt [Preorder V] {s : S} (h : P.IsDeviationOptimal s)
    {i : I} {s' : S} (hd : P.deviation i s s') : ¬ P.value i s < P.value i s' :=
  not_lt_of_ge (h i s' hd)

/-- For linearly ordered rewards, deviation optimality is absence of strict improvement. -/
lemma isDeviationOptimal_iff_not_lt [LinearOrder V] (P : EquilibriumProblem S I V) (s : S) :
    P.IsDeviationOptimal s ↔ ∀ i s', P.deviation i s s' → ¬ P.value i s < P.value i s' := by
  simp only [isDeviationOptimal_iff, not_lt]

/-- A valid incumbent whose reward weakly dominates every admissible deviation. -/
structure IsEquilibrium [LE V] (P : EquilibriumProblem S I V) (s : S) : Prop where
  /-- The incumbent is an admissible equilibrium candidate. -/
  valid : P.valid s
  /-- Every admissible deviation weakly lowers the deviator's reward. -/
  deviation_le : P.IsDeviationOptimal s

/-- Equilibrium consists of candidate validity and deviation optimality. -/
lemma isEquilibrium_iff [LE V] (P : EquilibriumProblem S I V) (s : S) :
    P.IsEquilibrium s ↔ P.valid s ∧ P.IsDeviationOptimal s :=
  ⟨fun h ↦ ⟨h.valid, h.deviation_le⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Removing admissible deviations preserves equilibrium when rewards agree and validity is
preserved. -/
lemma IsEquilibrium.of_deviation_subset [LE V] {s : S} (h : P.IsEquilibrium s)
    (hd : ∀ i s t, Q.deviation i s t → P.deviation i s t)
    (hv : Q.value = P.value) (hvalid : ∀ s, P.valid s → Q.valid s) :
    Q.IsEquilibrium s :=
  ⟨hvalid s h.valid, h.deviation_le.of_deviation_subset hd hv⟩

/-- Equilibrium excludes strictly profitable admissible deviations. -/
lemma IsEquilibrium.not_lt [Preorder V] {s : S} (h : P.IsEquilibrium s)
    {i : I} {s' : S} (hd : P.deviation i s s') : ¬ P.value i s < P.value i s' :=
  h.deviation_le.not_lt hd

/-- An equilibrium problem in which every state is a valid candidate. -/
def ofDeviation (deviation : I → S → S → Prop) (value : I → S → V) :
    EquilibriumProblem S I V where
  deviation := deviation
  value := value
  valid _ := True

/-- Admissible deviations of a problem with unrestricted candidates. -/
@[simp] lemma ofDeviation_deviation (deviation : I → S → S → Prop) (value : I → S → V) :
    (ofDeviation deviation value).deviation = deviation := rfl

/-- Rewards of a problem with unrestricted candidates. -/
@[simp] lemma ofDeviation_value (deviation : I → S → S → Prop) (value : I → S → V) :
    (ofDeviation deviation value).value = value := rfl

/-- Every candidate of a problem constructed from deviations and rewards is valid. -/
@[simp] lemma ofDeviation_valid (deviation : I → S → S → Prop) (value : I → S → V) (s : S) :
    (ofDeviation deviation value).valid s = True := rfl

/-- For unrestricted candidates, equilibrium consists of the admissible reward inequalities. -/
@[simp] lemma isEquilibrium_ofDeviation_iff [LE V] (deviation : I → S → S → Prop)
    (value : I → S → V) (s : S) :
    (ofDeviation deviation value).IsEquilibrium s ↔
      ∀ i s', deviation i s s' → value i s' ≤ value i s := by
  rw [isEquilibrium_iff]
  simp only [ofDeviation_valid, isDeviationOptimal_iff, ofDeviation_deviation,
    ofDeviation_value, true_and]

/-- Add a condition on incumbent candidates while retaining the same deviations and rewards. -/
def refine (P : EquilibriumProblem S I V) (condition : S → Prop) :
    EquilibriumProblem S I V where
  deviation := P.deviation
  value := P.value
  valid s := P.valid s ∧ condition s

/-- Refinement preserves admissible deviations. -/
@[simp] lemma refine_deviation (P : EquilibriumProblem S I V) (condition : S → Prop) :
    (P.refine condition).deviation = P.deviation := rfl

/-- Refinement preserves rewards. -/
@[simp] lemma refine_value (P : EquilibriumProblem S I V) (condition : S → Prop) :
    (P.refine condition).value = P.value := rfl

/-- A refined candidate satisfies both the original validity and the additional condition. -/
@[simp] lemma refine_valid (P : EquilibriumProblem S I V) (condition : S → Prop) (s : S) :
    (P.refine condition).valid s ↔ P.valid s ∧ condition s := Iff.rfl

/-- A refined equilibrium is an equilibrium satisfying the additional candidate condition. -/
@[simp] lemma isEquilibrium_refine_iff [LE V] (P : EquilibriumProblem S I V)
    (condition : S → Prop) (s : S) :
    (P.refine condition).IsEquilibrium s ↔ P.IsEquilibrium s ∧ condition s := by
  constructor
  · intro h
    exact ⟨⟨h.valid.1, h.deviation_le⟩, h.valid.2⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨h.valid, hc⟩, h.deviation_le⟩

end EquilibriumProblem

/-- A reward-preserving map that preserves candidate validity and lifts every target deviation
to a source deviation. -/
structure GameMorphism {V : Type r} {S : Type u} {I : Type v} {T : Type w} {J : Type x}
    (P : EquilibriumProblem S I V) (Q : EquilibriumProblem T J V) where
  /-- The map from source states to target states. -/
  toFun : S → T
  /-- The source deviator corresponding to each target deviator. -/
  deviatorMap : J → I
  /-- Every target deviation from an image state is the image of a source deviation. -/
  deviation_lifts : ∀ j s t, Q.deviation j (toFun s) t →
    ∃ s', P.deviation (deviatorMap j) s s' ∧ toFun s' = t
  /-- Corresponding deviators receive equal rewards at corresponding states. -/
  value_eq : ∀ j s, Q.value j (toFun s) = P.value (deviatorMap j) s
  /-- Valid source candidates have valid images. -/
  valid_preserves : ∀ s, P.valid s → Q.valid (toFun s)

namespace GameMorphism

variable {V : Type r} {S : Type u} {I : Type v} {T : Type w} {J : Type x} {U : Type y} {K : Type z}
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V} {R : EquilibriumProblem U K V}

/-- A deviation-lifting map preserves deviation optimality. -/
theorem transport_isDeviationOptimal [LE V] (f : GameMorphism P Q) {s : S}
    (h : P.IsDeviationOptimal s) : Q.IsDeviationOptimal (f.toFun s) := by
  intro j t ht
  obtain ⟨s', hs', rfl⟩ := f.deviation_lifts j s t ht
  simpa only [f.value_eq] using h (f.deviatorMap j) s' hs'

/-- A deviation-lifting map sends equilibria to equilibria. -/
theorem transport [LE V] (f : GameMorphism P Q) {s : S} (h : P.IsEquilibrium s) :
    Q.IsEquilibrium (f.toFun s) :=
  ⟨f.valid_preserves s h.valid, f.transport_isDeviationOptimal h.deviation_le⟩

/-- The identity map of an equilibrium problem. -/
def id (P : EquilibriumProblem S I V) : GameMorphism P P where
  toFun := _root_.id
  deviatorMap := _root_.id
  deviation_lifts _ _ t ht := ⟨t, ht, rfl⟩
  value_eq _ _ := rfl
  valid_preserves _ h := h

/-- Composition of deviation-lifting maps. -/
def comp (g : GameMorphism Q R) (f : GameMorphism P Q) : GameMorphism P R where
  toFun := g.toFun ∘ f.toFun
  deviatorMap := f.deviatorMap ∘ g.deviatorMap
  deviation_lifts k s u hu := by
    obtain ⟨t, ht, htu⟩ := g.deviation_lifts k (f.toFun s) u hu
    obtain ⟨s', hs', hst⟩ := f.deviation_lifts (g.deviatorMap k) s t ht
    exact ⟨s', hs', by simp [hst, htu]⟩
  value_eq k s := (g.value_eq k (f.toFun s)).trans (f.value_eq (g.deviatorMap k) s)
  valid_preserves s h := g.valid_preserves (f.toFun s) (f.valid_preserves s h)

end GameMorphism

/-- A reward-preserving map that reflects candidate validity and sends each source deviation
to a target deviation. -/
structure GameComorphism {V : Type r} {S : Type u} {I : Type v} {T : Type w} {J : Type x}
    (P : EquilibriumProblem S I V) (Q : EquilibriumProblem T J V) where
  /-- The map from source states to target states. -/
  toFun : S → T
  /-- The target deviator corresponding to each source deviator. -/
  deviatorMap : I → J
  /-- Every source deviation maps to an admissible target deviation. -/
  deviation_maps : ∀ i s s', P.deviation i s s' →
    Q.deviation (deviatorMap i) (toFun s) (toFun s')
  /-- Corresponding deviators receive equal rewards at corresponding states. -/
  value_eq : ∀ i s, Q.value (deviatorMap i) (toFun s) = P.value i s
  /-- Validity of an image implies validity of its source candidate. -/
  valid_reflects : ∀ s, Q.valid (toFun s) → P.valid s

namespace GameComorphism

variable {V : Type r} {S : Type u} {I : Type v} {T : Type w} {J : Type x} {U : Type y} {K : Type z}
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V} {R : EquilibriumProblem U K V}

/-- Deviation optimality pulls back along a deviation-preserving map. -/
theorem pullback_isDeviationOptimal [LE V] (f : GameComorphism P Q) {s : S}
    (h : Q.IsDeviationOptimal (f.toFun s)) : P.IsDeviationOptimal s := by
  intro i s' hs'
  simpa only [f.value_eq] using h (f.deviatorMap i) (f.toFun s') (f.deviation_maps i s s' hs')

/-- Equilibrium pulls back along a deviation-preserving map. -/
theorem pullback [LE V] (f : GameComorphism P Q) {s : S}
    (h : Q.IsEquilibrium (f.toFun s)) : P.IsEquilibrium s :=
  ⟨f.valid_reflects s h.valid, f.pullback_isDeviationOptimal h.deviation_le⟩

/-- The identity deviation-preserving map. -/
def id (P : EquilibriumProblem S I V) : GameComorphism P P where
  toFun := _root_.id
  deviatorMap := _root_.id
  deviation_maps _ _ _ h := h
  value_eq _ _ := rfl
  valid_reflects _ h := h

/-- Composition of deviation-preserving maps. -/
def comp (g : GameComorphism Q R) (f : GameComorphism P Q) : GameComorphism P R where
  toFun := g.toFun ∘ f.toFun
  deviatorMap := g.deviatorMap ∘ f.deviatorMap
  deviation_maps i s s' h := g.deviation_maps _ _ _ (f.deviation_maps i s s' h)
  value_eq i s := (g.value_eq (f.deviatorMap i) (f.toFun s)).trans (f.value_eq i s)
  valid_reflects s h := f.valid_reflects s (g.valid_reflects (f.toFun s) h)

end GameComorphism

end MathEconLib.GameTheory
