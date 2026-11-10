/-
Copyright (c) 2026 Daniel Lyng, Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng, Bo Cowgill
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
* `EquilibriumProblem.IsOptimalWith`: One deviator's optimality under an explicit comparison.
* `EquilibriumProblem.IsDeviationOptimalWith`: All explicit deviation comparisons, without validity.
* `EquilibriumProblem.IsEquilibriumWith`: Valid candidates satisfying those explicit comparisons.
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
* `EquilibriumProblem.isEquilibriumWith_le_iff` and `isDeviationOptimalWith_le_iff` recover the
  ordered predicates, including their distinction between validity and deviation optimality.
* `EquilibriumProblem.isEquilibriumWith_iff_of_comparisons` preserves equilibrium under exact
  comparisons and matching candidate validity, without a numerical-representation assumption.
* `GameMorphism.transportWith` and `GameComorphism.pullbackWith` transport explicit-comparison
  equilibria with the same candidate-validity requirements as their ordered counterparts.

## Tags

equilibrium, deviations, game theory
-/

@[expose] public section

namespace MathEconLib.GameTheory

universe u v w x y z r r'

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

/-- Every admissible deviation by `i` is weakly worse under the supplied comparison.
`R i x y` means that player `i` weakly prefers `y` to `x`; no order axioms are assumed. -/
def IsOptimalWith (P : EquilibriumProblem S I V) (R : I → V → V → Prop)
    (i : I) (s : S) : Prop :=
  ∀ t, P.deviation i s t → R i (P.value i t) (P.value i s)

/-- Every player is deviation-optimal under its explicitly supplied comparison.
Candidate validity is separate, and no validity condition is imposed on deviation targets. -/
def IsDeviationOptimalWith (P : EquilibriumProblem S I V) (R : I → V → V → Prop)
    (s : S) : Prop :=
  ∀ i, P.IsOptimalWith R i s

/-- A valid incumbent that is deviation-optimal under the supplied comparisons. -/
structure IsEquilibriumWith (P : EquilibriumProblem S I V) (R : I → V → V → Prop)
    (s : S) : Prop where
  /-- The incumbent is an admissible equilibrium candidate. -/
  valid : P.valid s
  /-- Every admissible deviation is weakly worse for its deviator. -/
  deviation_le : P.IsDeviationOptimalWith R s

/-- Optimality compares precisely the deviations admitted by the problem. -/
@[simp] theorem isOptimalWith_iff (P : EquilibriumProblem S I V)
    (R : I → V → V → Prop) (i : I) (s : S) :
    P.IsOptimalWith R i s ↔ ∀ t, P.deviation i s t → R i (P.value i t) (P.value i s) :=
  Iff.rfl

/-- Deviation optimality compares every player's admissible deviations. -/
@[simp] theorem isDeviationOptimalWith_iff (P : EquilibriumProblem S I V)
    (R : I → V → V → Prop) (s : S) :
    P.IsDeviationOptimalWith R s ↔
      ∀ i t, P.deviation i s t → R i (P.value i t) (P.value i s) :=
  Iff.rfl

/-- Full equilibrium requires a valid incumbent as well as every deviation comparison. -/
theorem isEquilibriumWith_iff (P : EquilibriumProblem S I V)
    (R : I → V → V → Prop) (s : S) :
    P.IsEquilibriumWith R s ↔ P.valid s ∧ P.IsDeviationOptimalWith R s :=
  ⟨fun h ↦ ⟨h.valid, h.deviation_le⟩, fun h ↦ ⟨h.1, h.2⟩⟩

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

/-- The explicit order comparison recovers the existing equilibrium predicate exactly. -/
@[simp] theorem isEquilibriumWith_le_iff [LE V] (P : EquilibriumProblem S I V) (s : S) :
    P.IsEquilibriumWith (fun _ x y ↦ x ≤ y) s ↔ P.IsEquilibrium s :=
  ⟨fun h ↦ ⟨h.valid, h.deviation_le⟩, fun h ↦ ⟨h.valid, h.deviation_le⟩⟩

/-- The explicit order comparison also recovers deviation optimality without candidate validity. -/
@[simp] theorem isDeviationOptimalWith_le_iff [LE V]
    (P : EquilibriumProblem S I V) (s : S) :
    P.IsDeviationOptimalWith (fun _ x y ↦ x ≤ y) s ↔ P.IsDeviationOptimal s :=
  Iff.rfl

/-- Removing deviations preserves optimality when the evaluated consequences agree. -/
theorem IsOptimalWith.of_deviation_subset {R : I → V → V → Prop} {i : I} {s : S}
    (h : P.IsOptimalWith R i s)
    (hd : ∀ t, Q.deviation i s t → P.deviation i s t)
    (hv : Q.value = P.value) : Q.IsOptimalWith R i s :=
  fun t ht ↦ by simpa only [hv] using h t (hd t ht)

/-- Removing deviations preserves deviation optimality when evaluated consequences agree. -/
theorem IsDeviationOptimalWith.of_deviation_subset {R : I → V → V → Prop} {s : S}
    (h : P.IsDeviationOptimalWith R s)
    (hd : ∀ i s t, Q.deviation i s t → P.deviation i s t)
    (hv : Q.value = P.value) : Q.IsDeviationOptimalWith R s :=
  fun i ↦ (h i).of_deviation_subset (hd i s) hv

/-- Removing deviations preserves full equilibrium when rewards agree and validity is preserved. -/
theorem IsEquilibriumWith.of_deviation_subset {R : I → V → V → Prop} {s : S}
    (h : P.IsEquilibriumWith R s)
    (hd : ∀ i s t, Q.deviation i s t → P.deviation i s t)
    (hv : Q.value = P.value) (hvalid : ∀ s, P.valid s → Q.valid s) :
    Q.IsEquilibriumWith R s :=
  ⟨hvalid s h.valid, h.deviation_le.of_deviation_subset hd hv⟩

/-- Equivalent comparisons on the pairs actually compared preserve one player's optimality.
The consequence carriers may differ, so exact numerical representation is a specialization. -/
theorem isOptimalWith_iff_of_comparisons {W : Type r'} (P : EquilibriumProblem S I V)
    (Q : EquilibriumProblem S I W) (R : I → V → V → Prop) (R' : I → W → W → Prop)
    (i : I) (hdev : ∀ s t, P.deviation i s t ↔ Q.deviation i s t)
    (hcmp : ∀ s t, P.deviation i s t →
      (R i (P.value i t) (P.value i s) ↔ R' i (Q.value i t) (Q.value i s))) (s : S) :
    P.IsOptimalWith R i s ↔ Q.IsOptimalWith R' i s :=
  ⟨fun h t ht ↦ (hcmp s t ((hdev s t).2 ht)).1 (h t ((hdev s t).2 ht)),
    fun h t ht ↦ (hcmp s t ht).2 (h t ((hdev s t).1 ht))⟩

/-- Matching deviations and comparisons preserve deviation optimality across consequence
carriers. -/
theorem isDeviationOptimalWith_iff_of_comparisons {W : Type r'}
    (P : EquilibriumProblem S I V) (Q : EquilibriumProblem S I W)
    (R : I → V → V → Prop) (R' : I → W → W → Prop)
    (hdev : ∀ i s t, P.deviation i s t ↔ Q.deviation i s t)
    (hcmp : ∀ i s t, P.deviation i s t →
      (R i (P.value i t) (P.value i s) ↔ R' i (Q.value i t) (Q.value i s))) (s : S) :
    P.IsDeviationOptimalWith R s ↔ Q.IsDeviationOptimalWith R' s :=
  ⟨fun h i ↦ (P.isOptimalWith_iff_of_comparisons Q R R' i (hdev i) (hcmp i) s).1 (h i),
    fun h i ↦ (P.isOptimalWith_iff_of_comparisons Q R R' i (hdev i) (hcmp i) s).2 (h i)⟩

/-- Exact representation preserves full equilibrium when candidate validity also agrees. -/
theorem isEquilibriumWith_iff_of_comparisons {W : Type r'}
    (P : EquilibriumProblem S I V) (Q : EquilibriumProblem S I W)
    (R : I → V → V → Prop) (R' : I → W → W → Prop)
    (hdev : ∀ i s t, P.deviation i s t ↔ Q.deviation i s t)
    (hcmp : ∀ i s t, P.deviation i s t →
      (R i (P.value i t) (P.value i s) ↔ R' i (Q.value i t) (Q.value i s)))
    (hvalid : ∀ s, P.valid s ↔ Q.valid s) (s : S) :
    P.IsEquilibriumWith R s ↔ Q.IsEquilibriumWith R' s := by
  rw [isEquilibriumWith_iff, isEquilibriumWith_iff, hvalid s,
    P.isDeviationOptimalWith_iff_of_comparisons Q R R' hdev hcmp s]

/-- Weak optimality excludes a deviation strictly preferred in the asymmetric part of `R`. -/
theorem IsOptimalWith.not_strictImprovement {R : I → V → V → Prop} {i : I} {s t : S}
    (h : P.IsOptimalWith R i s) (hd : P.deviation i s t) :
    ¬ (R i (P.value i s) (P.value i t) ∧ ¬ R i (P.value i t) (P.value i s)) :=
  fun hstrict ↦ hstrict.2 (h t hd)

/-- Deviation optimality excludes every strictly preferred admissible deviation. -/
theorem IsDeviationOptimalWith.not_strictImprovement {R : I → V → V → Prop} {s t : S}
    (h : P.IsDeviationOptimalWith R s) {i : I} (hd : P.deviation i s t) :
    ¬ (R i (P.value i s) (P.value i t) ∧ ¬ R i (P.value i t) (P.value i s)) :=
  (h i).not_strictImprovement hd

/-- Full equilibrium excludes every strictly preferred admissible deviation. -/
theorem IsEquilibriumWith.not_strictImprovement {R : I → V → V → Prop} {s t : S}
    (h : P.IsEquilibriumWith R s) {i : I} (hd : P.deviation i s t) :
    ¬ (R i (P.value i s) (P.value i t) ∧ ¬ R i (P.value i t) (P.value i s)) :=
  h.deviation_le.not_strictImprovement hd

/-- The converse needs comparability only between the incumbent and its admissible deviations. -/
theorem isOptimalWith_iff_no_strictImprovement (P : EquilibriumProblem S I V)
    (R : I → V → V → Prop) (i : I) (s : S)
    (hcmp : ∀ t, P.deviation i s t →
      R i (P.value i t) (P.value i s) ∨ R i (P.value i s) (P.value i t)) :
    P.IsOptimalWith R i s ↔ ∀ t, P.deviation i s t →
      ¬ (R i (P.value i s) (P.value i t) ∧ ¬ R i (P.value i t) (P.value i s)) :=
  ⟨fun h _ ht ↦ h.not_strictImprovement ht,
    fun h t ht ↦ (hcmp t ht).elim (fun hle ↦ hle)
      (fun hrev ↦ Classical.byContradiction fun hnot ↦ h t ht ⟨hrev, hnot⟩)⟩

/-- Comparability on admissible pairs makes deviation optimality equivalent to no strict gain. -/
theorem isDeviationOptimalWith_iff_no_strictImprovement (P : EquilibriumProblem S I V)
    (R : I → V → V → Prop) (s : S)
    (hcmp : ∀ i t, P.deviation i s t →
      R i (P.value i t) (P.value i s) ∨ R i (P.value i s) (P.value i t)) :
    P.IsDeviationOptimalWith R s ↔ ∀ i t, P.deviation i s t →
      ¬ (R i (P.value i s) (P.value i t) ∧ ¬ R i (P.value i t) (P.value i s)) :=
  ⟨fun h _ _ ht ↦ h.not_strictImprovement ht,
    fun h i ↦ (P.isOptimalWith_iff_no_strictImprovement R i s (hcmp i)).2 (h i)⟩

/-- Under comparability, full equilibrium is candidate validity and absence of strict gain. -/
theorem isEquilibriumWith_iff_no_strictImprovement (P : EquilibriumProblem S I V)
    (R : I → V → V → Prop) (s : S)
    (hcmp : ∀ i t, P.deviation i s t →
      R i (P.value i t) (P.value i s) ∨ R i (P.value i s) (P.value i t)) :
    P.IsEquilibriumWith R s ↔ P.valid s ∧ ∀ i t, P.deviation i s t →
      ¬ (R i (P.value i s) (P.value i t) ∧ ¬ R i (P.value i t) (P.value i s)) := by
  rw [isEquilibriumWith_iff, isDeviationOptimalWith_iff_no_strictImprovement P R s hcmp]

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

/-- A deviation-lifting map transports deviation optimality when comparisons on admissible pairs
are preserved. The existing reward-preserving morphism is reused without an order instance. -/
theorem transport_isDeviationOptimalWith (f : GameMorphism P Q) (C : I → V → V → Prop)
    (D : J → V → V → Prop)
    (hcmp : ∀ j s t, P.deviation (f.deviatorMap j) s t →
      C (f.deviatorMap j) (P.value (f.deviatorMap j) t) (P.value (f.deviatorMap j) s) →
      D j (P.value (f.deviatorMap j) t) (P.value (f.deviatorMap j) s))
    {s : S} (h : P.IsDeviationOptimalWith C s) :
    Q.IsDeviationOptimalWith D (f.toFun s) := by
  intro j t ht
  obtain ⟨s', hs', rfl⟩ := f.deviation_lifts j s t ht
  simpa only [f.value_eq] using hcmp j s s' hs' (h (f.deviatorMap j) s' hs')

/-- A deviation-lifting map transports full equilibrium, including candidate validity. -/
theorem transportWith (f : GameMorphism P Q) (C : I → V → V → Prop)
    (D : J → V → V → Prop)
    (hcmp : ∀ j s t, P.deviation (f.deviatorMap j) s t →
      C (f.deviatorMap j) (P.value (f.deviatorMap j) t) (P.value (f.deviatorMap j) s) →
      D j (P.value (f.deviatorMap j) t) (P.value (f.deviatorMap j) s))
    {s : S} (h : P.IsEquilibriumWith C s) : Q.IsEquilibriumWith D (f.toFun s) :=
  ⟨f.valid_preserves s h.valid, f.transport_isDeviationOptimalWith C D hcmp h.deviation_le⟩

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

/-- A deviation-preserving map pulls deviation optimality back when target comparisons imply
the source comparisons on admissible pairs. No complete-preference assumption is needed. -/
theorem pullback_isDeviationOptimalWith (f : GameComorphism P Q) (C : I → V → V → Prop)
    (D : J → V → V → Prop)
    (hcmp : ∀ i s t, P.deviation i s t →
      D (f.deviatorMap i) (P.value i t) (P.value i s) → C i (P.value i t) (P.value i s))
    {s : S} (h : Q.IsDeviationOptimalWith D (f.toFun s)) : P.IsDeviationOptimalWith C s := by
  intro i t ht
  apply hcmp i s t ht
  simpa only [f.value_eq] using h (f.deviatorMap i) (f.toFun t) (f.deviation_maps i s t ht)

/-- A deviation-preserving map pulls full equilibrium back, including reflected validity. -/
theorem pullbackWith (f : GameComorphism P Q) (C : I → V → V → Prop)
    (D : J → V → V → Prop)
    (hcmp : ∀ i s t, P.deviation i s t →
      D (f.deviatorMap i) (P.value i t) (P.value i s) → C i (P.value i t) (P.value i s))
    {s : S} (h : Q.IsEquilibriumWith D (f.toFun s)) : P.IsEquilibriumWith C s :=
  ⟨f.valid_reflects s h.valid, f.pullback_isDeviationOptimalWith C D hcmp h.deviation_le⟩

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
