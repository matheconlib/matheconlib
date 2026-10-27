/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Continuum.Basic
public import MathEconLib.Matching.PartnerComparisons
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Pointwise and distributional stability

Utilities represent ordinal preferences over partners and an outside option. Blocking requires
strict improvement for both agents, so indifference alone does not block. Pointwise stability
of a matching map checks every agent and pair. Distributional stability requires individual
rationality almost everywhere and no blocking for almost every ordered pair of assigned couples,
under the product of the matching measure with itself. Even every agent having a blocking partner
can be consistent with this product-almost-everywhere condition: a graph of blocking pairs may
have product measure zero. Deleting null sets of agents need not remove all blocking pairs.
`MathEconLibTest/Matching/Continuum/Antipodal.lean` verifies this stronger distinction.

The definition follows the product-measure criterion in Greinecker and Kah (2021), Section 2,
https://doi.org/10.3982/ECTA16228, extended here to measurable utility data and explicit outside
options. Their topological preference assumptions are additional hypotheses; see the source
comparison in `docs/MatchingArchitecture.md`. No existence, approximation or individual-agent
realization theorem is asserted in this layer.
-/

@[expose] public section

namespace MathEconLib.Matching.Continuum

open MeasureTheory

variable {A B : Type*}

/-- Partner utilities and outside-option utilities for the two populations. -/
structure PartnerUtilities (A B : Type*) where
  /-- Left agent's utility from a partner on the right. -/
  left : A → B → ℝ
  /-- Right agent's utility from a partner on the left. -/
  right : B → A → ℝ
  /-- Left agent's utility from remaining unmatched. -/
  outsideLeft : A → ℝ
  /-- Right agent's utility from remaining unmatched. -/
  outsideRight : B → ℝ

namespace PartnerUtilities

/-- Relabel preferences when exchanging the populations: `left := u.right`, `right := u.left`,
`outsideLeft := u.outsideRight`, and `outsideRight := u.outsideLeft`. Together with matching
inversion, this lets the symmetry theorems express preservation of stability. -/
def symm (u : PartnerUtilities A B) : PartnerUtilities B A :=
  ⟨u.right, u.left, u.outsideRight, u.outsideLeft⟩

@[simp] theorem symm_symm (u : PartnerUtilities A B) : u.symm.symm = u := rfl

/-- Utilities induce strict comparisons over partners and the outside option. -/
def toPartnerComparisons (u : PartnerUtilities A B) : PartnerComparisons A B where
  left a x y := x.elim (u.outsideLeft a) (u.left a) < y.elim (u.outsideLeft a) (u.left a)
  right b x y := x.elim (u.outsideRight b) (u.right b) < y.elim (u.outsideRight b) (u.right b)

@[simp] theorem toPartnerComparisons_symm (u : PartnerUtilities A B) :
    u.symm.toPartnerComparisons = u.toPartnerComparisons.symm := rfl

/-- Utility comparisons give strict improvements, including comparisons with the outside option. -/
@[simp] theorem toPartnerComparisons_blocks (u : PartnerUtilities A B) (a : A) (b : B)
    (currentLeft : Option B) (currentRight : Option A) :
    u.toPartnerComparisons.Blocks a b currentLeft currentRight ↔
      currentLeft.elim (u.outsideLeft a) (u.left a) < u.left a b ∧
      currentRight.elim (u.outsideRight b) (u.right b) < u.right b a := Iff.rfl

/-- Both agents in an assigned pair weakly prefer their partner to their outside option. -/
def IndividuallyRationalPair (u : PartnerUtilities A B) (p : A × B) : Prop :=
  u.outsideLeft p.1 ≤ u.left p.1 p.2 ∧ u.outsideRight p.2 ≤ u.right p.2 p.1

/-- The left agent in `p` and the right agent in `q` both strictly prefer matching to each other. -/
def Blocks (u : PartnerUtilities A B) (p q : A × B) : Prop :=
  u.toPartnerComparisons.Blocks p.1 q.2 (some p.2) (some q.1)

@[simp] theorem individuallyRationalPair_symm (u : PartnerUtilities A B) (p : A × B) :
    u.symm.IndividuallyRationalPair p.swap ↔ u.IndividuallyRationalPair p := by
  simp [IndividuallyRationalPair, symm, and_comm]

@[simp] theorem blocks_symm (u : PartnerUtilities A B) (p q : A × B) :
    u.symm.Blocks p.swap q.swap ↔ u.Blocks q p := by
  simpa only [Blocks, toPartnerComparisons_symm, Prod.swap] using
    u.toPartnerComparisons.blocks_symm q.1 p.2 (some q.2) (some p.1)

variable [MeasurableSpace A] [MeasurableSpace B]

/-- Joint measurability of partner utilities and measurability of outside-option utilities. -/
structure IsMeasurable (u : PartnerUtilities A B) : Prop where
  left : Measurable (Function.uncurry u.left)
  right : Measurable (Function.uncurry u.right)
  outsideLeft : Measurable u.outsideLeft
  outsideRight : Measurable u.outsideRight

theorem IsMeasurable.symm {u : PartnerUtilities A B} (h : u.IsMeasurable) : u.symm.IsMeasurable :=
  ⟨h.right, h.left, h.outsideRight, h.outsideLeft⟩

/-- The set of individually rational assigned pairs is measurable. -/
theorem IsMeasurable.measurableSet_individuallyRationalPair {u : PartnerUtilities A B}
    (h : u.IsMeasurable) : MeasurableSet {p | u.IndividuallyRationalPair p} :=
  (measurableSet_le (h.outsideLeft.comp measurable_fst) h.left).inter
    (measurableSet_le (h.outsideRight.comp measurable_snd) (h.right.comp measurable_swap))

/-- Measurable partner utilities suffice for measurable blocking; outside options do not enter. -/
theorem measurableSet_blocks {u : PartnerUtilities A B}
    (hleft : Measurable (Function.uncurry u.left))
    (hright : Measurable (Function.uncurry u.right)) :
    MeasurableSet {z : (A × B) × (A × B) | u.Blocks z.1 z.2} :=
  (measurableSet_lt (hleft.comp measurable_fst)
    (hleft.comp (measurable_fst.fst.prodMk measurable_snd.snd))).inter
    (measurableSet_lt (hright.comp (measurable_snd.snd.prodMk measurable_snd.fst))
      (hright.comp (measurable_snd.snd.prodMk measurable_fst.fst)))

/-- The set of ordered couple pairs witnessing a blocking pair is measurable. -/
theorem IsMeasurable.measurableSet_blocks {u : PartnerUtilities A B} (h : u.IsMeasurable) :
    MeasurableSet {z : (A × B) × (A × B) | u.Blocks z.1 z.2} :=
  PartnerUtilities.measurableSet_blocks h.left h.right

end PartnerUtilities

variable [MeasurableSpace A] [MeasurableSpace B]
variable {μ : ProbabilityMeasure A} {ν : ProbabilityMeasure B}

namespace MatchingMap

/-- All assigned agents weakly prefer their partner to remaining unmatched, including null types. -/
def IndividuallyRational (f : MatchingMap μ ν) (u : PartnerUtilities A B) : Prop :=
  ∀ a, u.IndividuallyRationalPair (f.graphMap a)

/-- Agents `a` and `b` both strictly prefer each other to their assigned partners. -/
def IsBlockingPair (f : MatchingMap μ ν) (u : PartnerUtilities A B) (a : A) (b : B) : Prop :=
  u.toPartnerComparisons.Blocks a b (some (f a)) (some (f.symm b))

/-- Blocking is exactly strict improvement for both agents over their assigned partners. -/
theorem isBlockingPair_iff (f : MatchingMap μ ν) (u : PartnerUtilities A B) (a : A) (b : B) :
    f.IsBlockingPair u a b ↔
      u.left a (f a) < u.left a b ∧ u.right b (f.symm b) < u.right b a := Iff.rfl

/-- No pair of agents blocks the matching, even if either agent has zero population mass. -/
def Unblocked (f : MatchingMap μ ν) (u : PartnerUtilities A B) : Prop :=
  ∀ a b, ¬f.IsBlockingPair u a b

/-- Individual rationality and no blocking pair, checked pointwise for every agent. -/
def PointwiseStable (f : MatchingMap μ ν) (u : PartnerUtilities A B) : Prop :=
  f.IndividuallyRational u ∧ f.Unblocked u

/-- Couple-based blocking agrees with blocking by the corresponding individual agents. -/
@[simp] theorem blocks_graphMap (f : MatchingMap μ ν) (u : PartnerUtilities A B) (a a' : A) :
    u.Blocks (f.graphMap a) (f.graphMap a') ↔ f.IsBlockingPair u a (f a') := by
  simp [PartnerUtilities.Blocks, IsBlockingPair, graphMap]

end MatchingMap

namespace MatchingMeasure

/-- Individually rational assignments for almost every assigned pair. -/
def IndividuallyRational (γ : MatchingMeasure μ ν) (u : PartnerUtilities A B) : Prop :=
  ∀ᵐ p ∂γ.toMeasure, u.IndividuallyRationalPair p

/-- Almost no ordered pair of assigned couples contains a blocking cross-pair, under `γ × γ`.
This quantifies over pairs almost everywhere; it need not give full-measure populations on
which every cross-pair is unblocked. -/
def Unblocked (γ : MatchingMeasure μ ν) (u : PartnerUtilities A B) : Prop :=
  ∀ᵐ z ∂γ.toMeasure.prod γ.toMeasure, ¬u.Blocks z.1 z.2

/-- Individual rationality almost everywhere and absence of blocking under `γ × γ`.
This may hold even if every agent has a blocking partner and blocking persists after deleting
arbitrary population-null sets; see the antipodal regression example. -/
def DistributionallyStable (γ : MatchingMeasure μ ν) (u : PartnerUtilities A B) : Prop :=
  γ.IndividuallyRational u ∧ γ.Unblocked u

/-- Exchanging the populations preserves distributional stability. -/
theorem DistributionallyStable.symm {γ : MatchingMeasure μ ν} {u : PartnerUtilities A B}
    (hγ : γ.DistributionallyStable u) : γ.symm.DistributionallyStable u.symm := by
  have hswap : MeasurePreserving Prod.swap γ.symm.toMeasure γ.toMeasure :=
    ⟨measurable_swap, by simp [Measure.map_map measurable_swap measurable_swap]⟩
  constructor
  · exact (hswap.quasiMeasurePreserving.ae hγ.1).mono fun p hp ↦ by
      simpa [PartnerUtilities.IndividuallyRationalPair, PartnerUtilities.symm, and_comm] using hp
  · exact ((hswap.prod hswap).quasiMeasurePreserving.ae
      ((Measure.measurePreserving_swap (μ := γ.toMeasure)
        (ν := γ.toMeasure)).quasiMeasurePreserving.ae hγ.2)).mono fun z hz ↦ by
      simpa [PartnerUtilities.Blocks, PartnerUtilities.symm, and_comm] using hz

end MatchingMeasure

namespace MatchingMap

/-- Pointwise individual rationality passes to the graph measure. -/
theorem IndividuallyRational.toMatchingMeasure {f : MatchingMap μ ν} {u : PartnerUtilities A B}
    (hf : f.IndividuallyRational u) (hu : u.IsMeasurable) :
    f.toMatchingMeasure.IndividuallyRational u :=
  (ae_map_iff f.measurable_graphMap.aemeasurable hu.measurableSet_individuallyRationalPair).mpr
    (Filter.Eventually.of_forall hf)

/-- No blocking passes to the graph measure when partner utilities are measurable. -/
theorem Unblocked.toMatchingMeasure_of_measurable {f : MatchingMap μ ν} {u : PartnerUtilities A B}
    (hf : f.Unblocked u) (hleft : Measurable (Function.uncurry u.left))
    (hright : Measurable (Function.uncurry u.right)) : f.toMatchingMeasure.Unblocked u := by
  change ∀ᵐ z ∂(μ.toMeasure.map f.graphMap).prod (μ.toMeasure.map f.graphMap), ¬u.Blocks z.1 z.2
  rw [Measure.map_prod_map _ _ f.measurable_graphMap f.measurable_graphMap]
  exact (ae_map_iff (f.measurable_graphMap.prodMap f.measurable_graphMap).aemeasurable
    (PartnerUtilities.measurableSet_blocks hleft hright).compl).mpr
    (Filter.Eventually.of_forall fun z ↦ by simpa using hf z.1 (f z.2))

/-- Absence of every blocking pair implies absence of blocking almost everywhere. -/
theorem Unblocked.toMatchingMeasure {f : MatchingMap μ ν} {u : PartnerUtilities A B}
    (hf : f.Unblocked u) (hu : u.IsMeasurable) : f.toMatchingMeasure.Unblocked u :=
  hf.toMatchingMeasure_of_measurable hu.left hu.right

/-- A pointwise-stable matching map induces a distributionally stable matching measure.
Measurable utility data make the individual-rationality and blocking events measurable. -/
theorem PointwiseStable.toMatchingMeasure {f : MatchingMap μ ν} {u : PartnerUtilities A B}
    (hf : f.PointwiseStable u) (hu : u.IsMeasurable) :
    f.toMatchingMeasure.DistributionallyStable u :=
  ⟨hf.1.toMatchingMeasure hu, hf.2.toMatchingMeasure hu⟩

/-- Exchanging the populations preserves pointwise stability. -/
theorem PointwiseStable.symm {f : MatchingMap μ ν} {u : PartnerUtilities A B}
    (hf : f.PointwiseStable u) : f.symm.PointwiseStable u.symm := by
  constructor
  · intro b
    simpa [graphMap, PartnerUtilities.IndividuallyRationalPair, PartnerUtilities.symm,
      and_comm] using hf.1 (f.symm b)
  · intro b a h
    exact hf.2 a b (by simpa [IsBlockingPair, PartnerUtilities.symm, and_comm] using h)

end MatchingMap

end MathEconLib.Matching.Continuum
