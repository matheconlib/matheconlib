/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Continuum

/-! API pins through the public continuum umbrella only. -/

@[expose] public section

namespace MathEconLibTest.Matching.Continuum.Compatibility

open MeasureTheory
open MathEconLib.Matching
open MathEconLib.Matching.Continuum
open MathEconLib.Preferences

section Generic

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {μ : ProbabilityMeasure A} {ν : ProbabilityMeasure B}

example (γ : MatchingMeasure μ ν) : γ.toMeasure.fst = μ.toMeasure := γ.fst_eq
example (γ : MatchingMeasure μ ν) : γ.toMeasure.snd = ν.toMeasure := γ.snd_eq
example (γ : MatchingMeasure μ ν) : IsProbabilityMeasure γ.toMeasure := inferInstance

example (γ : MatchingMeasure μ ν) : γ.symm.symm = γ := γ.symm_symm

example (f : MatchingMap μ ν) (a : A) : f.graphMap a = (a, f a) := rfl

example (f : MatchingMap μ ν) : Measurable f.graphMap := f.measurable_graphMap

example (u : PartnerUtilities A B) :
    u.symm.left = u.right ∧ u.symm.right = u.left ∧
      u.symm.outsideLeft = u.outsideRight ∧ u.symm.outsideRight = u.outsideLeft :=
  ⟨rfl, rfl, rfl, rfl⟩

example : (MatchingMeasure.product μ ν).symm = MatchingMeasure.product ν μ :=
  MatchingMeasure.product_symm μ ν

example (f : MatchingMap μ ν) : f.toMatchingMeasure.toMeasure.fst = μ.toMeasure :=
  f.toMatchingMeasure.fst_eq

example (f : MatchingMap μ ν) : f.toMatchingMeasure.toMeasure.snd = ν.toMeasure :=
  f.toMatchingMeasure.snd_eq

example (f : MatchingMap μ ν) : f.symm.toMatchingMeasure = f.toMatchingMeasure.symm :=
  f.toMatchingMeasure_symm

example (f : MatchingMap μ ν) (u : PartnerUtilities A B) (hu : u.IsMeasurable)
    (hf : f.PointwiseStable u) : f.toMatchingMeasure.DistributionallyStable u :=
  hf.toMatchingMeasure hu

example (γ : MatchingMeasure μ ν) (u : PartnerUtilities A B)
    (hγ : γ.DistributionallyStable u) : γ.symm.DistributionallyStable u.symm := hγ.symm

-- Indifference is not a strict blocking improvement.
example (γ : MatchingMeasure μ ν) : γ.DistributionallyStable
    ⟨fun _ _ ↦ 0, fun _ _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0⟩ := by
  simp [MatchingMeasure.DistributionallyStable, MatchingMeasure.IndividuallyRational,
    MatchingMeasure.Unblocked, PartnerUtilities.IndividuallyRationalPair, PartnerUtilities.Blocks]

example (f : MatchingMap μ ν) (u : PartnerUtilities A B) (hu : u.IsMeasurable)
    (hf : f.Unblocked u) : f.toMatchingMeasure.Unblocked u := hf.toMatchingMeasure hu

example (f : MatchingMap μ ν) (u : PartnerUtilities A B) (hf : f.Unblocked u)
    (hleft : Measurable (Function.uncurry u.left))
    (hright : Measurable (Function.uncurry u.right)) : f.toMatchingMeasure.Unblocked u :=
  hf.toMatchingMeasure_of_measurable hleft hright

example (f : MatchingMap μ ν) (u : PartnerUtilities A B)
    (mkt : MathEconLib.Matching.MarriageMarket A B)
    (hpref : mkt.toPartnerComparisons = u.toPartnerComparisons) :
    f.PointwiseStable u ↔ mkt.IsStableMatching f.toMeasurableEquiv.toEquiv.toPEquiv :=
  f.pointwiseStable_iff_classical u mkt hpref

-- Classical blocking retains its original conjunction, definitionally.
example (mkt : MathEconLib.Matching.MarriageMarket A B) (f : A ≃. B) (a : A) (b : B) :
    mkt.IsBlockingPair f a b ↔ mkt.BlocksM f a b ∧ mkt.BlocksW f b a := Iff.rfl

-- Both utility interfaces also retain their original strict inequalities.
example (u : PartnerUtilities A B) (p q : A × B) :
    u.Blocks p q ↔ u.left p.1 p.2 < u.left p.1 q.2 ∧
      u.right q.2 q.1 < u.right q.2 p.1 := by
  simp [PartnerUtilities.Blocks]

example (f : MatchingMap μ ν) (u : PartnerUtilities A B) (a : A) (b : B) :
    f.IsBlockingPair u a b ↔ u.left a (f a) < u.left a b ∧
      u.right b (f.symm b) < u.right b a := f.isBlockingPair_iff u a b

-- Outside options are represented at none, in both comparison directions and on both sides.
example (u : PartnerUtilities A B) (a : A) (b : B) :
    u.toPartnerComparisons.left a none (some b) ↔ u.outsideLeft a < u.left a b := by simp

example (u : PartnerUtilities A B) (a : A) (b : B) :
    u.toPartnerComparisons.left a (some b) none ↔ u.left a b < u.outsideLeft a := by simp

example (u : PartnerUtilities A B) (a : A) (b : B) :
    u.toPartnerComparisons.right b none (some a) ↔ u.outsideRight b < u.right b a := by simp

example (u : PartnerUtilities A B) (a : A) (b : B) :
    u.toPartnerComparisons.right b (some a) none ↔ u.right b a < u.outsideRight b := by simp

example (u : PartnerUtilities A B) (a : A) (b : B) :
    ¬u.toPartnerComparisons.left a none none ∧
      ¬u.toPartnerComparisons.right b none none := by simp

-- Equal utilities never create strict improvement, including ties with the outside option.
example (u : PartnerUtilities A B) (a : A) (x y : Option B)
    (h : x.elim (u.outsideLeft a) (u.left a) = y.elim (u.outsideLeft a) (u.left a)) :
    ¬u.toPartnerComparisons.left a x y ∧ ¬u.toPartnerComparisons.left a y x := by simp [h]

example (u : PartnerUtilities A B) (b : B) (x y : Option A)
    (h : x.elim (u.outsideRight b) (u.right b) = y.elim (u.outsideRight b) (u.right b)) :
    ¬u.toPartnerComparisons.right b x y ∧ ¬u.toPartnerComparisons.right b y x := by simp [h]

-- Outside-option functions may be arbitrary; blocking never consults them.
example (outsideLeft : A → ℝ) (outsideRight : B → ℝ) (f : MatchingMap μ ν) :
    f.toMatchingMeasure.Unblocked ⟨fun _ _ ↦ 0, fun _ _ ↦ 0, outsideLeft, outsideRight⟩ :=
  MatchingMap.Unblocked.toMatchingMeasure_of_measurable
    (by intro a b; simp [MatchingMap.IsBlockingPair]) measurable_const measurable_const

end Generic

section PreferenceAdapter

variable {A B : Type*}

-- The preference bridge needs no population measures, completeness, or utility representation.
example (left : A → Preference (Option B)) (right : B → Preference (Option A))
    (a : A) (b : B) (x : Option B) (y : Option A) :
    (PartnerComparisons.ofPreferences left right).Blocks a b x y ↔
      (left a).lt x (some b) ∧ (right b).lt y (some a) := Iff.rfl

example (left : A → Preference (Option B)) (right : B → Preference (Option A)) :
    (PartnerComparisons.ofPreferences left right).symm =
      PartnerComparisons.ofPreferences right left :=
  PartnerComparisons.ofPreferences_symm left right

-- A concrete incomplete preference also passes through the adapter without completing it.
example : ∃ R : Preference (Option Bool),
    ¬R.le none (some false) ∧ ¬R.le (some false) none ∧
      let p := PartnerComparisons.ofPreferences (fun _ : Bool ↦ R) (fun _ : Bool ↦ R)
      ¬p.left false none (some false) ∧ ¬p.right false (some false) none := by
  let R : Preference (Option Bool) :=
    { le := Eq, isPreorder :=
        { refl := fun _ ↦ rfl, trans := fun _ _ _ hxy hyz ↦ hxy.trans hyz } }
  exact ⟨R, by simp [R, Preference.lt]⟩

end PreferenceAdapter

#print axioms PartnerComparisons.ofPreferences
#print axioms PartnerUtilities.toPartnerComparisons_left
#print axioms PartnerUtilities.toPartnerComparisons_right
#print axioms MatchingMap.pointwiseStable_iff_classical
#print axioms MatchingMap.Unblocked.toMatchingMeasure_of_measurable

end MathEconLibTest.Matching.Continuum.Compatibility
