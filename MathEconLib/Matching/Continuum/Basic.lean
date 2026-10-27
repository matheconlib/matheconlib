/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Balanced two-sided matching: maps and measures

The two populations are probability measures, so each has total mass 1. A `MatchingMeasure`
records the joint distribution of matched pairs with those population marginals. A `MatchingMap`
is a measure-preserving measurable bijection. Its graph map induces a matching measure. A matching
measure describes the distribution of matched types and may split one type's mass among partners.
It need not be induced by a bijection between the given population spaces; realizing a general
matching measure using individual agents requires separate agent spaces and type maps.

These definitions allow both atomless populations and atoms; no finiteness assumptions are used.
Everyone is matched in this first layer. Outside options enter the stability definitions, while
partial matchings and unequal population masses are separate extensions.

Left and right are neutral names for the two populations (`A` and `B`). They assign neither a
proposing role nor a buyer/seller role. Applications and proposal algorithms specify those roles
separately. This convention applies equally to atomic and atomless populations.

## Reference

Michael Greinecker and Christopher Kah (2021), *Pairwise Stable Matching in Large Economies*,
Econometrica 89(6), 2929–2974. https://doi.org/10.3982/ECTA16228, Section 2.
This layer covers balanced matching objects and elementary representation lemmas, not the
existence, approximation or individual-agent representation theorems.
-/

@[expose] public section

namespace MathEconLib.Matching.Continuum

open MeasureTheory

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {μ : ProbabilityMeasure A} {ν : ProbabilityMeasure B}

/-- A joint distribution of matched pairs with the specified population marginals. -/
@[ext] structure MatchingMeasure (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure B) where
  /-- The distribution of assigned pairs. -/
  toProbabilityMeasure : ProbabilityMeasure (A × B)
  /-- The left population is accounted for exactly. -/
  fst_eq : toProbabilityMeasure.toMeasure.fst = μ.toMeasure
  /-- The right population is accounted for exactly. -/
  snd_eq : toProbabilityMeasure.toMeasure.snd = ν.toMeasure

namespace MatchingMeasure

/-- The underlying measure, for use with Mathlib's measure API. -/
abbrev toMeasure (γ : MatchingMeasure μ ν) : Measure (A × B) :=
  γ.toProbabilityMeasure.toMeasure

/-- Matching measures are determined by their underlying measures. -/
theorem ext_toMeasure {γ δ : MatchingMeasure μ ν} (h : γ.toMeasure = δ.toMeasure) : γ = δ :=
  MatchingMeasure.ext (ProbabilityMeasure.toMeasure_injective h)

/-- Exchange the population coordinates. -/
noncomputable def symm (γ : MatchingMeasure μ ν) : MatchingMeasure ν μ where
  toProbabilityMeasure := γ.toProbabilityMeasure.map Prod.swap
  fst_eq := by simpa using γ.snd_eq
  snd_eq := by simpa using γ.fst_eq

@[simp] theorem toMeasure_symm (γ : MatchingMeasure μ ν) :
    γ.symm.toMeasure = γ.toMeasure.map Prod.swap := rfl

@[simp] theorem symm_symm (γ : MatchingMeasure μ ν) : γ.symm.symm = γ :=
  ext_toMeasure (by simp [Measure.map_map measurable_swap measurable_swap])

/-- The mass assigned to a measurable group on the left equals its population mass. -/
theorem measure_left (γ : MatchingMeasure μ ν) {s : Set A} (hs : MeasurableSet s) :
    γ.toMeasure (Prod.fst ⁻¹' s) = μ.toMeasure s := by
  rw [← Measure.fst_apply hs, γ.fst_eq]

/-- The same accounting identity for the right population. -/
theorem measure_right (γ : MatchingMeasure μ ν) {s : Set B} (hs : MeasurableSet s) :
    γ.toMeasure (Prod.snd ⁻¹' s) = ν.toMeasure s := by
  rw [← Measure.snd_apply hs, γ.snd_eq]

/-- Package Mathlib's product measure and marginal identities as a feasible matching measure.
This optional construction assigns independent population types. It supplies one feasible
matching (used by the split-mass example); stability requires a separate proof. -/
noncomputable def product (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure B) :
    MatchingMeasure μ ν where
  toProbabilityMeasure := ⟨μ.toMeasure.prod ν.toMeasure, inferInstance⟩
  fst_eq := Measure.fst_prod
  snd_eq := Measure.snd_prod

/-- Exchanging the populations swaps the product matching measure. -/
@[simp] theorem product_symm (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure B) :
    (product μ ν).symm = product ν μ := ext_toMeasure Measure.prod_swap

end MatchingMeasure

/-- A one-to-one matching of the population spaces that preserves population mass. -/
@[ext] structure MatchingMap (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure B) where
  /-- Every agent has exactly one partner, with measurable assignment in both directions. -/
  toMeasurableEquiv : A ≃ᵐ B
  /-- Assigned partners have the specified right-population distribution. -/
  measurePreserving : MeasurePreserving toMeasurableEquiv μ.toMeasure ν.toMeasure

namespace MatchingMap

instance : CoeFun (MatchingMap μ ν) (fun _ ↦ A → B) := ⟨fun f ↦ f.toMeasurableEquiv⟩

/-- The matching assignment is measurable. -/
@[fun_prop] theorem measurable (f : MatchingMap μ ν) : Measurable f :=
  f.toMeasurableEquiv.measurable

/-- Exchange the two populations and invert the assignment. -/
def symm (f : MatchingMap μ ν) : MatchingMap ν μ where
  toMeasurableEquiv := f.toMeasurableEquiv.symm
  measurePreserving := f.measurePreserving.symm f.toMeasurableEquiv

@[simp] theorem symm_apply_apply (f : MatchingMap μ ν) (a : A) : f.symm (f a) = a :=
  f.toMeasurableEquiv.symm_apply_apply a

@[simp] theorem apply_symm_apply (f : MatchingMap μ ν) (b : B) : f (f.symm b) = b :=
  f.toMeasurableEquiv.apply_symm_apply b

@[simp] theorem symm_symm (f : MatchingMap μ ν) : f.symm.symm = f := rfl

/-- Match each member of a population to the same point in a copy of that population. -/
def refl (μ : ProbabilityMeasure A) : MatchingMap μ μ where
  toMeasurableEquiv := MeasurableEquiv.refl A
  measurePreserving := MeasurePreserving.id μ.toMeasure

@[simp] theorem refl_apply (μ : ProbabilityMeasure A) (a : A) : refl μ a = a := rfl

/-- The graph map `a ↦ (a, f a)` records each agent together with their assigned partner.
`toMatchingMeasure` pushes the left population forward along this map. -/
def graphMap (f : MatchingMap μ ν) (a : A) : A × B := (a, f a)

@[fun_prop] theorem measurable_graphMap (f : MatchingMap μ ν) : Measurable f.graphMap :=
  measurable_id.prodMk f.measurable

/-- The joint distribution of assigned pairs under the left-population measure. -/
noncomputable def toMatchingMeasure (f : MatchingMap μ ν) : MatchingMeasure μ ν where
  toProbabilityMeasure := μ.map f.graphMap
  fst_eq := (Measure.fst_map_prodMk (μ := μ.toMeasure) (X := id) (Y := f)
    measurable_id f.measurable).trans Measure.map_id
  snd_eq := (Measure.snd_map_prodMk (μ := μ.toMeasure) (X := id) (Y := f)
    measurable_id f.measurable).trans f.measurePreserving.map_eq

@[simp] theorem toMeasure_toMatchingMeasure (f : MatchingMap μ ν) :
    f.toMatchingMeasure.toMeasure = μ.toMeasure.map f.graphMap := rfl

/-- Inverting a matching map swaps the coordinates of its induced matching measure. -/
@[simp] theorem toMatchingMeasure_symm (f : MatchingMap μ ν) :
    f.symm.toMatchingMeasure = f.toMatchingMeasure.symm :=
  MatchingMeasure.ext_toMeasure <| calc
    _ = (μ.toMeasure.map f).map f.symm.graphMap :=
      congrArg (Measure.map f.symm.graphMap) f.measurePreserving.map_eq.symm
    _ = μ.toMeasure.map (fun a ↦ (f a, a)) := by
      simp [Measure.map_map f.symm.measurable_graphMap f.measurable, graphMap, Function.comp_def]
    _ = _ := by
      simp [Measure.map_map measurable_swap f.measurable_graphMap, graphMap, Function.comp_def]

/-- Changing assignments on a population-null set does not change the matching measure. -/
theorem toMatchingMeasure_congr {f g : MatchingMap μ ν} (h : f =ᵐ[μ.toMeasure] g) :
    f.toMatchingMeasure = g.toMatchingMeasure :=
  MatchingMeasure.ext_toMeasure (Measure.map_congr (h.mono fun _ ha ↦ Prod.ext rfl ha))

end MatchingMap
end MathEconLib.Matching.Continuum
