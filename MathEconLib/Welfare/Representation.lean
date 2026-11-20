/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Preferences.Representation.Basic
public import MathEconLib.Welfare.Pareto

/-!
# Utility representations of Pareto comparisons

Use `isParetoEfficient_iff_maximalFor` to compare feasible outcomes by their utility profiles.
For weak efficiency, the relevant improvement is strict in every coordinate. Each agent may use a
different preordered utility scale.
-/

@[expose] public section

namespace MathEconLib.Welfare

open Preferences

variable {I X : Type*} {V : I → Type*} [∀ i, Preorder (V i)]
    {R : I → Preference X} {u : (i : I) → X → V i} {F : Set X} {x y : X}

/-- The utility profile represents unanimous weak preference in the pointwise order. -/
theorem isRepresentedBy_unanimousPreference (hu : ∀ i, (R i).IsRepresentedBy (u i)) :
    (unanimousPreference R).IsRepresentedBy (fun z i ↦ u i z) :=
  fun a b ↦ forall_congr' fun i ↦ hu i a b

/-- A Pareto improvement strictly increases the utility profile in the product order. -/
theorem paretoImprovement_iff_lt (hu : ∀ i, (R i).IsRepresentedBy (u i)) :
    ParetoImprovement R x y ↔ (fun i ↦ u i x) < (fun i ↦ u i y) :=
  (unanimousPreference_lt_iff R x y).symm.trans (isRepresentedBy_unanimousPreference hu).lt_iff_lt

/-- A unanimous strict improvement strictly increases each agent's utility. -/
theorem unanimousStrictImprovement_iff_strongLT (hu : ∀ i, (R i).IsRepresentedBy (u i)) :
    UnanimousStrictImprovement R x y ↔ StrongLT (fun i ↦ u i x) (fun i ↦ u i y) :=
  forall_congr' fun i ↦ (hu i).lt_iff_lt

/-- A feasible outcome is Pareto efficient exactly when its utility profile is maximal. -/
theorem isParetoEfficient_iff_maximalFor (hu : ∀ i, (R i).IsRepresentedBy (u i)) :
    IsParetoEfficient R F x ↔ MaximalFor (· ∈ F) (fun z i ↦ u i z) x := by
  rw [isParetoEfficient_iff_maximal, (Preference.isRepresentedBy_iff_toPreorder_eq_lift ..).mp
    (isRepresentedBy_unanimousPreference hu)]
  rfl

/-- Weak efficiency rules out feasible outcomes with a strict gain in every utility. -/
theorem isWeaklyParetoEfficient_iff_forall_not_strongLT (hu : ∀ i, (R i).IsRepresentedBy (u i)) :
    IsWeaklyParetoEfficient R F x ↔
      x ∈ F ∧ ∀ y ∈ F, ¬ StrongLT (fun i ↦ u i x) (fun i ↦ u i y) :=
  and_congr_right' (forall₂_congr fun _ _ ↦ (unanimousStrictImprovement_iff_strongLT hu).not)

end MathEconLib.Welfare
