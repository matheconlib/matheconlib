/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

import MathEconLib.Welfare

/-! # Public contracts for ordinal Pareto efficiency -/

-- This module contains only anonymous checks.
set_option linter.privateModule false

namespace MathEconLib.Welfare.Tests

open Preferences

variable {I J X Y : Type*} (R : I → Preference X) (F : Set X) (x y : X)

example : (unanimousPreference R).le x y ↔ ∀ i, (R i).le x y :=
  unanimousPreference_le_iff R x y

example : ParetoImprovement R x y ↔ (∀ i, (R i).le x y) ∧ ∃ i, (R i).lt x y :=
  Iff.rfl

example : (unanimousPreference R).lt x y ↔ ParetoImprovement R x y :=
  unanimousPreference_lt_iff R x y

example : IsParetoEfficient R F x ↔
    (letI := (unanimousPreference R).toPreorder; Maximal (· ∈ F) x) :=
  isParetoEfficient_iff_maximal R F x

example : IsWeaklyParetoEfficient R F x ↔ x ∈ F ∧ ∀ y ∈ F, ¬ ∀ i, (R i).lt x y :=
  isWeaklyParetoEfficient_iff R F x

example [Nonempty I] (hx : IsParetoEfficient R F x) : IsWeaklyParetoEfficient R F x :=
  hx.isWeaklyParetoEfficient

example [IsEmpty I] :
    (IsParetoEfficient R F x ↔ x ∈ F) ∧ ¬ IsWeaklyParetoEfficient R F x :=
  ⟨isParetoEfficient_iff_mem_of_isEmpty R F x, not_isWeaklyParetoEfficient_of_isEmpty R F x⟩

example (hx : x ∉ F) : ¬ IsParetoEfficient R F x ∧ ¬ IsWeaklyParetoEfficient R F x :=
  ⟨fun h ↦ hx h.1, fun h ↦ hx h.1⟩

example : ¬ IsParetoEfficient R ∅ x ∧ ¬ IsWeaklyParetoEfficient R ∅ x :=
  ⟨fun h ↦ h.1, fun h ↦ h.1⟩

section Representation

variable {V : I → Type*} [∀ i, Preorder (V i)] (u : (i : I) → X → V i)
    (hu : ∀ i, (R i).IsRepresentedBy (u i))

example : (unanimousPreference R).IsRepresentedBy (fun z i ↦ u i z) :=
  isRepresentedBy_unanimousPreference hu

example : ParetoImprovement R x y ↔ (fun i ↦ u i x) < (fun i ↦ u i y) :=
  paretoImprovement_iff_lt hu

example : UnanimousStrictImprovement R x y ↔ ∀ i, u i x < u i y :=
  unanimousStrictImprovement_iff_strongLT hu

example : IsParetoEfficient R F x ↔ MaximalFor (· ∈ F) (fun z i ↦ u i z) x :=
  isParetoEfficient_iff_maximalFor hu

end Representation

-- Each agent may change to a different utility scale. Equality transports both efficiency tests.
example {U V : I → Type*} [∀ i, LinearOrder (U i)] [∀ i, Preorder (V i)]
    (u : (i : I) → X → U i) (g : (i : I) → U i → V i) (hg : ∀ i, StrictMono (g i)) :
    (fun i ↦ Preference.ofUtility (u i)) = fun i ↦ Preference.ofUtility (g i ∘ u i) :=
  funext fun i ↦ (Preference.isRepresentedBy_iff_eq_ofUtility _ _).1
    ((Preference.isRepresentedBy_ofUtility (u i)).comp_strictMono (hg i))

-- Relabel both the agents and the outcomes, keeping every feasible alternative available.
example (a : J ≃ I) (e : Y ≃ X) (z : Y) :
    IsParetoEfficient (fun j ↦ (R (a j)).comap e) (e ⁻¹' F) z ↔ IsParetoEfficient R F (e z) :=
  (isParetoEfficient_reindex_iff (fun i ↦ (R i).comap e) a.surjective).trans
    (isParetoEfficient_comap_iff R e (fun w _ ↦ e.surjective w))

example (a : J ≃ I) (e : Y ≃ X) (z : Y) :
    IsWeaklyParetoEfficient (fun j ↦ (R (a j)).comap e) (e ⁻¹' F) z ↔
      IsWeaklyParetoEfficient R F (e z) :=
  (isWeaklyParetoEfficient_reindex_iff (fun i ↦ (R i).comap e) a.surjective).trans
    (isWeaklyParetoEfficient_comap_iff R e (fun w _ ↦ e.surjective w))

example (z : F) :
    IsParetoEfficient (fun i ↦ (R i).comap Subtype.val) Set.univ z ↔ IsParetoEfficient R F ↑z :=
  isParetoEfficient_subtype_iff R F z

example (z : F) :
    IsWeaklyParetoEfficient (fun i ↦ (R i).comap Subtype.val) Set.univ z ↔
      IsWeaklyParetoEfficient R F ↑z :=
  isWeaklyParetoEfficient_subtype_iff R F z

end MathEconLib.Welfare.Tests
