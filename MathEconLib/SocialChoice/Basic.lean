/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.SocialChoice.Defs
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Aggregating preferences: basic properties

Linear profiles, supporters, and independence of irrelevant alternatives on linear profiles.

## Main statements

* `le_iff_lt_of_mem_linearProfiles`: on a linear profile, weak and strict preference agree on
  distinct alternatives.
* `reindexAgents_mem_linearProfiles`, `comap_mem_linearProfiles`: reindexing the agents and
  relabelling the alternatives injectively preserve linear profiles.
* `exists_mem_linearProfiles_lt_of_lt`: every family of ranks has a linear profile.
* `card_supporters_add_card_supporters`: on a linear profile, for `x ≠ y`, supporters of `x` and
  of `y` partition the agents.
* `IsIIAOn.le_iff_of_lt_iff`: on linear profiles, IIA implies Osborne and Rubinstein's form.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Sections 20.2–20.3
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preferences

universe u v w

variable {N : Type u} {X : Type v} {F : SocialWelfareFunction N X}
  {D : Set (Profile N fun _ => X)} {P Q : Profile N fun _ => X} {x y : X}

/-- On a linear profile, weak preference between distinct alternatives is strict preference. -/
theorem le_iff_lt_of_mem_linearProfiles (hP : P ∈ linearProfiles N X) (hxy : x ≠ y) (i : N) :
    x ≼[P i] y ↔ x ≺[P i] y := by
  have := hP i
  rw [(P i).le_iff_eq_or_lt]
  exact or_iff_right hxy

theorem lt_iff_not_lt_of_mem_linearProfiles (hP : P ∈ linearProfiles N X) (hxy : x ≠ y) (i : N) :
    x ≺[P i] y ↔ ¬ y ≺[P i] x := by
  rw [← le_iff_lt_of_mem_linearProfiles hP hxy, (P i).not_lt]

theorem lt_or_gt_of_mem_linearProfiles (hP : P ∈ linearProfiles N X) (hxy : x ≠ y) (i : N) :
    y ≺[P i] x ∨ x ≺[P i] y := by
  have := hP i
  exact ((P i).lt_or_gt_of_ne hxy).symm

theorem reindexAgents_mem_linearProfiles {M : Type w} (hP : P ∈ linearProfiles N X) (g : M → N) :
    P.reindexAgents g ∈ linearProfiles M X :=
  fun j => hP (g j)

theorem comap_mem_linearProfiles {Y : Type w} (hP : P ∈ linearProfiles N X) {f : Y → X}
    (hf : Function.Injective f) : (P.comap fun _ => f) ∈ linearProfiles N Y := fun i => by
  have := hP i
  exact (P i).toPreference.antisymm_comap hf

/-- Two linear preferences with the same strict preferences are equal. -/
theorem eq_of_mem_linearProfiles_of_lt_iff (hP : P ∈ linearProfiles N X)
    (hQ : Q ∈ linearProfiles N X) {i j : N} (h : ∀ a b : X, a ≺[P i] b ↔ a ≺[Q j] b) :
    P i = Q j := by
  ext a b
  by_cases hab : a = b
  · subst hab
    exact ⟨fun _ => (Q j).le_refl a, fun _ => (P i).le_refl a⟩
  · rw [le_iff_lt_of_mem_linearProfiles hP hab, h a b,
      ← le_iff_lt_of_mem_linearProfiles hQ hab]

/-- With injective utilities into a linear order, the profile they define is linear. -/
theorem ofUtility_mem_linearProfiles {U : Type w} [LinearOrder U] {r : N → X → U}
    (hr : ∀ i, Function.Injective (r i)) :
    (Profile.ofUtility r : Profile N fun _ => X) ∈ linearProfiles N X := fun i =>
  ⟨fun a b hab hba => hr i (le_antisymm ((Preference.ofUtility_le_iff (r i) a b).1 hab)
    ((Preference.ofUtility_le_iff (r i) b a).1 hba))⟩

/-- Some linear profile has `b ≺[P i] a` whenever `r i b < r i a`. -/
theorem exists_mem_linearProfiles_lt_of_lt (r : N → X → ℕ) :
    ∃ P ∈ linearProfiles N X, ∀ i a b, r i b < r i a → b ≺[P i] a := by
  classical
  let _ : LinearOrder X := linearOrderOfSTO WellOrderingRel
  let w : N → X → ℕ ×ₗ X := fun i z => toLex (r i z, z)
  have hw : ∀ i, Function.Injective (w i) := fun i a b h =>
    congrArg Prod.snd (toLex.injective h)
  refine ⟨Profile.ofUtility w, ofUtility_mem_linearProfiles hw, fun i a b h => ?_⟩
  exact (Preference.ofUtility_lt_iff (w i) b a).2 (Prod.Lex.toLex_lt_toLex.2 (Or.inl h))

section Supporters

variable [Fintype N]

theorem supporters_comap {Y : Type w} (f : Y → X) (P : Profile N fun _ => X) (x y : Y) :
    supporters (P.comap fun _ => f) x y = supporters P (f x) (f y) := by
  ext i
  simp only [mem_supporters]
  exact Iff.rfl

theorem card_supporters_reindexAgents (σ : N ≃ N) (P : Profile N fun _ => X) (x y : X) :
    (supporters (P.reindexAgents σ) x y).card = (supporters P x y).card :=
  Finset.card_equiv σ fun i => by simp only [mem_supporters, Profile.reindexAgents_apply]

theorem disjoint_supporters (P : Profile N fun _ => X) (x y : X) :
    Disjoint (supporters P x y) (supporters P y x) :=
  Finset.disjoint_left.2 fun i h₁ h₂ =>
    (P i).lt_asymm (mem_supporters.1 h₁) (mem_supporters.1 h₂)

theorem supporters_union_supporters [DecidableEq N] (hP : P ∈ linearProfiles N X) (hxy : x ≠ y) :
    supporters P x y ∪ supporters P y x = Finset.univ :=
  Finset.eq_univ_of_forall fun i =>
    (lt_or_gt_of_mem_linearProfiles hP hxy i).elim
      (fun h => Finset.mem_union_left _ (mem_supporters.2 h))
      (fun h => Finset.mem_union_right _ (mem_supporters.2 h))

theorem card_supporters_add_card_supporters (hP : P ∈ linearProfiles N X) (hxy : x ≠ y) :
    (supporters P x y).card + (supporters P y x).card = Fintype.card N := by
  classical
  rw [← Finset.card_union_of_disjoint (disjoint_supporters P x y),
    supporters_union_supporters hP hxy, Finset.card_univ]

/-- If exactly the members of `S` prefer `x` to `y`, the supporters of `x` against `y` are `S`. -/
theorem supporters_eq_of_forall {S : Finset N} (h₁ : ∀ i ∈ S, y ≺[P i] x)
    (h₂ : ∀ i ∉ S, x ≺[P i] y) : supporters P x y = S := by
  ext i
  rw [mem_supporters]
  by_cases hi : i ∈ S
  · exact ⟨fun _ => hi, fun _ => h₁ i hi⟩
  · exact ⟨fun h => ((P i).lt_asymm (h₂ i hi) h).elim, fun h => (hi h).elim⟩

end Supporters

/-- On linear profiles, IIA implies Osborne and Rubinstein's form (Definition 20.7), which compares
only the strict preferences of `x` over `y`. -/
theorem IsIIAOn.le_iff_of_lt_iff (hF : IsIIAOn F D) (hD : D ⊆ linearProfiles N X)
    (hP : P ∈ D) (hQ : Q ∈ D) (hxy : x ≠ y) (h : ∀ i, y ≺[P i] x ↔ y ≺[Q i] x) :
    y ≼[F P] x ↔ y ≼[F Q] x :=
  hF hP hQ x y fun i => ⟨by
    rw [le_iff_lt_of_mem_linearProfiles (hD hP) (Ne.symm hxy),
      le_iff_lt_of_mem_linearProfiles (hD hQ) (Ne.symm hxy), h i], by
    rw [← (P i).not_lt, ← (Q i).not_lt, h i]⟩

/-- The same, for society's strict preference of `x` over `y`. -/
theorem IsIIAOn.lt_iff_of_lt_iff (hF : IsIIAOn F D) (hD : D ⊆ linearProfiles N X)
    (hP : P ∈ D) (hQ : Q ∈ D) (hxy : x ≠ y) (h : ∀ i, y ≺[P i] x ↔ y ≺[Q i] x) :
    y ≺[F P] x ↔ y ≺[F Q] x := by
  have h' : ∀ i, x ≺[P i] y ↔ x ≺[Q i] y := fun i => by
    rw [lt_iff_not_lt_of_mem_linearProfiles (hD hP) hxy,
      lt_iff_not_lt_of_mem_linearProfiles (hD hQ) hxy, h i]
  exact and_congr (hF.le_iff_of_lt_iff hD hP hQ hxy h)
    (not_congr (hF.le_iff_of_lt_iff hD hP hQ (Ne.symm hxy) h'))

end MathEconLib.SocialChoice

section Examples

open MathEconLib.Preferences MathEconLib.SocialChoice

example : (Profile.ofUtility fun (i : Fin 2) (b : Bool) => if (i = 0) = b then 1 else 0 :
    Profile (Fin 2) fun _ => Bool) ∈ linearProfiles (Fin 2) Bool :=
  ofUtility_mem_linearProfiles (by decide)

/-- A profile with an indifference is not linear. -/
example : (fun _ => CompletePreference.ofUtility fun _ : Bool => (0 : ℕ) :
    Profile (Fin 1) fun _ => Bool) ∉ linearProfiles (Fin 1) Bool := fun h =>
  absurd ((h 0).antisymm true false ((Preference.ofUtility_le_iff _ _ _).2 le_rfl)
    ((Preference.ofUtility_le_iff _ _ _).2 le_rfl)) (by decide)

/-- A constant rule (Osborne and Rubinstein's Example 20.4) ignores the profile. -/
example (R : CompletePreference Bool) (P : Profile (Fin 2) fun _ => Bool) :
    (Function.const _ R : SocialWelfareFunction (Fin 2) Bool) P = R :=
  rfl

end Examples
