/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.SocialChoice.Defs
public import MathEconLib.Preferences.Relation
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Aggregating preferences: basic properties

Linear profiles, supporters, and independence of irrelevant alternatives on linear profiles.

## Main statements

* `card_supporters_add_card_supporters`: on a linear profile, for `x ≠ y`, supporters of `x` and
  of `y` partition the agents.
* `exists_mem_linearProfiles_strictPart_of_lt`: every family of ranks has a linear profile.
* `IsIIAOn.iff_of_strictPart_iff`: on linear profiles, IIA implies Osborne and Rubinstein's form.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Sections 20.2–20.3
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preferences

universe u v

variable {N : Type u} {X : Type v} {F G : SocialWelfareFunction N X} {D D' : Set (Profile N X)}
  {P Q : Profile N X} {x y : X}

theorem rel_iff_strictPart_of_mem_linearProfiles (hP : P ∈ linearProfiles N X) (hxy : x ≠ y)
    (i : N) : P i x y ↔ StrictPart (P i) x y := by
  rw [(hP.1 i).isComplete.rel_iff_eq_or_strictPart (hP.2 i)]
  exact or_iff_right hxy

theorem rel_iff_not_strictPart_of_mem_linearProfiles (hP : P ∈ linearProfiles N X) (i : N) :
    P i y x ↔ ¬ StrictPart (P i) x y :=
  (hP.1 i).isComplete.rel_iff_not_strictPart

theorem strictPart_iff_not_strictPart_of_mem_linearProfiles (hP : P ∈ linearProfiles N X)
    (hxy : x ≠ y) (i : N) : StrictPart (P i) y x ↔ ¬ StrictPart (P i) x y := by
  rw [← rel_iff_strictPart_of_mem_linearProfiles hP (Ne.symm hxy),
    rel_iff_not_strictPart_of_mem_linearProfiles hP]

theorem strictPart_or_strictPart_of_mem_linearProfiles (hP : P ∈ linearProfiles N X)
    (hxy : x ≠ y) (i : N) : StrictPart (P i) x y ∨ StrictPart (P i) y x :=
  (hP.1 i).isComplete.strictPart_or_strictPart (hP.2 i) hxy

theorem permuteAgents_mem_linearProfiles (hP : P ∈ linearProfiles N X) (σ : N ≃ N) :
    Profile.permuteAgents σ P ∈ linearProfiles N X :=
  ⟨hP.1.permuteAgents σ, hP.2.permuteAgents σ⟩

theorem relabel_mem_linearProfiles (hP : P ∈ linearProfiles N X) (τ : X ≃ X) :
    Profile.relabel τ P ∈ linearProfiles N X :=
  ⟨hP.1.relabel τ, hP.2.relabel τ⟩

/-- Two linear preferences with the same strict preferences are equal. -/
theorem eq_of_mem_linearProfiles_of_strictPart_iff (hP : P ∈ linearProfiles N X)
    (hQ : Q ∈ linearProfiles N X) {i j : N}
    (h : ∀ a b, StrictPart (P i) a b ↔ StrictPart (Q j) a b) : P i = Q j := by
  funext a b
  apply propext
  by_cases hab : a = b
  · subst hab
    exact ⟨fun _ => (hQ.1 j).refl a, fun _ => (hP.1 i).refl a⟩
  · rw [rel_iff_strictPart_of_mem_linearProfiles hP hab, h a b,
      ← rel_iff_strictPart_of_mem_linearProfiles hQ hab]

/-- Some linear profile has `a ≻ᵢ b` whenever `r i b < r i a`. -/
theorem exists_mem_linearProfiles_strictPart_of_lt (r : N → X → ℕ) :
    ∃ P ∈ linearProfiles N X, ∀ i a b, r i b < r i a → StrictPart (P i) a b := by
  classical
  let _ : LinearOrder X := linearOrderOfSTO WellOrderingRel
  let w : N → X → ℕ ×ₗ X := fun i z => toLex (r i z, z)
  have hw : ∀ i, Function.Injective (w i) := fun i a b h =>
    congrArg Prod.snd (toLex.injective h)
  refine ⟨Profile.ofUtilities w,
    ⟨Profile.isPreferenceRelation_ofUtilities w, Profile.isStrict_ofUtilities hw⟩,
    fun i a b h => ?_⟩
  rw [Profile.ofUtilities_apply, strictPart_utilityRel_iff]
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

section Supporters

variable [Fintype N]

theorem supporters_relabel (τ : X ≃ X) (P : Profile N X) (x y : X) :
    supporters (Profile.relabel τ P) x y = supporters P (τ.symm x) (τ.symm y) := by
  ext i
  simp only [mem_supporters, strictPart_iff, Profile.relabel_apply]

theorem card_supporters_permuteAgents (σ : N ≃ N) (P : Profile N X) (x y : X) :
    (supporters (Profile.permuteAgents σ P) x y).card = (supporters P x y).card :=
  Finset.card_equiv σ fun i => by simp only [mem_supporters, Profile.permuteAgents_apply]

theorem disjoint_supporters (P : Profile N X) (x y : X) :
    Disjoint (supporters P x y) (supporters P y x) :=
  Finset.disjoint_left.2 fun _ h₁ h₂ => (mem_supporters.1 h₁).asymm (mem_supporters.1 h₂)

theorem supporters_union_supporters [DecidableEq N] (hP : P ∈ linearProfiles N X) (hxy : x ≠ y) :
    supporters P x y ∪ supporters P y x = Finset.univ :=
  Finset.eq_univ_of_forall fun i =>
    (strictPart_or_strictPart_of_mem_linearProfiles hP hxy i).elim
      (fun h => Finset.mem_union_left _ (mem_supporters.2 h))
      (fun h => Finset.mem_union_right _ (mem_supporters.2 h))

theorem card_supporters_add_card_supporters (hP : P ∈ linearProfiles N X) (hxy : x ≠ y) :
    (supporters P x y).card + (supporters P y x).card = Fintype.card N := by
  classical
  rw [← Finset.card_union_of_disjoint (disjoint_supporters P x y),
    supporters_union_supporters hP hxy, Finset.card_univ]

/-- If exactly the members of `S` prefer `x` to `y`, the supporters of `x` against `y` are `S`. -/
theorem supporters_eq_of_forall {S : Finset N} (h₁ : ∀ i ∈ S, StrictPart (P i) x y)
    (h₂ : ∀ i ∉ S, StrictPart (P i) y x) : supporters P x y = S := by
  ext i
  rw [mem_supporters]
  by_cases hi : i ∈ S
  · exact ⟨fun _ => hi, fun _ => h₁ i hi⟩
  · exact ⟨fun h => ((h₂ i hi).asymm h).elim, fun h => (hi h).elim⟩

end Supporters

/-- On linear profiles, IIA implies Osborne and Rubinstein's form (Definition 20.7), which compares
only the strict preferences `x ≻ᵢ y`. -/
theorem IsIIAOn.iff_of_strictPart_iff (hF : IsIIAOn F D) (hD : D ⊆ linearProfiles N X)
    (hP : P ∈ D) (hQ : Q ∈ D) (hxy : x ≠ y)
    (h : ∀ i, StrictPart (P i) x y ↔ StrictPart (Q i) x y) : F P x y ↔ F Q x y :=
  hF hP hQ x y fun i => ⟨by
    rw [rel_iff_strictPart_of_mem_linearProfiles (hD hP) hxy,
      rel_iff_strictPart_of_mem_linearProfiles (hD hQ) hxy, h i], by
    rw [rel_iff_not_strictPart_of_mem_linearProfiles (hD hP),
      rel_iff_not_strictPart_of_mem_linearProfiles (hD hQ), h i]⟩

/-- The same, for the strict social preference `x ≻ y`. -/
theorem IsIIAOn.strictPart_iff_of_strictPart_iff (hF : IsIIAOn F D) (hD : D ⊆ linearProfiles N X)
    (hP : P ∈ D) (hQ : Q ∈ D) (hxy : x ≠ y)
    (h : ∀ i, StrictPart (P i) x y ↔ StrictPart (Q i) x y) :
    StrictPart (F P) x y ↔ StrictPart (F Q) x y := by
  have h' : ∀ i, StrictPart (P i) y x ↔ StrictPart (Q i) y x := fun i => by
    rw [strictPart_iff_not_strictPart_of_mem_linearProfiles (hD hP) hxy,
      strictPart_iff_not_strictPart_of_mem_linearProfiles (hD hQ) hxy, h i]
  rw [MathEconLib.Preferences.strictPart_iff, MathEconLib.Preferences.strictPart_iff,
    hF.iff_of_strictPart_iff hD hP hQ hxy h, hF.iff_of_strictPart_iff hD hP hQ (Ne.symm hxy) h']

end MathEconLib.SocialChoice

section Examples

open MathEconLib.Preferences MathEconLib.SocialChoice

example : Profile.ofUtilities (fun (i : Fin 2) (b : Bool) => if (i = 0) = b then 1 else 0)
    ∈ linearProfiles (Fin 2) Bool :=
  ⟨Profile.isPreferenceRelation_ofUtilities _, Profile.isStrict_ofUtilities (by decide)⟩

example : (fun (_ : Fin 1) (_ _ : Bool) => True) ∉ linearProfiles (Fin 1) Bool :=
  fun h => Bool.noConfusion ((h.2 0).antisymm (x := true) (y := false) trivial trivial)

/-- A constant rule (Osborne and Rubinstein's Example 20.4) ignores the profile. -/
example (R : Bool → Bool → Prop) (P : Profile (Fin 2) Bool) :
    (Function.const _ R : SocialWelfareFunction (Fin 2) Bool) P = R :=
  rfl

end Examples
