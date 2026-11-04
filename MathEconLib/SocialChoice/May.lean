/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.SocialChoice.Majority
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic

/-!
# May's theorem

With two alternatives, a rule complete at every linear profile is anonymous, neutral and
positively responsive on the linear profiles if and only if it is majority rule there.

## Main statements

* `eqOn_majority_of_isAnonymousOn_of_isNeutralOn_of_isPositivelyResponsiveOn`: **May's theorem**.
* `isAnonymousOn_and_isNeutralOn_and_isPositivelyResponsiveOn_iff_eqOn_majority`: with converse.

## Implementation notes

* The domain is the linear profiles; May's domain also allows indifference.

## References

* K. O. May, *A set of independent necessary and sufficient conditions for simple majority
  decision*, Econometrica **20** (1952), 680–684
* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Chapter 20, Problem 1
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preference

universe u v

variable {N : Type u} {X : Type v} [Fintype N] {F : SocialWelfareFunction N X} {x y : X}
  {P Q : Profile N X}

omit [Fintype N] in
/-- On two alternatives, a linear preference is determined by whether `x ≻ y`. -/
private theorem eq_of_strictPart_iff_of_two (hxy : x ≠ y) (hX : ∀ z, z = x ∨ z = y)
    (hP : P ∈ linearProfiles N X) (hQ : Q ∈ linearProfiles N X) {i j : N}
    (h : StrictPart (P i) x y ↔ StrictPart (Q j) x y) : P i = Q j := by
  apply eq_of_mem_linearProfiles_of_strictPart_iff hP hQ
  intro s t
  rcases hX s with rfl | rfl <;> rcases hX t with rfl | rfl
  · simp
  · exact h
  · rw [strictPart_iff_not_strictPart_of_mem_linearProfiles hP hxy,
      strictPart_iff_not_strictPart_of_mem_linearProfiles hQ hxy, h]
  · simp

/-- By anonymity, the social relation depends only on the number of supporters of `x`. -/
private theorem eq_of_card_supporters_eq (hxy : x ≠ y) (hX : ∀ z, z = x ∨ z = y)
    (hA : IsAnonymousOn F (linearProfiles N X)) (hP : P ∈ linearProfiles N X)
    (hQ : Q ∈ linearProfiles N X) (h : (supporters P x y).card = (supporters Q x y).card) :
    F P = F Q := by
  classical
  let S := supporters Q x y
  let T := supporters P x y
  let e : {i // i ∈ S} ≃ {i // i ∈ T} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe]; exact h.symm)
  let f : {i // i ∉ S} ≃ {i // i ∉ T} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe,
        Fintype.card_coe]
      exact congrArg _ h.symm)
  let σ : N ≃ N := Equiv.subtypeCongr e f
  have hσ : ∀ i, σ i ∈ T ↔ i ∈ S := by
    intro i
    by_cases hi : i ∈ S
    · have : σ i = e ⟨i, hi⟩ := by simp [σ, Equiv.subtypeCongr, hi]
      rw [this]
      exact ⟨fun _ => hi, fun _ => (e ⟨i, hi⟩).2⟩
    · have : σ i = f ⟨i, hi⟩ := by simp [σ, Equiv.subtypeCongr, hi]
      rw [this]
      exact ⟨fun h' => ((f ⟨i, hi⟩).2 h').elim, fun h' => (hi h').elim⟩
  have hQσ : Q = Profile.permuteAgents σ P := funext fun i =>
    eq_of_strictPart_iff_of_two hxy hX hQ hP (by
      have := hσ i
      simp only [S, T, mem_supporters] at this
      exact this.symm)
  rw [hQσ, hA σ hP (permuteAgents_mem_linearProfiles hP σ)]

/-- Swapping `x` and `y` reverses the social comparison and the supporters. -/
private theorem neutral_swap [DecidableEq X] (hN : IsNeutralOn F (linearProfiles N X))
    (hP : P ∈ linearProfiles N X) :
    (F (Profile.relabel (Equiv.swap x y) P) x y ↔ F P y x) ∧
      supporters (Profile.relabel (Equiv.swap x y) P) x y = supporters P y x := by
  constructor
  · rw [hN (Equiv.swap x y) hP (relabel_mem_linearProfiles hP _)]
    simp
  · rw [supporters_relabel]
    simp

/-- For `x ≠ y`, a linear profile whose supporters of `x` against `y` are a given set. -/
private theorem exists_supporters_eq (hxy : x ≠ y) (S : Finset N) :
    ∃ Q ∈ linearProfiles N X, supporters Q x y = S := by
  classical
  obtain ⟨Q, hQ, hr⟩ := exists_mem_linearProfiles_strictPart_of_lt (N := N)
    fun i z => if i ∈ S then (if z = x then 1 else 0) else (if z = x then 0 else 1)
  exact ⟨Q, hQ, supporters_eq_of_forall (fun i hi => hr i x y (by simp [hi, hxy.symm]))
    (fun i hi => hr i y x (by simp [hi, hxy.symm]))⟩

/-- If more agents prefer `x` to `y` than `y` to `x`, society strictly prefers `x` to `y`. -/
private theorem strictPart_of_card_lt (hxy : x ≠ y) (hX : ∀ z, z = x ∨ z = y)
    (hF : ∀ P ∈ linearProfiles N X, IsComplete (F P))
    (hA : IsAnonymousOn F (linearProfiles N X)) (hN : IsNeutralOn F (linearProfiles N X))
    (hR : IsPositivelyResponsiveOn F (linearProfiles N X)) (hP : P ∈ linearProfiles N X)
    (hlt : (supporters P y x).card < (supporters P x y).card) : StrictPart (F P) x y := by
  classical
  have hnot : ¬ F P y x := by
    intro hyx
    let P' := Profile.relabel (Equiv.swap x y) P
    have hP' : P' ∈ linearProfiles N X := relabel_mem_linearProfiles hP _
    obtain ⟨hF', hs'⟩ := neutral_swap (x := x) (y := y) hN hP
    have hxy' : F P' x y := hF'.2 hyx
    obtain ⟨S, hS₁, -, hS₂⟩ := Finset.exists_subsuperset_card_eq (s := supporters P' x y)
      (t := Finset.univ) (n := (supporters P x y).card) (Finset.subset_univ _)
      (by rw [hs']; exact hlt.le) (Finset.card_le_univ _)
    obtain ⟨Q, hQ, hQS⟩ := exists_supporters_eq (X := X) hxy S
    have hrise : RisesAgainst P' Q x y := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
      · rw [← mem_supporters, hQS]; exact hS₁ (mem_supporters.2 hi)
      · have hi' : i ∉ supporters P' x y := fun h => by
          have : i ∈ supporters Q x y := hQS ▸ hS₁ h
          exact (mem_supporters.1 this).asymm hi
        exact ((strictPart_or_strictPart_of_mem_linearProfiles hP' hxy i).resolve_left
          fun h => hi' (mem_supporters.2 h))
      · have hcard : (supporters P' x y).card < S.card := by rw [hs', hS₂]; exact hlt
        obtain ⟨i, hiS, hiP⟩ := Finset.exists_of_ssubset
          (Finset.ssubset_iff_subset_ne.2 ⟨hS₁, fun h => hcard.ne (congrArg _ h)⟩)
        exact ⟨i, Or.inl ⟨mem_supporters.1 (hQS ▸ hiS), fun h => hiP (mem_supporters.2 h)⟩⟩
    have hQF : StrictPart (F Q) x y := hR hP' hQ x y hrise hxy'
    have hFQ : F Q = F P := eq_of_card_supporters_eq hxy hX hA hQ hP (by rw [hQS, hS₂])
    rw [hFQ] at hQF
    exact hQF.2 hyx
  exact (hF P hP).not_rel_iff.1 hnot

/-- If as many agents prefer `x` to `y` as `y` to `x`, society is indifferent. -/
private theorem indiff_of_card_eq (hxy : x ≠ y) (hX : ∀ z, z = x ∨ z = y)
    (hF : ∀ P ∈ linearProfiles N X, IsComplete (F P))
    (hA : IsAnonymousOn F (linearProfiles N X)) (hN : IsNeutralOn F (linearProfiles N X))
    (hP : P ∈ linearProfiles N X)
    (heq : (supporters P y x).card = (supporters P x y).card) : Indiff (F P) x y := by
  classical
  obtain ⟨hF', hs'⟩ := neutral_swap (x := x) (y := y) hN hP
  have hP' := relabel_mem_linearProfiles hP (Equiv.swap x y)
  have hFeq : F (Profile.relabel (Equiv.swap x y) P) = F P :=
    eq_of_card_supporters_eq hxy hX hA hP' hP (by rw [hs', heq])
  rw [hFeq] at hF'
  rcases (hF P hP).total x y with h | h
  · exact ⟨h, hF'.1 h⟩
  · exact ⟨hF'.2 h, h⟩

/-- **May's theorem**: on two alternatives, an anonymous, neutral, positively responsive rule
that is complete on linear profiles is majority rule there. -/
theorem eqOn_majority_of_isAnonymousOn_of_isNeutralOn_of_isPositivelyResponsiveOn {a b : X}
    (hab : a ≠ b) (hX : ∀ z, z = a ∨ z = b)
    (hF : ∀ P ∈ linearProfiles N X, IsComplete (F P))
    (hA : IsAnonymousOn F (linearProfiles N X)) (hN : IsNeutralOn F (linearProfiles N X))
    (hR : IsPositivelyResponsiveOn F (linearProfiles N X)) :
    Set.EqOn F majority (linearProfiles N X) := by
  intro P hP
  have pair : ∀ {x y : X}, x ≠ y → (∀ z, z = x ∨ z = y) → (F P x y ↔ majority P x y) := by
    intro x y hxy hX'
    rw [majority_apply]
    rcases lt_trichotomy (supporters P y x).card (supporters P x y).card with h | h | h
    · exact ⟨fun _ => h.le, fun _ => (strictPart_of_card_lt hxy hX' hF hA hN hR hP h).1⟩
    · exact ⟨fun _ => h.le, fun _ => (indiff_of_card_eq hxy hX' hF hA hN hP h).1⟩
    · have hX'' : ∀ z, z = y ∨ z = x := fun z => (hX' z).symm
      exact ⟨fun h' => ((strictPart_of_card_lt hxy.symm hX'' hF hA hN hR hP h).2 h').elim,
        fun h' => (h.not_ge h').elim⟩
  funext s t
  apply propext
  rcases hX s with rfl | rfl <;> rcases hX t with rfl | rfl
  · exact ⟨fun _ => majority_self P _, fun _ => (hF P hP).isReflexive.refl _⟩
  · exact pair hab hX
  · exact pair hab.symm fun z => (hX z).symm
  · exact ⟨fun _ => majority_self P _, fun _ => (hF P hP).isReflexive.refl _⟩

/-- May's characterization: on two alternatives, the three axioms hold iff the rule is majority. -/
theorem isAnonymousOn_and_isNeutralOn_and_isPositivelyResponsiveOn_iff_eqOn_majority {a b : X}
    (hab : a ≠ b) (hX : ∀ z, z = a ∨ z = b)
    (hF : ∀ P ∈ linearProfiles N X, IsComplete (F P)) :
    IsAnonymousOn F (linearProfiles N X) ∧ IsNeutralOn F (linearProfiles N X) ∧
        IsPositivelyResponsiveOn F (linearProfiles N X) ↔
      Set.EqOn F majority (linearProfiles N X) := by
  refine ⟨fun ⟨hA, hN, hR⟩ =>
    eqOn_majority_of_isAnonymousOn_of_isNeutralOn_of_isPositivelyResponsiveOn hab hX hF hA hN hR,
    fun h => ⟨fun σ P hP hσP => ?_, fun τ P hP hτP s t => ?_, fun P hP Q hQ s t hr hst => ?_⟩⟩
  · rw [h hP, h hσP]; exact isAnonymousOn_majority _ σ hP hσP
  · rw [h hP, h hτP]; exact isNeutralOn_majority _ τ hP hτP s t
  · rw [h hP] at hst; rw [h hQ]; exact isPositivelyResponsiveOn_majority _ hP hQ s t hr hst

end MathEconLib.SocialChoice

/-! ### Worked examples -/

section Examples

open MathEconLib.Preference MathEconLib.SocialChoice

example (F : SocialWelfareFunction (Fin 3) Bool)
    (hF : ∀ P ∈ linearProfiles (Fin 3) Bool, IsComplete (F P))
    (hA : IsAnonymousOn F (linearProfiles (Fin 3) Bool))
    (hN : IsNeutralOn F (linearProfiles (Fin 3) Bool))
    (hR : IsPositivelyResponsiveOn F (linearProfiles (Fin 3) Bool)) :
    Set.EqOn F majority (linearProfiles (Fin 3) Bool) :=
  eqOn_majority_of_isAnonymousOn_of_isNeutralOn_of_isPositivelyResponsiveOn (a := true)
    (b := false) (by decide) (fun z => by cases z <;> simp) hF hA hN hR

/-- The converse direction, on `Bool` with four agents. -/
example : IsAnonymousOn (majority (N := Fin 4) (X := Bool)) (linearProfiles _ _) ∧
    IsNeutralOn (majority (N := Fin 4) (X := Bool)) (linearProfiles _ _) ∧
    IsPositivelyResponsiveOn (majority (N := Fin 4) (X := Bool)) (linearProfiles _ _) :=
  (isAnonymousOn_and_isNeutralOn_and_isPositivelyResponsiveOn_iff_eqOn_majority (a := true)
    (b := false) (by decide) (fun z => by cases z <;> simp)
    (fun P _ => isComplete_majority P)).2 fun _ _ => rfl

end Examples
