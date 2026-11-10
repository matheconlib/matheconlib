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

With two alternatives, a social welfare function is anonymous, neutral and positively responsive
on the linear profiles if and only if it is majority rule there.

## Main statements

* `le_iff_majority_of_isAnonymousOn_of_isNeutralOn_of_isPositivelyResponsiveOn`: **May's theorem**.
* `isAnonymousOn_and_isNeutralOn_and_isPositivelyResponsiveOn_iff_le_iff_majority`: with
  converse.

## Implementation notes

* The domain is the linear profiles; May's domain also allows indifference.

## References

* K. O. May, *A set of independent necessary and sufficient conditions for simple majority
  decision*, Econometrica **20** (1952), 680–684
* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Chapter 20, Problem 1
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preferences

universe u v

variable {N : Type u} {X : Type v} [Fintype N] {F : SocialWelfareFunction N X} {x y : X}
  {P Q : Profile N fun _ => X}

omit [Fintype N] in
/-- On two alternatives, a linear preference is determined by whether `x` is preferred to `y`. -/
private theorem eq_of_lt_iff_of_two (hxy : x ≠ y) (hX : ∀ z, z = x ∨ z = y)
    (hP : P ∈ linearProfiles N X) (hQ : Q ∈ linearProfiles N X) {i j : N}
    (h : y ≺[P i] x ↔ y ≺[Q j] x) : P i = Q j := by
  apply eq_of_mem_linearProfiles_of_lt_iff hP hQ
  intro s t
  rcases hX s with rfl | rfl <;> rcases hX t with rfl | rfl
  · simp
  · rw [lt_iff_not_lt_of_mem_linearProfiles hP hxy, lt_iff_not_lt_of_mem_linearProfiles hQ hxy, h]
  · exact h
  · simp

/-- By anonymity, society's preference depends only on the number of supporters of `x`. -/
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
  have hQσ : Q = P.reindexAgents σ := funext fun i =>
    eq_of_lt_iff_of_two hxy hX hQ (reindexAgents_mem_linearProfiles hP σ) (by
      have := hσ i
      simp only [S, T, mem_supporters] at this
      exact this.symm)
  rw [hQσ, hA σ hP (reindexAgents_mem_linearProfiles hP σ)]

/-- Swapping `x` and `y` reverses society's comparison and the supporters. -/
private theorem neutral_swap [DecidableEq X] (hN : IsNeutralOn F (linearProfiles N X))
    (hP : P ∈ linearProfiles N X) :
    (y ≼[F (P.comap fun _ => (Equiv.swap x y).symm)] x ↔ x ≼[F P] y) ∧
      supporters (P.comap fun _ => (Equiv.swap x y).symm) x y = supporters P y x := by
  constructor
  · rw [hN (Equiv.swap x y) hP (comap_mem_linearProfiles hP (Equiv.swap x y).symm.injective)]
    simp
  · rw [supporters_comap]
    simp

/-- For `x ≠ y`, a linear profile whose supporters of `x` against `y` are a given set. -/
private theorem exists_supporters_eq (hxy : x ≠ y) (S : Finset N) :
    ∃ Q ∈ linearProfiles N X, supporters Q x y = S := by
  classical
  obtain ⟨Q, hQ, hr⟩ := exists_mem_linearProfiles_lt_of_lt (N := N)
    fun i z => if i ∈ S then (if z = x then 1 else 0) else (if z = x then 0 else 1)
  exact ⟨Q, hQ, supporters_eq_of_forall (fun i hi => hr i x y (by simp [hi, hxy.symm]))
    (fun i hi => hr i y x (by simp [hi, hxy.symm]))⟩

/-- If more agents prefer `x` to `y` than `y` to `x`, society strictly prefers `x` to `y`. -/
private theorem lt_of_card_lt (hxy : x ≠ y) (hX : ∀ z, z = x ∨ z = y)
    (hA : IsAnonymousOn F (linearProfiles N X)) (hN : IsNeutralOn F (linearProfiles N X))
    (hR : IsPositivelyResponsiveOn F (linearProfiles N X)) (hP : P ∈ linearProfiles N X)
    (hlt : (supporters P y x).card < (supporters P x y).card) : y ≺[F P] x := by
  classical
  have hnot : ¬ x ≼[F P] y := by
    intro hyx
    let P' := P.comap fun _ => (Equiv.swap x y).symm
    have hP' : P' ∈ linearProfiles N X :=
      comap_mem_linearProfiles hP (Equiv.swap x y).symm.injective
    obtain ⟨hF', hs'⟩ := neutral_swap (x := x) (y := y) hN hP
    have hxy' : y ≼[F P'] x := hF'.2 hyx
    obtain ⟨S, hS₁, -, hS₂⟩ := Finset.exists_subsuperset_card_eq (s := supporters P' x y)
      (t := Finset.univ) (n := (supporters P x y).card) (Finset.subset_univ _)
      (by rw [hs']; exact hlt.le) (Finset.card_le_univ _)
    obtain ⟨Q, hQ, hQS⟩ := exists_supporters_eq (X := X) hxy S
    have hrise : RisesAgainst P' Q x y := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
      · rw [← mem_supporters, hQS]; exact hS₁ (mem_supporters.2 hi)
      · have hi' : i ∉ supporters P' x y := fun h => by
          have : i ∈ supporters Q x y := hQS ▸ hS₁ h
          exact (Q i).lt_asymm (mem_supporters.1 this) hi
        exact ((lt_or_gt_of_mem_linearProfiles hP' hxy i).resolve_left
          fun h => hi' (mem_supporters.2 h))
      · have hcard : (supporters P' x y).card < S.card := by rw [hs', hS₂]; exact hlt
        obtain ⟨i, hiS, hiP⟩ := Finset.exists_of_ssubset
          (Finset.ssubset_iff_subset_ne.2 ⟨hS₁, fun h => hcard.ne (congrArg _ h)⟩)
        exact ⟨i, Or.inl ⟨mem_supporters.1 (hQS ▸ hiS), fun h => hiP (mem_supporters.2 h)⟩⟩
    have hQF : y ≺[F Q] x := hR hP' hQ x y hrise hxy'
    have hFQ : F Q = F P := eq_of_card_supporters_eq hxy hX hA hQ hP (by rw [hQS, hS₂])
    rw [hFQ] at hQF
    exact hQF.2 hyx
  exact (F P).not_le.1 hnot

/-- If as many agents prefer `x` to `y` as `y` to `x`, society is indifferent. -/
private theorem antisymmRel_of_card_eq (hxy : x ≠ y) (hX : ∀ z, z = x ∨ z = y)
    (hA : IsAnonymousOn F (linearProfiles N X)) (hN : IsNeutralOn F (linearProfiles N X))
    (hP : P ∈ linearProfiles N X)
    (heq : (supporters P y x).card = (supporters P x y).card) : x ~[F P] y := by
  classical
  obtain ⟨hF', hs'⟩ := neutral_swap (x := x) (y := y) hN hP
  have hP' := comap_mem_linearProfiles hP (Equiv.swap x y).symm.injective
  have hFeq : F (P.comap fun _ => (Equiv.swap x y).symm) = F P :=
    eq_of_card_supporters_eq hxy hX hA hP' hP (by rw [hs', heq])
  rw [hFeq] at hF'
  rcases (F P).total x y with h | h
  · exact ⟨h, hF'.2 h⟩
  · exact ⟨hF'.1 h, h⟩

/-- **May's theorem**: on two alternatives, an anonymous, neutral, positively responsive social
welfare function is majority rule on linear profiles. -/
theorem le_iff_majority_of_isAnonymousOn_of_isNeutralOn_of_isPositivelyResponsiveOn {a b : X}
    (hab : a ≠ b) (hX : ∀ z, z = a ∨ z = b)
    (hA : IsAnonymousOn F (linearProfiles N X)) (hN : IsNeutralOn F (linearProfiles N X))
    (hR : IsPositivelyResponsiveOn F (linearProfiles N X)) :
    ∀ P ∈ linearProfiles N X, ∀ x y : X, x ≼[F P] y ↔ majority P x y := by
  intro P hP
  have pair : ∀ {x y : X}, x ≠ y → (∀ z, z = x ∨ z = y) → (y ≼[F P] x ↔ majority P y x) := by
    intro x y hxy hX'
    rw [majority_apply]
    rcases lt_trichotomy (supporters P y x).card (supporters P x y).card with h | h | h
    · exact ⟨fun _ => h.le, fun _ => (lt_of_card_lt hxy hX' hA hN hR hP h).1⟩
    · exact ⟨fun _ => h.le, fun _ => (antisymmRel_of_card_eq hxy hX' hA hN hP h).2⟩
    · have hX'' : ∀ z, z = y ∨ z = x := fun z => (hX' z).symm
      exact ⟨fun h' => ((lt_of_card_lt hxy.symm hX'' hA hN hR hP h).2 h').elim,
        fun h' => (h.not_ge h').elim⟩
  intro s t
  rcases hX s with rfl | rfl <;> rcases hX t with rfl | rfl
  · exact ⟨fun _ => majority_self P _, fun _ => (F P).le_refl _⟩
  · exact pair hab.symm fun z => (hX z).symm
  · exact pair hab hX
  · exact ⟨fun _ => majority_self P _, fun _ => (F P).le_refl _⟩

/-- May's characterization: on two alternatives, the three axioms hold iff the social welfare
function is majority rule on linear profiles. -/
theorem isAnonymousOn_and_isNeutralOn_and_isPositivelyResponsiveOn_iff_le_iff_majority {a b : X}
    (hab : a ≠ b) (hX : ∀ z, z = a ∨ z = b) :
    IsAnonymousOn F (linearProfiles N X) ∧ IsNeutralOn F (linearProfiles N X) ∧
        IsPositivelyResponsiveOn F (linearProfiles N X) ↔
      ∀ P ∈ linearProfiles N X, ∀ x y : X, x ≼[F P] y ↔ majority P x y := by
  refine ⟨fun ⟨hA, hN, hR⟩ =>
    le_iff_majority_of_isAnonymousOn_of_isNeutralOn_of_isPositivelyResponsiveOn hab hX hA hN hR,
    fun h => ⟨fun σ P hP hσP => ?_, fun τ P hP hτP s t => ?_, fun P hP Q hQ s t hr hst => ?_⟩⟩
  · ext s t
    rw [h _ hσP, h _ hP, majority_reindexAgents]
  · rw [h _ hτP, h _ hP, majority_comap]
  · exact (F Q).not_le.1 fun h' =>
      not_majority_of_risesAgainst hr ((h _ hP t s).1 hst) ((h _ hQ s t).1 h')

end MathEconLib.SocialChoice

/-! ### Worked examples -/

section Examples

open MathEconLib.Preferences MathEconLib.SocialChoice

example (F : SocialWelfareFunction (Fin 3) Bool)
    (hA : IsAnonymousOn F (linearProfiles (Fin 3) Bool))
    (hN : IsNeutralOn F (linearProfiles (Fin 3) Bool))
    (hR : IsPositivelyResponsiveOn F (linearProfiles (Fin 3) Bool)) :
    ∀ P ∈ linearProfiles (Fin 3) Bool, ∀ x y : Bool, x ≼[F P] y ↔ majority P x y :=
  le_iff_majority_of_isAnonymousOn_of_isNeutralOn_of_isPositivelyResponsiveOn (a := true)
    (b := false) (by decide) (fun z => by cases z <;> simp) hA hN hR

/-- Majority rule on two alternatives as a social welfare function: each alternative's utility is
the number of agents who strictly prefer it to the other. -/
private noncomputable def majorityOnBool {N : Type*} [Fintype N] : SocialWelfareFunction N Bool :=
  fun P => CompletePreference.ofUtility fun b => (supporters P b !b).card

/-- The converse direction, on `Bool` with four agents: majority rule satisfies May's axioms. -/
example : IsAnonymousOn (majorityOnBool (N := Fin 4)) (linearProfiles _ _) ∧
    IsNeutralOn (majorityOnBool (N := Fin 4)) (linearProfiles _ _) ∧
    IsPositivelyResponsiveOn (majorityOnBool (N := Fin 4)) (linearProfiles _ _) :=
  (isAnonymousOn_and_isNeutralOn_and_isPositivelyResponsiveOn_iff_le_iff_majority (a := true)
    (b := false) (by decide) (fun z => by cases z <;> simp)).2 fun P _ x y => by
      cases x <;> cases y <;> simp [majorityOnBool, majority_apply]

end Examples
