/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.SocialChoice.Majority
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FinCases

/-!
# May's theorem

With two alternatives, a social welfare function on the linear profiles is anonymous, neutral and
positively responsive if and only if it is majority rule there, ties included: society is
indifferent exactly when the two alternatives have equally many supporters.

## Main statements

* `le_iff_majority_of_isAnonymous_of_isNeutral_of_isPositivelyResponsive`: **May's theorem**.
* `isAnonymous_and_isNeutral_and_isPositivelyResponsive_iff_le_iff_majority`: with converse.

## Implementation notes

* The inputs are strict: the domain is the linear profiles, while May's domain also allows
  individual indifference.
* May assumes that the social relation is complete. Here the rule returns a `CompletePreference`;
  with two alternatives every complete relation is transitive, so this is the same premise.
* Anonymity concerns permutations of the agents, and neutrality equivalences of the alternatives.

## References

* K. O. May, *A set of independent necessary and sufficient conditions for simple majority
  decision*, Econometrica **20** (1952), 680–684
* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Chapter 20, Problem 1
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preferences

universe u v

variable {N : Type u} {X : Type v} [Fintype N] {F : SocialWelfareFunction (linearProfiles N X)}
  {x y : X} {P Q : Profile N fun _ => X}

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
    (hA : IsAnonymous F) (hP : P ∈ linearProfiles N X)
    (hQ : Q ∈ linearProfiles N X) (h : (supporters P x y).card = (supporters Q x y).card) :
    F ⟨P, hP⟩ = F ⟨Q, hQ⟩ := by
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
  have hQ' : P.reindexAgents σ ∈ linearProfiles N X := reindexAgents_mem_linearProfiles hP σ
  rw [← hA σ ⟨P, hP⟩ hQ']
  exact congrArg F (Subtype.ext hQσ.symm)

/-- Swapping `x` and `y` reverses society's comparison and the supporters. -/
private theorem neutral_swap [DecidableEq X] (hN : IsNeutral F) (hP : P ∈ linearProfiles N X) :
    (y ≼[F ⟨P.comap fun _ => (Equiv.swap x y).symm,
        comap_mem_linearProfiles hP (Equiv.swap x y).symm.injective⟩] x ↔ x ≼[F ⟨P, hP⟩] y) ∧
      supporters (P.comap fun _ => (Equiv.swap x y).symm) x y = supporters P y x := by
  constructor
  · rw [hN (Equiv.swap x y) ⟨P, hP⟩]
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
    (hA : IsAnonymous F) (hN : IsNeutral F) (hR : IsPositivelyResponsive F)
    (hP : P ∈ linearProfiles N X)
    (hlt : (supporters P y x).card < (supporters P x y).card) : y ≺[F ⟨P, hP⟩] x := by
  classical
  have hnot : ¬ x ≼[F ⟨P, hP⟩] y := by
    intro hyx
    let P' := P.comap fun _ => (Equiv.swap x y).symm
    have hP' : P' ∈ linearProfiles N X :=
      comap_mem_linearProfiles hP (Equiv.swap x y).symm.injective
    obtain ⟨hF', hs'⟩ := neutral_swap (x := x) (y := y) hN hP
    have hxy' : y ≼[F ⟨P', hP'⟩] x := hF'.2 hyx
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
    have hQF : y ≺[F ⟨Q, hQ⟩] x := hR ⟨P', hP'⟩ ⟨Q, hQ⟩ x y hrise hxy'
    have hFQ : F ⟨Q, hQ⟩ = F ⟨P, hP⟩ :=
      eq_of_card_supporters_eq hxy hX hA hQ hP (by rw [hQS, hS₂])
    rw [hFQ] at hQF
    exact hQF.2 hyx
  exact (F ⟨P, hP⟩).not_le.1 hnot

/-- If as many agents prefer `x` to `y` as `y` to `x`, society is indifferent. -/
private theorem antisymmRel_of_card_eq (hxy : x ≠ y) (hX : ∀ z, z = x ∨ z = y)
    (hA : IsAnonymous F) (hN : IsNeutral F) (hP : P ∈ linearProfiles N X)
    (heq : (supporters P y x).card = (supporters P x y).card) : x ~[F ⟨P, hP⟩] y := by
  classical
  obtain ⟨hF', hs'⟩ := neutral_swap (x := x) (y := y) hN hP
  have hFeq := eq_of_card_supporters_eq hxy hX hA
    (comap_mem_linearProfiles hP (Equiv.swap x y).symm.injective) hP (by rw [hs', heq])
  rw [hFeq] at hF'
  rcases (F ⟨P, hP⟩).total x y with h | h
  · exact ⟨h, hF'.2 h⟩
  · exact ⟨hF'.1 h, h⟩

/-- **May's theorem**: on two alternatives, an anonymous, neutral, positively responsive social
welfare function on linear profiles is majority rule, ties included. -/
theorem le_iff_majority_of_isAnonymous_of_isNeutral_of_isPositivelyResponsive {a b : X}
    (hab : a ≠ b) (hX : ∀ z, z = a ∨ z = b) (hA : IsAnonymous F) (hN : IsNeutral F)
    (hR : IsPositivelyResponsive F) :
    ∀ (P : {P // P ∈ linearProfiles N X}) (x y : X), x ≼[F P] y ↔ majority P.1 x y := by
  rintro ⟨P, hP⟩
  have pair : ∀ {x y : X}, x ≠ y → (∀ z, z = x ∨ z = y) →
      (y ≼[F ⟨P, hP⟩] x ↔ majority P y x) := by
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
  · exact ⟨fun _ => majority_self P _, fun _ => (F ⟨P, hP⟩).le_refl _⟩
  · exact pair hab.symm fun z => (hX z).symm
  · exact pair hab hX
  · exact ⟨fun _ => majority_self P _, fun _ => (F ⟨P, hP⟩).le_refl _⟩

/-- May's characterization: on two alternatives, the three axioms hold iff the social welfare
function is majority rule on linear profiles. -/
theorem isAnonymous_and_isNeutral_and_isPositivelyResponsive_iff_le_iff_majority {a b : X}
    (hab : a ≠ b) (hX : ∀ z, z = a ∨ z = b) :
    IsAnonymous F ∧ IsNeutral F ∧ IsPositivelyResponsive F ↔
      ∀ (P : {P // P ∈ linearProfiles N X}) (x y : X), x ≼[F P] y ↔ majority P.1 x y := by
  refine ⟨fun ⟨hA, hN, hR⟩ =>
    le_iff_majority_of_isAnonymous_of_isNeutral_of_isPositivelyResponsive hab hX hA hN hR,
    fun h => ⟨fun σ P hσP => ?_, fun τ P hτP s t => ?_, fun P Q s t hr hst => ?_⟩⟩
  · ext s t
    rw [h, h, majority_reindexAgents]
  · rw [h, h, majority_comap]
  · exact (F Q).not_le.1 fun h' =>
      not_majority_of_risesAgainst hr ((h P t s).1 hst) ((h Q s t).1 h')

end MathEconLib.SocialChoice

/-! ### Worked examples -/

section Examples

open MathEconLib.Preferences MathEconLib.SocialChoice

example (F : SocialWelfareFunction (linearProfiles (Fin 3) Bool)) (hA : IsAnonymous F)
    (hN : IsNeutral F) (hR : IsPositivelyResponsive F) :
    ∀ (P : {P // P ∈ linearProfiles (Fin 3) Bool}) (x y : Bool), x ≼[F P] y ↔ majority P.1 x y :=
  le_iff_majority_of_isAnonymous_of_isNeutral_of_isPositivelyResponsive (a := true)
    (b := false) (by decide) (fun z => by cases z <;> simp) hA hN hR

/-- Majority rule on two alternatives as a social welfare function: each alternative's utility is
the number of agents who strictly prefer it to the other. -/
private noncomputable def majorityOnBool {N : Type*} [Fintype N] :
    SocialWelfareFunction (linearProfiles N Bool) :=
  fun P => CompletePreference.ofUtility fun b => (supporters P.1 b !b).card

/-- The converse direction, on `Bool` with four agents: majority rule satisfies May's axioms. -/
example : IsAnonymous (majorityOnBool (N := Fin 4)) ∧ IsNeutral (majorityOnBool (N := Fin 4)) ∧
    IsPositivelyResponsive (majorityOnBool (N := Fin 4)) :=
  (isAnonymous_and_isNeutral_and_isPositivelyResponsive_iff_le_iff_majority (a := true)
    (b := false) (by decide) (fun z => by cases z <;> simp)).2 fun P x y => by
      cases x <;> cases y <;> simp [majorityOnBool, majority_apply]

/-- A tied two-alternative vote: agent `0` strictly prefers `true` and agent `1` strictly prefers
`false`. -/
private def tiedVote : Profile (Fin 2) fun _ => Bool :=
  Profile.ofUtility fun i b => if i = 0 then b.toNat else (!b).toNat

/-- In a tied vote, May's axioms force social indifference. -/
example (F : SocialWelfareFunction (linearProfiles (Fin 2) Bool)) (hA : IsAnonymous F)
    (hN : IsNeutral F) (hR : IsPositivelyResponsive F) :
    true ~[F ⟨tiedVote, ofUtility_mem_linearProfiles (by decide)⟩] false := by
  have h₁ : supporters tiedVote true false = {0} :=
    supporters_eq_of_forall
      (fun i hi => by simp only [Finset.mem_singleton] at hi; subst hi; simp [tiedVote])
      (fun i hi => by
        have : i = 1 := by fin_cases i <;> simp_all
        subst this; simp [tiedVote])
  have h₂ : supporters tiedVote false true = {1} :=
    supporters_eq_of_forall
      (fun i hi => by simp only [Finset.mem_singleton] at hi; subst hi; simp [tiedVote])
      (fun i hi => by
        have : i = 0 := by fin_cases i <;> simp_all
        subst this; simp [tiedVote])
  have hmay := le_iff_majority_of_isAnonymous_of_isNeutral_of_isPositivelyResponsive (a := true)
    (b := false) (by decide) (fun z => by cases z <;> simp) hA hN hR
    ⟨tiedVote, ofUtility_mem_linearProfiles (by decide)⟩
  exact ⟨(hmay true false).2 (by simp [majority_apply, h₁, h₂]),
    (hmay false true).2 (by simp [majority_apply, h₁, h₂])⟩

end Examples
