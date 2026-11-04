/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.SocialChoice.Dictatorship
public import MathEconLib.SocialChoice.Majority
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card

/-!
# Arrow's impossibility theorem

With finitely many agents and at least three alternatives, a social welfare function whose social
relation is a preference relation at every linear profile, and which satisfies the Pareto property
and independence of irrelevant alternatives on the linear profiles, has a dictator there.

## Main statements

* `isDictatorialOn_of_isParetoOn_of_isIIAOn`: **Arrow's impossibility theorem**, for three
  distinct alternatives `a`, `b`, `c`.
* `isParetoOn_and_isIIAOn_iff_isDictatorialOn`: Osborne and Rubinstein's Proposition 20.1: on the
  linear profiles, the Pareto property and independence of irrelevant alternatives hold if and
  only if the rule is dictatorial.
* `isDictatorialOn_of_isParetoOn_of_isIIAOn_of_two_lt_card`: the theorem for a finite type of at
  least three alternatives.

## Implementation notes

* The proof is Sen's, by decisive coalitions, not Osborne and Rubinstein's (Geanakoplos's
  pivotal-agent argument). A coalition `G` is decisive for `x` against `y` if society strictly
  prefers `x` to `y` whenever every member of `G` does. (1) Field expansion: if `G` is decisive
  for `x` against `y` at the profiles where everyone outside `G` prefers `y` to `x`, it is
  decisive for every pair; this uses a third alternative, transitivity, Pareto and independence.
  (2) Contraction: a coalition decisive for every pair, with at least two members, has a proper
  part decisive for every pair; this uses completeness. (3) The set of all agents is decisive
  (Pareto), so some single agent is, and she is a dictator.
* The alternatives form an arbitrary type `X`, not necessarily finite, with three distinct
  elements. The agents are finite (`[Finite N]`), as Arrow's theorem requires.
* The social relation is assumed to be a preference relation only at linear profiles
  (`∀ P ∈ linearProfiles N X, IsPreferenceRelation (F P)`); Osborne and Rubinstein's preference
  aggregation functions satisfy this by definition.

## References

Kenneth J. Arrow (1951), *Social Choice and Individual Values*, Wiley, Chapter V. Arrow's original
conditions are positive association and non-imposition rather than the Pareto property.

Amartya K. Sen (1970), *Collective Choice and Social Welfare*, Holden-Day, Chapter 3* (the proof
by decisive coalitions).

Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, expanded second
edition, Open Book Publishers, Proposition 20.1.
[DOI: 10.11647/OBP.0361](https://doi.org/10.11647/OBP.0361).

## Tags

Arrow's impossibility theorem, social welfare function, dictator, decisive coalition
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preference

universe u v

variable {N : Type u} {X : Type v} {F : SocialWelfareFunction N X}

/-- Closes a comparison of two ranks written with `if … then … else`, from the hypotheses that
decide the conditions. -/
local macro "rank_tac" : tactic => `(tactic| (split_ifs <;> first | omega | contradiction))

/-- `G` is decisive for `x` against `y`: at every linear profile at which every member of `G`
strictly prefers `x` to `y`, society strictly prefers `x` to `y`. -/
private def Decisive (F : SocialWelfareFunction N X) (G : Set N) (x y : X) : Prop :=
  ∀ P ∈ linearProfiles N X, (∀ i ∈ G, StrictPart (P i) x y) → StrictPart (F P) x y

/-- `G` is decisive for `x` against `y` at the linear profiles where everyone outside `G` strictly
prefers `y` to `x`. -/
private def WeaklyDecisive (F : SocialWelfareFunction N X) (G : Set N) (x y : X) : Prop :=
  ∀ P ∈ linearProfiles N X, (∀ i ∈ G, StrictPart (P i) x y) → (∀ i ∉ G, StrictPart (P i) y x) →
    StrictPart (F P) x y

private theorem weaklyDecisive_of_decisive {G : Set N} {x y : X} (h : Decisive F G x y) :
    WeaklyDecisive F G x y :=
  fun P hP hG _ => h P hP hG

/-- Field expansion to the right: weakly decisive for `a` against `b` gives decisive for `a`
against any third `c`. -/
private theorem decisive_left_of_weaklyDecisive
    (hF : ∀ P ∈ linearProfiles N X, IsPreferenceRelation (F P))
    (hPar : IsParetoOn F (linearProfiles N X)) (hIIA : IsIIAOn F (linearProfiles N X))
    {G : Set N} {a b c : X} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hW : WeaklyDecisive F G a b) : Decisive F G a c := by
  classical
  intro P hP hG
  let r : N → X → ℕ := fun i z =>
    if i ∈ G then (if z = a then 3 else if z = b then 2 else if z = c then 1 else 0)
    else (if z = b then 3 else if z = a then (if StrictPart (P i) a c then 2 else 1)
      else if z = c then (if StrictPart (P i) a c then 1 else 2) else 0)
  have ra : ∀ i, r i a = if i ∈ G then 3 else if StrictPart (P i) a c then 2 else 1 :=
    fun i => by simp [r, hab]
  have rb : ∀ i, r i b = if i ∈ G then 2 else 3 := fun i => by simp [r, hab.symm]
  have rc : ∀ i, r i c = if i ∈ G then 1 else if StrictPart (P i) a c then 1 else 2 :=
    fun i => by simp [r, hca, hcb]
  obtain ⟨Q, hQ, hr⟩ := exists_mem_linearProfiles_strictPart_of_lt r
  have h₁ : StrictPart (F Q) a b := hW Q hQ
    (fun i hi => hr i a b (by rw [ra, rb]; rank_tac))
    (fun i hi => hr i b a (by rw [ra, rb]; rank_tac))
  have h₂ : StrictPart (F Q) b c := hPar hQ b c fun i => hr i b c (by rw [rb, rc]; rank_tac)
  have h₃ : StrictPart (F Q) a c := (hF Q hQ).isTransitive.strictPart.trans h₁ h₂
  refine (hIIA.strictPart_iff_of_strictPart_iff subset_rfl hQ hP hca.symm fun i => ?_).1 h₃
  by_cases hi : i ∈ G
  · exact ⟨fun _ => hG i hi, fun _ => hr i a c (by rw [ra, rc]; rank_tac)⟩
  · by_cases hs : StrictPart (P i) a c
    · exact ⟨fun _ => hs, fun _ => hr i a c (by rw [ra, rc]; rank_tac)⟩
    · exact ⟨fun h => ((hr i c a (by rw [ra, rc]; rank_tac)).asymm h).elim,
        fun h => (hs h).elim⟩

/-- Field expansion to the left: weakly decisive for `a` against `b` gives decisive for any third
`c` against `b`. -/
private theorem decisive_right_of_weaklyDecisive
    (hF : ∀ P ∈ linearProfiles N X, IsPreferenceRelation (F P))
    (hPar : IsParetoOn F (linearProfiles N X)) (hIIA : IsIIAOn F (linearProfiles N X))
    {G : Set N} {a b c : X} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hW : WeaklyDecisive F G a b) : Decisive F G c b := by
  classical
  intro P hP hG
  let r : N → X → ℕ := fun i z =>
    if i ∈ G then (if z = c then 3 else if z = a then 2 else if z = b then 1 else 0)
    else (if z = a then 1 else if z = b then (if StrictPart (P i) c b then 2 else 3)
      else if z = c then (if StrictPart (P i) c b then 3 else 2) else 0)
  have ra : ∀ i, r i a = if i ∈ G then 2 else 1 := fun i => by simp [r, hca.symm]
  have rb : ∀ i, r i b = if i ∈ G then 1 else if StrictPart (P i) c b then 2 else 3 :=
    fun i => by simp [r, hcb.symm, hab.symm]
  have rc : ∀ i, r i c = if i ∈ G then 3 else if StrictPart (P i) c b then 3 else 2 :=
    fun i => by simp [r, hca, hcb]
  obtain ⟨Q, hQ, hr⟩ := exists_mem_linearProfiles_strictPart_of_lt r
  have h₁ : StrictPart (F Q) c a := hPar hQ c a fun i => hr i c a (by rw [ra, rc]; rank_tac)
  have h₂ : StrictPart (F Q) a b := hW Q hQ
    (fun i hi => hr i a b (by rw [ra, rb]; rank_tac))
    (fun i hi => hr i b a (by rw [ra, rb]; rank_tac))
  have h₃ : StrictPart (F Q) c b := (hF Q hQ).isTransitive.strictPart.trans h₁ h₂
  refine (hIIA.strictPart_iff_of_strictPart_iff subset_rfl hQ hP hcb fun i => ?_).1 h₃
  by_cases hi : i ∈ G
  · exact ⟨fun _ => hG i hi, fun _ => hr i c b (by rw [rb, rc]; rank_tac)⟩
  · by_cases hs : StrictPart (P i) c b
    · exact ⟨fun _ => hs, fun _ => hr i c b (by rw [rb, rc]; rank_tac)⟩
    · exact ⟨fun h => ((hr i b c (by rw [rb, rc]; rank_tac)).asymm h).elim,
        fun h => (hs h).elim⟩

/-- Field expansion: with a third alternative for every pair, a coalition weakly decisive for one
pair is decisive for every pair. -/
private theorem decisive_of_weaklyDecisive
    (hF : ∀ P ∈ linearProfiles N X, IsPreferenceRelation (F P))
    (hPar : IsParetoOn F (linearProfiles N X)) (hIIA : IsIIAOn F (linearProfiles N X))
    (hX : ∀ u v : X, ∃ w, w ≠ u ∧ w ≠ v) {G : Set N} {x y : X} (hxy : x ≠ y)
    (hW : WeaklyDecisive F G x y) {u v : X} (huv : u ≠ v) : Decisive F G u v := by
  have L := fun {a b c : X} => @decisive_left_of_weaklyDecisive N X F hF hPar hIIA G a b c
  have R := fun {a b c : X} => @decisive_right_of_weaklyDecisive N X F hF hPar hIIA G a b c
  have step : ∀ {w : X}, w ≠ x → Decisive F G x w := by
    intro w hw
    by_cases hwy : w = y
    · subst hwy
      obtain ⟨z, hzx, hzw⟩ := hX x w
      exact L (Ne.symm hzx) hw (fun h => hzw h.symm)
        (weaklyDecisive_of_decisive (L hxy hzx hzw hW))
    · exact L hxy hw hwy hW
  by_cases hux : u = x
  · subst hux
    exact step (Ne.symm huv)
  by_cases hvx : v = x
  · subst hvx
    obtain ⟨z, hzu, hzv⟩ := hX u v
    have h₁ : Decisive F G u z :=
      R (Ne.symm hzv) hux (Ne.symm hzu) (weaklyDecisive_of_decisive (step hzv))
    exact L (Ne.symm hzu) (Ne.symm huv) (fun h => hzv h.symm) (weaklyDecisive_of_decisive h₁)
  · exact R (Ne.symm hvx) hux huv (weaklyDecisive_of_decisive (step hvx))

/-- Contraction: if `G` is decisive for every pair, then for `i ∈ G` either `{i}` or `G \ {i}` is
decisive for every pair. -/
private theorem decisive_singleton_or_decisive_erase [DecidableEq N]
    (hF : ∀ P ∈ linearProfiles N X, IsPreferenceRelation (F P))
    (hPar : IsParetoOn F (linearProfiles N X)) (hIIA : IsIIAOn F (linearProfiles N X))
    (hX : ∀ u v : X, ∃ w, w ≠ u ∧ w ≠ v) {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {G : Finset N} (hG : ∀ u v : X, u ≠ v → Decisive F (G : Set N) u v) {i : N} (hi : i ∈ G) :
    (∀ u v : X, u ≠ v → Decisive F ({i} : Set N) u v) ∨
      (∀ u v : X, u ≠ v → Decisive F ((G.erase i : Finset N) : Set N) u v) := by
  classical
  let r : N → X → ℕ := fun j z =>
    if j = i then (if z = a then 2 else if z = b then 1 else 0)
    else if j ∈ G then (if z = c then 2 else if z = a then 1 else 0)
    else (if z = b then 2 else if z = c then 1 else 0)
  have ra : ∀ j, r j a = if j = i then 2 else if j ∈ G then 1 else 0 := fun j => by
    simp [r, hac, hab]
  have rb : ∀ j, r j b = if j = i then 1 else if j ∈ G then 0 else 2 := fun j => by
    simp [r, hab.symm, hbc]
  have rc : ∀ j, r j c = if j = i then 0 else if j ∈ G then 2 else 1 := fun j => by
    simp [r, hac.symm, hbc.symm]
  obtain ⟨P, hP, hr⟩ := exists_mem_linearProfiles_strictPart_of_lt r
  have hPab : StrictPart (F P) a b := hG a b hab P hP fun j hj => hr j a b (by
    have : j ∈ G := hj
    rw [ra, rb]; rank_tac)
  by_cases hac' : StrictPart (F P) a c
  · left
    refine fun u v huv =>
      decisive_of_weaklyDecisive hF hPar hIIA hX hac (fun Q hQ h₁ h₂ => ?_) huv
    refine (hIIA.strictPart_iff_of_strictPart_iff subset_rfl hP hQ hac fun j => ?_).1 hac'
    by_cases hj : j = i
    · subst hj
      exact ⟨fun _ => h₁ j rfl, fun _ => hr j a c (by rw [ra, rc]; rank_tac)⟩
    · have hQj := h₂ j hj
      have hPj : StrictPart (P j) c a := hr j c a (by rw [ra, rc]; rank_tac)
      exact ⟨fun h => (hPj.asymm h).elim, fun h => (hQj.asymm h).elim⟩
  · right
    have hca : F P c a := ((hF P hP).isComplete.rel_iff_not_strictPart).2 hac'
    have hcb : StrictPart (F P) c b :=
      (hF P hP).isTransitive.strictPart_of_rel_of_strictPart hca hPab
    refine fun u v huv =>
      decisive_of_weaklyDecisive hF hPar hIIA hX hbc.symm (fun Q hQ h₁ h₂ => ?_) huv
    refine (hIIA.strictPart_iff_of_strictPart_iff subset_rfl hP hQ hbc.symm fun j => ?_).1 hcb
    by_cases hj : j ∈ G.erase i
    · have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hjG : j ∈ G := Finset.mem_of_mem_erase hj
      exact ⟨fun _ => h₁ j hj, fun _ => hr j c b (by rw [rb, rc]; rank_tac)⟩
    · have hQj := h₂ j hj
      have hjG : j = i ∨ j ∉ G := by
        by_cases hji : j = i
        · exact Or.inl hji
        · exact Or.inr fun h => hj (Finset.mem_erase.2 ⟨hji, h⟩)
      have hPj : StrictPart (P j) b c := hr j b c (by
        rw [rb, rc]
        rcases hjG with hjG | hjG <;> rank_tac)
      exact ⟨fun h => (hPj.asymm h).elim, fun h => (hQj.asymm h).elim⟩

/-- **Arrow's impossibility theorem.** With finitely many agents and three distinct alternatives,
a social welfare function whose social relation is a preference relation at every linear profile,
and which satisfies the Pareto property and independence of irrelevant alternatives on the linear
profiles, has a dictator on the linear profiles. -/
theorem isDictatorialOn_of_isParetoOn_of_isIIAOn [Finite N] {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hF : ∀ P ∈ linearProfiles N X, IsPreferenceRelation (F P))
    (hPar : IsParetoOn F (linearProfiles N X)) (hIIA : IsIIAOn F (linearProfiles N X)) :
    IsDictatorialOn F (linearProfiles N X) := by
  classical
  have _ := Fintype.ofFinite N
  have hX : ∀ u v : X, ∃ w, w ≠ u ∧ w ≠ v := by
    intro u v
    by_cases h₁ : a ≠ u ∧ a ≠ v
    · exact ⟨a, h₁⟩
    by_cases h₂ : b ≠ u ∧ b ≠ v
    · exact ⟨b, h₂⟩
    have ha : a = u ∨ a = v := by tauto
    have hb : b = u ∨ b = v := by tauto
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · exact ⟨c, fun h => hac (ha.trans h.symm), fun h => hbc (hb.trans h.symm)⟩
    · exact ⟨c, fun h => hbc (hb.trans h.symm), fun h => hac (ha.trans h.symm)⟩
    · exact absurd (ha.trans hb.symm) hab
  -- Some single agent is decisive for every pair: the set of all agents is, the empty set is
  -- not, and contraction removes one agent at a time. That agent is a dictator.
  let AllDecisive : Finset N → Prop := fun G => ∀ u v : X, u ≠ v → Decisive F (G : Set N) u v
  have hUniv : AllDecisive Finset.univ := fun u v _ P hP hG =>
    hPar hP u v fun i => hG i (by simp)
  have hEmpty : ¬ AllDecisive ∅ := by
    intro h
    obtain ⟨P, hP, -⟩ := exists_mem_linearProfiles_strictPart_of_lt (N := N) (X := X) 0
    have h₁ := h a b hab P hP (by simp)
    have h₂ := h b a hab.symm P hP (by simp)
    exact h₁.asymm h₂
  have hInd : ∀ n : ℕ, ∀ G : Finset N, G.card = n + 1 → AllDecisive G →
      ∃ i, AllDecisive {i} := by
    intro n
    induction n with
    | zero =>
      intro G hG hD
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hG
      exact ⟨i, hD⟩
    | succ n ih =>
      intro G hG hD
      obtain ⟨i, hi⟩ : G.Nonempty := Finset.card_pos.1 (by omega)
      rcases decisive_singleton_or_decisive_erase hF hPar hIIA hX hab hac hbc hD hi with h | h
      · exact ⟨i, by simpa [AllDecisive] using h⟩
      · exact ih (G.erase i) (by rw [Finset.card_erase_of_mem hi]; omega) h
  have hcard : Finset.univ.card ≠ 0 := fun h0 => hEmpty (by
    rw [Finset.card_eq_zero] at h0; rw [← h0]; exact hUniv)
  obtain ⟨i, hi⟩ := hInd (Finset.univ.card - 1) Finset.univ (by omega) hUniv
  refine ⟨i, fun P hP => funext₂ fun x y => propext ?_⟩
  by_cases hxy : x = y
  · subst hxy
    exact ⟨fun _ => (hP.1 i).refl x, fun _ => (hF P hP).refl x⟩
  · rcases strictPart_or_strictPart_of_mem_linearProfiles hP hxy i with h | h
    · exact ⟨fun _ => h.1, fun _ => (hi x y hxy P hP (by simpa using h)).1⟩
    · exact ⟨fun h' => ((hi y x (Ne.symm hxy) P hP (by simpa using h)).2 h').elim,
        fun h' => (h.2 h').elim⟩

/-- Osborne and Rubinstein's Proposition 20.1: with finitely many agents and three distinct
alternatives, a social welfare function whose social relation is a preference relation at every
linear profile satisfies the Pareto property and independence of irrelevant alternatives on the
linear profiles if and only if it is dictatorial there. -/
theorem isParetoOn_and_isIIAOn_iff_isDictatorialOn [Finite N] {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hF : ∀ P ∈ linearProfiles N X, IsPreferenceRelation (F P)) :
    IsParetoOn F (linearProfiles N X) ∧ IsIIAOn F (linearProfiles N X) ↔
      IsDictatorialOn F (linearProfiles N X) :=
  ⟨fun h => isDictatorialOn_of_isParetoOn_of_isIIAOn hab hac hbc hF h.1 h.2,
    fun ⟨_, hi⟩ => ⟨hi.isParetoOn, hi.isIIAOn⟩⟩

/-- **Arrow's impossibility theorem** for a finite type of at least three alternatives. -/
theorem isDictatorialOn_of_isParetoOn_of_isIIAOn_of_two_lt_card [Finite N] [Fintype X]
    (hX : 2 < Fintype.card X) (hF : ∀ P ∈ linearProfiles N X, IsPreferenceRelation (F P))
    (hPar : IsParetoOn F (linearProfiles N X)) (hIIA : IsIIAOn F (linearProfiles N X)) :
    IsDictatorialOn F (linearProfiles N X) := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 hX
  exact isDictatorialOn_of_isParetoOn_of_isIIAOn hab hac hbc hF hPar hIIA

end MathEconLib.SocialChoice

/-! ### Worked examples -/

section Examples

open MathEconLib.Preference MathEconLib.SocialChoice

/-- Majority rule with three agents and three alternatives is Pareto and independent of irrelevant
alternatives but not dictatorial on the linear profiles: by Arrow's theorem its social relation is
not always a preference relation (the Condorcet paradox). -/
example : ¬ ∀ P ∈ linearProfiles (Fin 3) (Fin 3), IsPreferenceRelation (majority P) := by
  intro hF
  obtain ⟨i, hi⟩ := isDictatorialOn_of_isParetoOn_of_isIIAOn (N := Fin 3) (a := (0 : Fin 3))
    (b := 1) (c := 2) (by decide) (by decide) (by decide) hF (isParetoOn_majority _)
    (isIIAOn_majority _)
  -- Agents `j, k ≠ i` both rank `1 ≻ 0` while `i` ranks `0 ≻ 1`: majority ranks `1 ≻ 0`.
  classical
  obtain ⟨P, hP, hr⟩ := exists_mem_linearProfiles_strictPart_of_lt (N := Fin 3) (X := Fin 3)
    fun j z => if j = i then (if z = 0 then 1 else 0) else (if z = 1 then 1 else 0)
  have h₀ : StrictPart (P i) 0 1 := hr i 0 1 (by simp)
  have h₁ : ∀ j, j ≠ i → StrictPart (P j) 1 0 := fun j hj => hr j 1 0 (by simp [hj])
  have hs : supporters P 1 0 = Finset.univ.erase i :=
    supporters_eq_of_forall (fun j hj => h₁ j (Finset.ne_of_mem_erase hj))
      (fun j hj => by
        have : j = i := by by_contra h; exact hj (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩)
        exact this ▸ h₀)
  have hsum := card_supporters_add_card_supporters hP (x := (1 : Fin 3)) (y := 0) (by decide)
  have hcard : (supporters P 1 0).card = 2 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _)]; rfl
  have hmaj : StrictPart (majority P) 1 0 := by
    rw [strictPart_majority_iff]; rw [Fintype.card_fin] at hsum; omega
  rw [hi hP] at hmaj
  exact h₀.asymm hmaj

end Examples
