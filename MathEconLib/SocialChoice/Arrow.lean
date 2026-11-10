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

With finitely many agents and three distinct alternatives, a Pareto and IIA social welfare
function is dictatorial on the linear profiles.

## Main statements

* `isDictatorialOn_of_isParetoOn_of_isIIAOn`: **Arrow's impossibility theorem**.
* `isParetoOn_and_isIIAOn_iff_isDictatorialOn`: Osborne and Rubinstein's Proposition 20.1.
* `isDictatorialOn_of_isParetoOn_of_isIIAOn_of_two_lt_card`: Arrow's theorem for a finite type of
  at least three alternatives.

## References

* K. J. Arrow, *Social Choice and Individual Values*, Wiley (1951)
* A. K. Sen, *Collective Choice and Social Welfare*, Holden-Day (1970), Chapter 3* (the proof)
* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Proposition 20.1
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preferences

universe u v

variable {N : Type u} {X : Type v} {F : SocialWelfareFunction N X}

/-- Closes a comparison of two ranks written with `if … then … else`. -/
local macro "rank_tac" : tactic => `(tactic| (split_ifs <;> first | omega | contradiction))

/-- `G` is decisive for `x` against `y`: if all of `G` prefer `x` to `y`, so does society. -/
private def Decisive (F : SocialWelfareFunction N X) (G : Set N) (x y : X) : Prop :=
  ∀ P ∈ linearProfiles N X, (∀ i ∈ G, y ≺[P i] x) → y ≺[F P] x

/-- `G` is decisive for `x` against `y` at the linear profiles where everyone outside `G` strictly
prefers `y` to `x`. -/
private def WeaklyDecisive (F : SocialWelfareFunction N X) (G : Set N) (x y : X) : Prop :=
  ∀ P ∈ linearProfiles N X, (∀ i ∈ G, y ≺[P i] x) → (∀ i ∉ G, x ≺[P i] y) → y ≺[F P] x

private theorem weaklyDecisive_of_decisive {G : Set N} {x y : X} (h : Decisive F G x y) :
    WeaklyDecisive F G x y :=
  fun P hP hG _ => h P hP hG

/-- Field expansion: weakly decisive for `a` against `b` gives decisive for `a` against `c`. -/
private theorem decisive_left_of_weaklyDecisive
    (hPar : IsParetoOn F (linearProfiles N X)) (hIIA : IsIIAOn F (linearProfiles N X))
    {G : Set N} {a b c : X} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hW : WeaklyDecisive F G a b) : Decisive F G a c := by
  classical
  intro P hP hG
  let r : N → X → ℕ := fun i z =>
    if i ∈ G then (if z = a then 3 else if z = b then 2 else if z = c then 1 else 0)
    else (if z = b then 3 else if z = a then (if c ≺[P i] a then 2 else 1)
      else if z = c then (if c ≺[P i] a then 1 else 2) else 0)
  have ra : ∀ i, r i a = if i ∈ G then 3 else if c ≺[P i] a then 2 else 1 :=
    fun i => by simp [r, hab]
  have rb : ∀ i, r i b = if i ∈ G then 2 else 3 := fun i => by simp [r, hab.symm]
  have rc : ∀ i, r i c = if i ∈ G then 1 else if c ≺[P i] a then 1 else 2 :=
    fun i => by simp [r, hca, hcb]
  obtain ⟨Q, hQ, hr⟩ := exists_mem_linearProfiles_lt_of_lt r
  have h₁ : b ≺[F Q] a := hW Q hQ
    (fun i hi => hr i a b (by rw [ra, rb]; rank_tac))
    (fun i hi => hr i b a (by rw [ra, rb]; rank_tac))
  have h₂ : c ≺[F Q] b := hPar hQ b c fun i => hr i b c (by rw [rb, rc]; rank_tac)
  have h₃ : c ≺[F Q] a := (F Q).lt_trans h₂ h₁
  refine (hIIA.lt_iff_of_lt_iff subset_rfl hQ hP hca.symm fun i => ?_).1 h₃
  by_cases hi : i ∈ G
  · exact ⟨fun _ => hG i hi, fun _ => hr i a c (by rw [ra, rc]; rank_tac)⟩
  · by_cases hs : c ≺[P i] a
    · exact ⟨fun _ => hs, fun _ => hr i a c (by rw [ra, rc]; rank_tac)⟩
    · exact ⟨fun h => ((Q i).lt_asymm (hr i c a (by rw [ra, rc]; rank_tac)) h).elim,
        fun h => (hs h).elim⟩

/-- Field expansion: weakly decisive for `a` against `b` gives decisive for `c` against `b`. -/
private theorem decisive_right_of_weaklyDecisive
    (hPar : IsParetoOn F (linearProfiles N X)) (hIIA : IsIIAOn F (linearProfiles N X))
    {G : Set N} {a b c : X} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hW : WeaklyDecisive F G a b) : Decisive F G c b := by
  classical
  intro P hP hG
  let r : N → X → ℕ := fun i z =>
    if i ∈ G then (if z = c then 3 else if z = a then 2 else if z = b then 1 else 0)
    else (if z = a then 1 else if z = b then (if b ≺[P i] c then 2 else 3)
      else if z = c then (if b ≺[P i] c then 3 else 2) else 0)
  have ra : ∀ i, r i a = if i ∈ G then 2 else 1 := fun i => by simp [r, hca.symm]
  have rb : ∀ i, r i b = if i ∈ G then 1 else if b ≺[P i] c then 2 else 3 :=
    fun i => by simp [r, hcb.symm, hab.symm]
  have rc : ∀ i, r i c = if i ∈ G then 3 else if b ≺[P i] c then 3 else 2 :=
    fun i => by simp [r, hca, hcb]
  obtain ⟨Q, hQ, hr⟩ := exists_mem_linearProfiles_lt_of_lt r
  have h₁ : a ≺[F Q] c := hPar hQ c a fun i => hr i c a (by rw [ra, rc]; rank_tac)
  have h₂ : b ≺[F Q] a := hW Q hQ
    (fun i hi => hr i a b (by rw [ra, rb]; rank_tac))
    (fun i hi => hr i b a (by rw [ra, rb]; rank_tac))
  have h₃ : b ≺[F Q] c := (F Q).lt_trans h₂ h₁
  refine (hIIA.lt_iff_of_lt_iff subset_rfl hQ hP hcb fun i => ?_).1 h₃
  by_cases hi : i ∈ G
  · exact ⟨fun _ => hG i hi, fun _ => hr i c b (by rw [rb, rc]; rank_tac)⟩
  · by_cases hs : b ≺[P i] c
    · exact ⟨fun _ => hs, fun _ => hr i c b (by rw [rb, rc]; rank_tac)⟩
    · exact ⟨fun h => ((Q i).lt_asymm (hr i b c (by rw [rb, rc]; rank_tac)) h).elim,
        fun h => (hs h).elim⟩

/-- Field expansion: a coalition weakly decisive for one pair is decisive for every pair. -/
private theorem decisive_of_weaklyDecisive
    (hPar : IsParetoOn F (linearProfiles N X)) (hIIA : IsIIAOn F (linearProfiles N X))
    (hX : ∀ u v : X, ∃ w, w ≠ u ∧ w ≠ v) {G : Set N} {x y : X} (hxy : x ≠ y)
    (hW : WeaklyDecisive F G x y) {u v : X} (huv : u ≠ v) : Decisive F G u v := by
  have L := fun {a b c : X} => @decisive_left_of_weaklyDecisive N X F hPar hIIA G a b c
  have R := fun {a b c : X} => @decisive_right_of_weaklyDecisive N X F hPar hIIA G a b c
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
  obtain ⟨P, hP, hr⟩ := exists_mem_linearProfiles_lt_of_lt r
  have hPab : b ≺[F P] a := hG a b hab P hP fun j hj => hr j a b (by
    have : j ∈ G := hj
    rw [ra, rb]; rank_tac)
  by_cases hac' : c ≺[F P] a
  · left
    refine fun u v huv =>
      decisive_of_weaklyDecisive hPar hIIA hX hac (fun Q hQ h₁ h₂ => ?_) huv
    refine (hIIA.lt_iff_of_lt_iff subset_rfl hP hQ hac fun j => ?_).1 hac'
    by_cases hj : j = i
    · subst hj
      exact ⟨fun _ => h₁ j rfl, fun _ => hr j a c (by rw [ra, rc]; rank_tac)⟩
    · have hQj := h₂ j hj
      have hPj : a ≺[P j] c := hr j c a (by rw [ra, rc]; rank_tac)
      exact ⟨fun h => ((P j).lt_asymm hPj h).elim, fun h => ((Q j).lt_asymm hQj h).elim⟩
  · right
    have hca : a ≼[F P] c := (F P).not_lt.1 hac'
    have hcb : b ≺[F P] c := (F P).lt_of_lt_of_le hPab hca
    refine fun u v huv =>
      decisive_of_weaklyDecisive hPar hIIA hX hbc.symm (fun Q hQ h₁ h₂ => ?_) huv
    refine (hIIA.lt_iff_of_lt_iff subset_rfl hP hQ hbc.symm fun j => ?_).1 hcb
    by_cases hj : j ∈ G.erase i
    · have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hjG : j ∈ G := Finset.mem_of_mem_erase hj
      exact ⟨fun _ => h₁ j hj, fun _ => hr j c b (by rw [rb, rc]; rank_tac)⟩
    · have hQj := h₂ j hj
      have hjG : j = i ∨ j ∉ G := by
        by_cases hji : j = i
        · exact Or.inl hji
        · exact Or.inr fun h => hj (Finset.mem_erase.2 ⟨hji, h⟩)
      have hPj : c ≺[P j] b := hr j b c (by
        rw [rb, rc]
        rcases hjG with hjG | hjG <;> rank_tac)
      exact ⟨fun h => ((P j).lt_asymm hPj h).elim, fun h => ((Q j).lt_asymm hQj h).elim⟩

/-- **Arrow's impossibility theorem**: a Pareto, IIA social welfare function on linear profiles,
with finitely many agents and three alternatives, is dictatorial. -/
theorem isDictatorialOn_of_isParetoOn_of_isIIAOn [Finite N] {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hPar : IsParetoOn F (linearProfiles N X))
    (hIIA : IsIIAOn F (linearProfiles N X)) :
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
    obtain ⟨P, hP, -⟩ := exists_mem_linearProfiles_lt_of_lt (N := N) (X := X) 0
    have h₁ := h a b hab P hP (by simp)
    have h₂ := h b a hab.symm P hP (by simp)
    exact (F P).lt_asymm h₁ h₂
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
      rcases decisive_singleton_or_decisive_erase hPar hIIA hX hab hac hbc hD hi with h | h
      · exact ⟨i, by simpa [AllDecisive] using h⟩
      · exact ih (G.erase i) (by rw [Finset.card_erase_of_mem hi]; omega) h
  have hcard : Finset.univ.card ≠ 0 := fun h0 => hEmpty (by
    rw [Finset.card_eq_zero] at h0; rw [← h0]; exact hUniv)
  obtain ⟨i, hi⟩ := hInd (Finset.univ.card - 1) Finset.univ (by omega) hUniv
  refine ⟨i, fun P hP => CompletePreference.ext fun x y => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    exact ⟨fun _ => (P i).le_refl x, fun _ => (F P).le_refl x⟩
  · rcases lt_or_gt_of_mem_linearProfiles hP hxy i with h | h
    · exact ⟨fun h' => ((hi x y hxy P hP (by simpa using h)).2 h').elim,
        fun h' => (h.2 h').elim⟩
    · exact ⟨fun _ => h.1, fun _ => (hi y x (Ne.symm hxy) P hP (by simpa using h)).1⟩

/-- Osborne and Rubinstein's **Proposition 20.1**: on linear profiles, Pareto and IIA hold iff the
rule is dictatorial. -/
theorem isParetoOn_and_isIIAOn_iff_isDictatorialOn [Finite N] {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    IsParetoOn F (linearProfiles N X) ∧ IsIIAOn F (linearProfiles N X) ↔
      IsDictatorialOn F (linearProfiles N X) :=
  ⟨fun h => isDictatorialOn_of_isParetoOn_of_isIIAOn hab hac hbc h.1 h.2,
    fun ⟨_, hi⟩ => ⟨hi.isParetoOn, hi.isIIAOn⟩⟩

/-- **Arrow's impossibility theorem** for a finite type of at least three alternatives. -/
theorem isDictatorialOn_of_isParetoOn_of_isIIAOn_of_two_lt_card [Finite N] [Fintype X]
    (hX : 2 < Fintype.card X) (hPar : IsParetoOn F (linearProfiles N X))
    (hIIA : IsIIAOn F (linearProfiles N X)) :
    IsDictatorialOn F (linearProfiles N X) := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 hX
  exact isDictatorialOn_of_isParetoOn_of_isIIAOn hab hac hbc hPar hIIA

end MathEconLib.SocialChoice

/-! ### Worked examples -/

section Examples

open MathEconLib.Preferences MathEconLib.SocialChoice

/-- By Arrow's theorem, no social welfare function agrees with majority rule on every linear
profile of three agents over three alternatives. -/
example : ¬ ∃ F : SocialWelfareFunction (Fin 3) (Fin 3),
    ∀ P ∈ linearProfiles (Fin 3) (Fin 3), ∀ x y : Fin 3, x ≼[F P] y ↔ majority P x y := by
  rintro ⟨F, hF⟩
  have hPar : IsParetoOn F (linearProfiles (Fin 3) (Fin 3)) := fun P hP x y h =>
    (F P).not_le.1 fun h' => not_majority_of_forall_lt h ((hF P hP x y).1 h')
  have hIIA : IsIIAOn F (linearProfiles (Fin 3) (Fin 3)) := fun P hP Q hQ x y h => by
    rw [hF P hP, hF Q hQ]
    exact majority_congr h
  obtain ⟨i, hi⟩ := isDictatorialOn_of_isParetoOn_of_isIIAOn (N := Fin 3) (a := (0 : Fin 3))
    (b := 1) (c := 2) (by decide) (by decide) (by decide) hPar hIIA
  -- Agents `j, k ≠ i` both rank `1` above `0` while `i` ranks `0` above `1`: a majority prefers
  -- `1` to `0`, against the dictator.
  classical
  obtain ⟨P, hP, hr⟩ := exists_mem_linearProfiles_lt_of_lt (N := Fin 3) (X := Fin 3)
    fun j z => if j = i then (if z = 0 then 1 else 0) else (if z = 1 then 1 else 0)
  have h₀ : (1 : Fin 3) ≺[P i] 0 := hr i 0 1 (by simp)
  have h₁ : ∀ j, j ≠ i → (0 : Fin 3) ≺[P j] 1 := fun j hj => hr j 1 0 (by simp [hj])
  have hs : supporters P 1 0 = Finset.univ.erase i :=
    supporters_eq_of_forall (fun j hj => h₁ j (Finset.ne_of_mem_erase hj))
      (fun j hj => by
        have : j = i := by by_contra h; exact hj (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩)
        exact this ▸ h₀)
  have hsum := card_supporters_add_card_supporters hP (x := (1 : Fin 3)) (y := 0) (by decide)
  have hcard : (supporters P 1 0).card = 2 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _)]; rfl
  have hmaj : ¬ majority P 1 0 := by
    rw [not_majority_iff]; rw [Fintype.card_fin] at hsum; omega
  exact hmaj ((hF P hP 1 0).1 (by rw [hi hP]; exact h₀.1))

end Examples
