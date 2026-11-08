/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Contracts.JointPreservation
public import MathEconLibExamples.Matching.JointPreservationRules

import Mathlib.Tactic.FinCases

/-!
# Three stable allocations that cannot all survive completion

One hospital and three doctors trade two terms per doctor. Each doctor prefers
their `b` term. In target `i`, doctor `i` takes their `a` term and the other
doctors take their `b` terms. Every target is stable under the original rule.
For each omitted target, a substitutable, consistent, size-monotone completion
preserves the other two. Any substitutable completion preserving all three would reject all
the `b` terms at the full menu, contrary to the original full-menu choice.

The stability notion is the existing choice-theoretic one. A new contract can
block when the completed buyer chooses it alongside the doctor's current term.
See Hatfield and Kominers (2019), *Hidden Substitutes*, Appendix A, Example A.1,
for a two-doctor example where different completions give different stable sets.
https://johnhatfield.squarespace.com/s/Hidden-Substitutes.pdf
-/

@[expose] public section

open MathEconLib.Choice MathEconLib.Matching

namespace MathEconLib.Examples.Matching.JointPreservation

open Contract

/-- The term each doctor strictly prefers to their other term and being unmatched. -/
def preferred : Fin 3 → Contract
  | 0 => b1
  | 1 => b2
  | 2 => b3

/-- The other term, which is still preferable to being unmatched. -/
def lessPreferred : Fin 3 → Contract
  | 0 => a1
  | 1 => a2
  | 2 => a3

@[simp] private theorem worker_preferred (i : Fin 3) : worker (preferred i) = i := by
  fin_cases i <;> rfl

private theorem term_cases (x : Contract) :
    x = preferred (worker x) ∨ x = lessPreferred (worker x) := by
  cases x <;> decide

/-- Doctors choose their best available own term, with both terms acceptable. -/
def sellerChoice (i : Fin 3) : ChoiceFunction Contract where
  toFun Y := {x ∈ Y | worker x = i ∧ (x = preferred i ∨ preferred i ∉ Y)}
  choose_subset _ _ hx := hx.1

/-- Each doctor chooses at most one contract. -/
theorem sellerChoice_unitDemand (i : Fin 3) : (sellerChoice i).UnitDemand := by
  intro Y x hx y hy
  change x ∈ Y ∧ worker x = i ∧ (x = preferred i ∨ preferred i ∉ Y) at hx
  change y ∈ Y ∧ worker y = i ∧ (y = preferred i ∨ preferred i ∉ Y) at hy
  by_cases h : preferred i ∈ Y
  · exact (hx.2.2.resolve_right (fun hnot ↦ hnot h)).trans
      (hy.2.2.resolve_right (fun hnot ↦ hnot h)).symm
  · have hx' : x = lessPreferred i := by
      have ht := term_cases x
      rw [hx.2.1] at ht
      exact ht.resolve_left (fun heq ↦ h (heq ▸ hx.1))
    have hy' : y = lessPreferred i := by
      have ht := term_cases y
      rw [hy.2.1] at ht
      exact ht.resolve_left (fun heq ↦ h (heq ▸ hy.1))
    exact hx'.trans hy'.symm

/-- Dropping rejected offers keeps the doctor's favorite available term. -/
theorem sellerChoice_consistent (i : Fin 3) : (sellerChoice i).Consistent := by
  intro Y Z hchoice hYZ
  apply Set.Subset.antisymm
  · intro x hx
    change x ∈ Z ∧ worker x = i ∧ (x = preferred i ∨ preferred i ∉ Z) at hx
    refine ⟨hYZ hx.1, hx.2.1, hx.2.2.imp_right ?_⟩
    intro hnot hmem
    exact hnot (hchoice (show preferred i ∈ sellerChoice i Y from
      ⟨hmem, worker_preferred i, Or.inl rfl⟩))
  · intro x hx
    change x ∈ Y ∧ worker x = i ∧ (x = preferred i ∨ preferred i ∉ Y) at hx
    exact ⟨hchoice hx, hx.2.1, hx.2.2.imp_right (fun hnot hmem ↦ hnot (hYZ hmem))⟩

/-- The three-doctor market with an arbitrary choice rule for the hospital. -/
def marketOfBuyerChoice (C : ChoiceFunction Contract) :
    Market Unit (Fin 3) Contract where
  buyer _ := ()
  seller := worker
  choiceB _ := C
  choiceS := sellerChoice
  buyer_eq_of_mem := fun {b _ _} _ ↦ Subsingleton.elim _ b
  seller_eq_of_mem := fun {_ _ _} hx ↦ hx.2.1

/-- The original one-hospital market. -/
def market : Market Unit (Fin 3) Contract := marketOfBuyerChoice original

/-- The market with the hospital's rule replaced by the specified completion. -/
def completedMarket (D : ChoiceFunction Contract) (hcomp : original.IsCompletionOf worker D)
    (hsub : D.Substitutable) : Market Unit (Fin 3) Contract :=
  market.withBuyerCompletions (fun _ ↦ D) (fun _ ↦ hcomp) (fun _ ↦ hsub)

/-- Target `i` assigns the less preferred term to `i` and preferred terms to all other doctors. -/
def target (i : Fin 3) : Set Contract :=
  {x | if worker x = i then x = lessPreferred i else x = preferred (worker x)}

private theorem preferred_not_mem_target (i : Fin 3) : preferred i ∉ target i := by
  fin_cases i <;> simp [target, worker, preferred, lessPreferred]

/-- Each target assigns at most one term to each doctor. -/
theorem target_feasible (i : Fin 3) : Set.InjOn worker (target i) := by
  intro x hx y hy hxy
  change (if worker x = i then x = lessPreferred i else x = preferred (worker x)) at hx
  change (if worker y = i then y = lessPreferred i else y = preferred (worker y)) at hy
  rw [← hxy] at hy
  split at hx
  · rename_i h
    rw [ite_eq_left h] at hy
    exact hx.trans hy.symm
  · rename_i h
    rw [ite_eq_right h] at hy
    exact hx.trans hy.symm

private theorem sellerChoice_target (s i : Fin 3) :
    sellerChoice s (target i) = {x ∈ target i | worker x = s} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, hx.2.1⟩
  · rintro ⟨hx, hxs⟩
    refine ⟨hx, hxs, ?_⟩
    change (if worker x = i then x = lessPreferred i else x = preferred (worker x)) at hx
    by_cases h : worker x = i
    · right
      rw [← hxs, h]
      exact preferred_not_mem_target i
    · left
      rw [← hxs]
      rwa [ite_eq_right h] at hx

private theorem preferred_chosen_on_offer (i : Fin 3) :
    preferred i ∈ sellerChoice (worker (preferred i)) (insert (preferred i) (target i)) :=
  ⟨Set.mem_insert _ _, rfl, Or.inl (by rw [worker_preferred])⟩

private theorem new_chosen_offer_eq_preferred {i : Fin 3} {x : Contract} {Y : Set Contract}
    (hY : target i ⊆ Y) (hx : x ∉ target i) (hchoose : x ∈ sellerChoice (worker x) Y) :
    x = preferred i := by
  by_cases hi : worker x = i
  · rcases term_cases x with h | h
    · simpa only [hi] using h
    · apply (hx ?_).elim
      change (if worker x = i then x = lessPreferred i else x = preferred (worker x))
      rw [ite_eq_left hi]
      simpa only [hi] using h
  · have hpreferred : preferred (worker x) ∈ target i := by
      change (if worker (preferred (worker x)) = i
        then preferred (worker x) = lessPreferred i
        else preferred (worker x) = preferred (worker (preferred (worker x))))
      simp only [worker_preferred, ite_eq_right hi]
    have hchoice : x = preferred (worker x) ∨ preferred (worker x) ∉ Y := hchoose.2.2
    have heq := hchoice.resolve_right (fun hnot ↦ hnot (hY hpreferred))
    exact (hx (heq ▸ hpreferred)).elim

private theorem stable_target_of_rejection (C : ChoiceFunction Contract) (i : Fin 3)
    (hchoice : C (target i) = target i)
    (hreject : preferred i ∉ C (insert (preferred i) (target i))) :
    (marketOfBuyerChoice C).Stable (target i) := by
  let N := marketOfBuyerChoice C
  have hIR : N.IndRational (target i) := by
    refine ⟨?_, fun s ↦ sellerChoice_target s i⟩
    intro b
    rw [show N.choiceB b (target i) = C (target i) from rfl, hchoice]
    ext x
    exact ⟨fun hx ↦ ⟨hx, Subsingleton.elim _ _⟩, fun hx ↦ hx.1⟩
  refine ⟨hIR, fun Z hblock ↦ ?_⟩
  obtain ⟨x, hx⟩ := hblock.1
  have heq {z : Contract} (hz : z ∈ Z) : z = preferred i :=
    new_chosen_offer_eq_preferred Set.subset_union_left
      (Set.disjoint_left.mp hblock.2.1 hz) (hblock.2.2.2 (worker z) ⟨hz, rfl⟩)
  have hZ : Z = {preferred i} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨heq hx ▸ hx, fun _ hz ↦ heq hz⟩
  rw [hZ] at hblock
  exact hreject (N.blocks_singleton_iff.mp hblock).2.1

private theorem original_rejects_preferred (i : Fin 3) :
    preferred i ∉ original (insert (preferred i) (target i)) := by
  fin_cases i <;> simp [target, worker, preferred, lessPreferred, originalAccepts]

/-- Each of the three targets is stable under the original choice rules. -/
theorem target_stable (i : Fin 3) : market.Stable (target i) :=
  stable_target_of_rejection original i (original_apply_of_feasible (target_feasible i))
    (original_rejects_preferred i)

private theorem pairCompletion_rejects_preferred {i j : Fin 3} (hij : i ≠ j) :
    preferred i ∉ pairCompletion j (insert (preferred i) (target i)) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [target, worker, preferred, lessPreferred, pairAccepts]

/-- The completion indexed by `j` preserves every other target. -/
theorem target_stable_under_pairCompletion {i j : Fin 3} (hij : i ≠ j) :
    (completedMarket (pairCompletion j) (pairCompletion_isCompletion j)
      (pairCompletion_substitutable j)).Stable (target i) := by
  apply stable_target_of_rejection (pairCompletion j) i
  · exact ((pairCompletion_isCompletion j).eq_of_injOn_menu (target_feasible i)).trans
      (original_apply_of_feasible (target_feasible i))
  · exact pairCompletion_rejects_preferred hij

/-- Each pair survives under one substitutable IRC completion with aggregate demand. -/
theorem pair_preserved {i j : Fin 3} (hij : i ≠ j) :
    ∃ (D : ChoiceFunction Contract) (hcomp : original.IsCompletionOf worker D)
      (hsub : D.Substitutable),
      D.Consistent ∧ D.SizeMonotone ∧
        (completedMarket D hcomp hsub).Stable (target i) ∧
        (completedMarket D hcomp hsub).Stable (target j) := by
  have hthird : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by decide
  obtain ⟨k, hik, hjk⟩ := hthird i j hij
  exact ⟨pairCompletion k, pairCompletion_isCompletion k, pairCompletion_substitutable k,
    pairCompletion_consistent k, pairCompletion_lawOfAggregateDemand k,
    target_stable_under_pairCompletion hik, target_stable_under_pairCompletion hjk⟩

/-- No substitutable completion preserves all three targets. -/
theorem not_jointly_preserved (D : ChoiceFunction Contract)
    (hcomp : original.IsCompletionOf worker D) (hsub : D.Substitutable) :
    ¬ ∀ i : Fin 3, (completedMarket D hcomp hsub).Stable (target i) := by
  intro hstable
  let N := completedMarket D hcomp hsub
  have hrejected (i : Fin 3) : preferred i ∉ D Set.univ := by
    intro hfull
    have hchosen : preferred i ∈ D (insert (preferred i) (target i)) :=
      hsub.mem_of_subset (Set.subset_univ _) hfull (Set.mem_insert _ _)
    exact (hstable i).2 _ (N.blocks_singleton_iff.mpr
      ⟨preferred_not_mem_target i, hchosen, preferred_chosen_on_offer i⟩)
  have hfeasible : Set.InjOn worker (D Set.univ) := by
    intro x hx y hy hxy
    have hx' := (term_cases x).resolve_left (fun heq ↦ hrejected (worker x) (heq ▸ hx))
    have hy' := (term_cases y).resolve_left (fun heq ↦ hrejected (worker y) (heq ▸ hy))
    exact hx'.trans ((congrArg lessPreferred hxy).trans hy'.symm)
  have hb3 : b3 ∈ original (Set.univ : Set Contract) := by simp [originalAccepts]
  exact hrejected 2 ((hcomp.eq_of_injOn hfeasible).symm ▸ hb3)

section Ordinal

open Classical

/-- The best available term in one doctor's position, with vacancy last. -/
noncomputable def termRank (high low : Contract) (A : Set Contract) : ℕ :=
  if high ∈ A then 2 else if low ∈ A then 1 else 0

private theorem termRank_le_two (high low : Contract) (A : Set Contract) :
    termRank high low A ≤ 2 := by
  by_cases hh : high ∈ A <;> by_cases hl : low ∈ A <;> simp [termRank, hh, hl]

private theorem termRank_mono {high low : Contract} {A Y : Set Contract}
    (hAY : A ⊆ Y) : termRank high low A ≤ termRank high low Y := by
  by_cases hh : high ∈ A
  · simp [termRank, hh, hAY hh]
  by_cases hl : low ∈ A
  · by_cases hhigh : high ∈ Y <;> simp [termRank, hh, hl, hAY hl, hhigh]
  · simp [termRank, hh, hl]

private theorem termRank_eq_of_priority {high low : Contract} {A Y : Set Contract}
    (hh : high ∈ A ↔ high ∈ Y) (hl : low ∈ A ↔ low ∈ Y ∧ high ∉ Y) :
    termRank high low A = termRank high low Y := by
  by_cases h : high ∈ Y <;> simp [termRank, hh, hl, h]

private theorem termRank_mem_of_eq {high low : Contract} {A Y : Set Contract}
    (hA : high ∈ A → low ∉ A) (hY : high ∈ Y → low ∉ Y)
    (heq : termRank high low A = termRank high low Y) :
    (high ∈ A ↔ high ∈ Y) ∧ (low ∈ A ↔ low ∈ Y) := by
  by_cases ha : high ∈ A <;> by_cases hy : high ∈ Y <;>
    by_cases la : low ∈ A <;> by_cases ly : low ∈ Y <;> simp_all [termRank]

/-- The third coordinate reverses priority when the first two coordinates are a-terms. -/
noncomputable def thirdRank (A : Set Contract) : ℕ :=
  if a1 ∈ A ∧ a2 ∈ A then termRank b3 a3 A else termRank a3 b3 A

private theorem thirdRank_le_two (A : Set Contract) : thirdRank A ≤ 2 := by
  unfold thirdRank
  split <;> apply termRank_le_two

/-- A numerical encoding of the hospital's lexicographic ordinal ranking.
Each coordinate is in {0, 1, 2}, so its earlier coordinates take priority. -/
noncomputable def hospitalRank (A : Set Contract) : ℕ :=
  9 * termRank a1 b1 A + 3 * termRank a2 b2 A + thirdRank A

/-- The hospital chooses its unique highest-ranked feasible bundle from every menu. -/
theorem original_rank_lt_of_feasible_ne {A Y : Set Contract}
    (hA : Set.InjOn worker A) (hAY : A ⊆ Y) (hne : A ≠ original Y) :
    hospitalRank A < hospitalRank (original Y) := by
  have h1best : termRank a1 b1 (original Y) = termRank a1 b1 Y :=
    termRank_eq_of_priority (by simp [originalAccepts]) (by simp [originalAccepts])
  have h2best : termRank a2 b2 (original Y) = termRank a2 b2 Y :=
    termRank_eq_of_priority (by simp [originalAccepts]) (by simp [originalAccepts])
  have h1le : termRank a1 b1 A ≤ termRank a1 b1 (original Y) :=
    h1best ▸ termRank_mono hAY
  have h2le : termRank a2 b2 A ≤ termRank a2 b2 (original Y) :=
    h2best ▸ termRank_mono hAY
  have h2max := termRank_le_two a2 b2 A
  have h3max := thirdRank_le_two A
  unfold hospitalRank
  by_cases h1eq : termRank a1 b1 A = termRank a1 b1 (original Y)
  swap
  · omega
  by_cases h2eq : termRank a2 b2 A = termRank a2 b2 (original Y)
  swap
  · omega
  have distinct {F : Set Contract} (hf : Set.InjOn worker F) {a b : Contract}
      (hw : worker a = worker b) (hab : a ≠ b) : a ∈ F → b ∉ F :=
    fun ha hb ↦ hab (hf ha hb hw)
  have hC := original_feasible Y
  have h1 := termRank_mem_of_eq
    (distinct hA (a := a1) (b := b1) rfl (by decide))
    (distinct hC (a := a1) (b := b1) rfl (by decide)) h1eq
  have h2 := termRank_mem_of_eq
    (distinct hA (a := a2) (b := b2) rfl (by decide))
    (distinct hC (a := a2) (b := b2) rfl (by decide)) h2eq
  have hflag : (a1 ∈ A ∧ a2 ∈ A) ↔ a1 ∈ Y ∧ a2 ∈ Y := by
    rw [h1.1, h2.1]
    simp [originalAccepts]
  have hflagC : (a1 ∈ original Y ∧ a2 ∈ original Y) ↔ a1 ∈ Y ∧ a2 ∈ Y := by
    simp [originalAccepts]
  suffices h3lt : thirdRank A < thirdRank (original Y) by omega
  have lastRank {high low : Contract} (hw : worker high = worker low)
      (hne' : high ≠ low)
      (hh : high ∈ original Y ↔ high ∈ Y)
      (hl : low ∈ original Y ↔ low ∈ Y ∧ high ∉ Y)
      (hterms : (high = a3 ∧ low = b3) ∨ (high = b3 ∧ low = a3)) :
      termRank high low A < termRank high low (original Y) := by
    have hbest := termRank_eq_of_priority hh hl
    have hle : termRank high low A ≤ termRank high low (original Y) :=
      hbest ▸ termRank_mono hAY
    refine lt_of_le_of_ne hle ?_
    intro heq
    have h3 := termRank_mem_of_eq (distinct hA hw hne') (distinct hC hw hne') heq
    apply hne
    ext x
    cases x with
    | a1 => exact h1.1
    | b1 => exact h1.2
    | a2 => exact h2.1
    | b2 => exact h2.2
    | a3 =>
      rcases hterms with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h3.1
      · exact h3.2
    | b3 =>
      rcases hterms with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h3.2
      · exact h3.1
  by_cases h : a1 ∈ Y ∧ a2 ∈ Y
  · simp only [thirdRank, hflag, hflagC, ite_eq_left h]
    apply lastRank (high := b3) (low := a3) rfl (by decide)
    · simp [originalAccepts, h]
    · simp [originalAccepts, h.1, h.2]
    · exact Or.inr ⟨rfl, rfl⟩
  · simp only [thirdRank, hflag, hflagC, ite_eq_right h]
    apply lastRank (high := a3) (low := b3) rfl (by decide)
    · constructor
      · exact fun hx ↦ (mem_original.mp hx).1
      · exact fun hx ↦ mem_original.mpr ⟨hx, fun hb ↦ h ⟨hb.1, hb.2.1⟩⟩
    · simp only [mem_original, originalAccepts, h, or_false]
    · exact Or.inl ⟨rfl, rfl⟩

/-- Each doctor ranks their preferred term above the other term, and both above vacancy. -/
noncomputable def workerRank (i : Fin 3) (A : Set Contract) : ℕ :=
  termRank (preferred i) (lessPreferred i) A

/-- No distinct feasible allocation weakly improves the hospital and every doctor. -/
theorem target_paretoEfficient (i : Fin 3) {A : Set Contract}
    (hA : Set.InjOn worker A)
    (hWorkers : ∀ j, workerRank j (target i) ≤ workerRank j A)
    (hHospital : hospitalRank (target i) ≤ hospitalRank A) :
    A = target i := by
  let Y := insert (preferred i) (target i)
  have hAY : A ⊆ Y := by
    intro x hx
    by_cases hi : worker x = i
    · rcases term_cases x with heq | heq
      · exact Or.inl (heq.trans (congrArg preferred hi))
      · exact Or.inr (by simpa [target, hi] using heq)
    · have hpreferred : preferred (worker x) ∈ target i := by
        simp [target, hi]
      have hp : preferred (worker x) ∈ A := by
        have hRank := hWorkers (worker x)
        by_contra hnot
        simp only [workerRank, termRank, ite_eq_left hpreferred, ite_eq_right hnot] at hRank
        split at hRank <;> omega
      have heq : x = preferred (worker x) := hA hx hp (worker_preferred (worker x)).symm
      exact Or.inr (heq ▸ hpreferred)
  have hsub : original Y ⊆ target i := by
    intro x hx
    rcases Set.mem_insert_iff.mp (original.choose_subset Y hx) with rfl | hx
    · exact (original_rejects_preferred i hx).elim
    · exact hx
  have hchoice : original Y = target i := by
    rw [← original_consistent hsub (Set.subset_insert _ _),
      original_apply_of_feasible (target_feasible i)]
  by_contra hne
  have hlt := original_rank_lt_of_feasible_ne hA hAY (fun heq ↦ hne (heq.trans hchoice))
  exact (not_lt_of_ge hHospital) (hchoice ▸ hlt)

end Ordinal

/-- The canonical criterion passes on each pair of targets in the example. -/
theorem canonicalCompletion_pair {i j : Fin 3} (hij : i ≠ j) :
    ∀ b, (market.choiceB b).IsCompletionOf market.seller
      (market.jointPreservationChoices {target i, target j} b) := by
  have hunit : market.SellersUnitDemand := sellerChoice_unitDemand
  have hSsub (s : Fin 3) : (market.choiceS s).Substitutable :=
    (sellerChoice_unitDemand s).substitutable (sellerChoice_consistent s)
  have hIR : ∀ A ∈ ({target i, target j} : Set (Set Contract)), market.IndRational A := by
    intro A hA
    rcases Set.mem_insert_iff.mp hA with rfl | hA
    · exact (target_stable i).1
    · rw [Set.mem_singleton_iff.mp hA]
      exact (target_stable j).1
  apply (market.preservingBuyerCompletions_nonempty_iff hunit hSsub hIR).mp
  obtain ⟨D, hcomp, hsub, hcons, _, hi, hj⟩ := pair_preserved hij
  refine ⟨fun _ ↦ D, fun _ ↦ hcomp, fun _ ↦ hsub, fun _ ↦ hcons, ?_⟩
  intro A hA
  rcases Set.mem_insert_iff.mp hA with rfl | hA
  · exact hi
  · rw [Set.mem_singleton_iff.mp hA]
    exact hj

end MathEconLib.Examples.Matching.JointPreservation
