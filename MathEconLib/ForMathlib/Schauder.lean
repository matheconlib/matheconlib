/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Data.Nat.Nth

/-!
# Schauder's fixed point theorem
This file contains an auto-formalisation of Schauder's fixed point theorem, a generalisation of
Brouwer's fixed point theorem stating that every continuous map from a nonempty compact convex
subset of a Hausdorff locally convex topological vector space to itself has at least one fixed
point.

All declarations used in the proof are kept private; the only three public declarations of this
file are:
* `FiniteDimensional.locallyConvexSpace`, an instance showing that Schauder's theorem applies in
  particular in finite-dimensional Hausdorff topological vector spaces and hence generalises
  Brouwer's theorem,
* `Continuous.exists_fixedPt_of_isConvex_isCompact`, Schauder's theorem stated in terms of
  continuous maps between subtypes,
* `ContinuousOn.exists_fixedPt_of_isConvex_isCompact`, Schauder's theorem stated in terms of
  `ContinuousOn` and `Set.MapsTo`.

The formalisation is based on https://arxiv.org/abs/1902.00827 and
https://planetmath.org/proofofschauderfixedpointtheorem.
-/

-- This file is the original auto-formalisation output (see the module doc below) and has not
-- been through the library's review discipline. The Mathlib style linters are scoped off here
-- so that they give a usable signal on the hand-written parts of the library; re-enable them
-- when this file is cleaned up or replaced by an upstreamed version.
-- TODO: 116 linter findings, dominated by unused `Fintype`/`DecidableEq` instance arguments in
-- statements (42 + 29) and `show` used where `change` is meant (29). The 14 `linter.flexible`
-- findings are deliberately left visible: Mathlib forbids scoping that linter off downstream.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.show false
set_option linter.style.refine false
set_option linter.style.openClassical false

noncomputable section

open Classical

def isDominant {n : ℕ} {T : Type}
    (ords : Fin (n + 1) → LinearOrder T)
    (σ : Finset T) (C : Finset (Fin (n + 1))) : Prop :=
  ∀ y : T, ∃ i ∈ C, ∀ x ∈ σ, ¬ (ords i).lt x y

/-- Adjacency predicate on pairs (σ, C): one pair is a room and the other is
    obtained by removing an element from σ or adding an element to C. -/
def scarfAdjRel {n : ℕ} {T : Type} [DecidableEq T]
    (v w : Finset T × Finset (Fin (n + 1))) : Prop :=
  v ≠ w ∧
  ((v.1.card = v.2.card ∧
    ((∃ x ∈ v.1, w.1 = v.1.erase x ∧ w.2 = v.2) ∨
     (∃ i, i ∉ v.2 ∧ w.1 = v.1 ∧ w.2 = insert i v.2))) ∨
   (w.1.card = w.2.card ∧
    ((∃ x ∈ w.1, v.1 = w.1.erase x ∧ v.2 = w.2) ∨
     (∃ i, i ∉ w.2 ∧ v.1 = w.1 ∧ v.2 = insert i w.2))))

/-- The Scarf vertex predicate. A pair (σ, C) is a Scarf vertex (w.r.t. a
    distinguished index i₀, orders ords, and coloring c) iff C is nonempty,
    σ is dominant w.r.t. C, and one of:
    (1) colorful room: |σ| = |C| and C = σ.image c
    (2) nearly colorful room: |σ| = |C| and C \ σ.image c = {i₀}
    (3) nearly colorful door: |C| = |σ| + 1 and C \ σ.image c = {i₀} -/
def IsScarfVtx {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1)) (p : Finset T × Finset (Fin (n + 1))) : Prop :=
  p.2.Nonempty ∧ isDominant ords p.1 p.2 ∧
  ((p.1.card = p.2.card ∧ p.2 = p.1.image c) ∨
   (p.1.card = p.2.card ∧ p.2 \ p.1.image c = {i₀}) ∨
   (p.2.card = p.1.card + 1 ∧ p.2 \ p.1.image c = {i₀}))

lemma isDominant_erase {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (σ : Finset T) (C : Finset (Fin (n + 1))) (z : T)
    (hdom : isDominant ords σ C) :
    isDominant ords (σ.erase z) C := by
  intro y
  obtain ⟨i, hi, hx⟩ := hdom y
  exact ⟨i, hi, fun x hx' ↦ hx x (Finset.mem_of_mem_erase hx')⟩

-- InjOn version of image_erase

lemma image_erase_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} {s : Finset α} {a : α}
    (hinj : Set.InjOn f ↑s) (ha : a ∈ s) :
    (s.erase a).image f = (s.image f).erase (f a) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨t, ⟨ht_ne, ht_mem⟩, rfl⟩
    exact ⟨fun h ↦ ht_ne (hinj ht_mem ha h), t, ht_mem, rfl⟩
  · grind

lemma colorful_room_unique_adj_mem {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hcard : σ.card = C.card) (hcolor : C = σ.image c)
    (hdom : isDominant ords σ C) (hC : C.Nonempty)
    (hi₀ : i₀ ∈ C) :
    ∃! w : Finset T × Finset (Fin (n + 1)),
      scarfAdjRel (σ, C) w ∧ IsScarfVtx ords c i₀ w := by
  -- Step 1: c is injective on σ
  have hinj : Set.InjOn c ↑σ := by
    apply Finset.injOn_of_card_image_eq
    rw [← hcolor]; exact hcard.symm
  -- Step 2: Find x₀ ∈ σ with c(x₀) = i₀
  have hi₀_img : i₀ ∈ σ.image c := hcolor ▸ hi₀
  obtain ⟨x₀, hx₀_mem, hcx₀⟩ := Finset.mem_image.mp hi₀_img
  -- Key computations
  have herase_img : (σ.erase x₀).image c = C.erase i₀ := by
    rw [image_erase_of_injOn hinj hx₀_mem, hcolor, hcx₀]
  have hsdiff : C \ (σ.erase x₀).image c = {i₀} := by
    rw [herase_img]
    exact Finset.sdiff_erase_self hi₀
  have hcard_erase : (σ.erase x₀).card = σ.card - 1 :=
    Finset.card_erase_of_mem hx₀_mem
  have hcard_rel : C.card = (σ.erase x₀).card + 1 := by
    rw [hcard_erase]
    have : 0 < C.card := Finset.card_pos.mpr hC
    omega
  -- Existence: w = (σ.erase x₀, C)
  refine ⟨(σ.erase x₀, C), ?_, ?_⟩
  · constructor
    · -- scarfAdjRel
      constructor <;> grind
    · -- IsScarfVtx
      refine ⟨hC, isDominant_erase ords σ C x₀ hdom, ?_⟩
      right; right
      exact ⟨hcard_rel, hsdiff⟩
  · -- Uniqueness: show every neighbor w satisfying IsScarfVtx equals (σ.erase x₀, C)
    intro w ⟨hadj, hvtx⟩
    -- Unpack scarfAdjRel
    obtain ⟨hne, hadj_cases⟩ := hadj
    -- Unpack IsScarfVtx
    obtain ⟨hw2_ne, hw_dom, hvtx_cases⟩ := hvtx
    -- Simplify pair projections everywhere
    simp only [] at *
    -- Case split on scarfAdjRel disjunction
    rcases hadj_cases with ⟨_, hadj_sub⟩ | ⟨hcard_eq_w, hadj_sub⟩
    · -- First disjunction: (σ,C) is the room
      rcases hadj_sub with ⟨z, hz_mem, hw1_eq, hw2_eq⟩ | ⟨j, hj_nmem, hw1_eq, hw2_eq⟩
      · -- Case (a): w.1 = σ.erase z, w.2 = C
        have herase_z : (σ.erase z).image c = C.erase (c z) := by
          rw [image_erase_of_injOn hinj hz_mem, hcolor]
        have hcz : c z = i₀ := by
          have hcz_mem : c z ∈ C := hcolor ▸ Finset.mem_image_of_mem c hz_mem
          rcases hvtx_cases with ⟨hc1, hc2⟩ | ⟨_, hc2⟩ | ⟨_, hc2⟩
          · -- Colorful: C = (σ.erase z).image c — contradicts cardinality
            grind
          · -- Nearly colorful: C \ (σ.erase z).image c = {i₀}
            grind
          · -- Door: C \ (σ.erase z).image c = {i₀}
            rw [hw2_eq, hw1_eq, herase_z] at hc2
            rw [Finset.sdiff_erase_self hcz_mem] at hc2
            exact Finset.singleton_injective hc2
        have hz_eq : z = x₀ := hinj hz_mem hx₀_mem (hcz.trans hcx₀.symm)
        rw [hz_eq] at hw1_eq
        exact Prod.ext hw1_eq hw2_eq
      · -- Case (b): w.1 = σ, w.2 = insert j C for j ∉ C
        exfalso
        rcases hvtx_cases with ⟨_, hc2⟩ | ⟨_, hc2⟩ | ⟨_, hc2⟩
        · -- Colorful: w.2 = w.1.image c = σ.image c = C
          grind
        · -- Nearly colorful: w.2 \ w.1.image c = {i₀}
          grind
        · -- Door: same argument
          rw [hw1_eq, ← hcolor, hw2_eq] at hc2
          rw [Finset.insert_sdiff_cancel hj_nmem] at hc2
          exact hj_nmem (Finset.singleton_injective hc2 ▸ hi₀)
    · -- Second disjunction: w is the room, (σ,C) is obtained from w
      grind

/-- isDominant is monotone in C: if σ is dominant w.r.t. C and C ⊆ D, then σ is dominant w.r.t. D.
    This follows directly from the definition: for any y, there exists i ∈ C ⊆ D such that
    no x ∈ σ satisfies (ords i).lt x y.
    Uses `isDominant : ∀ y, ∃ i ∈ C, ∀ x ∈ σ, ¬ (ords i).lt x y`.
    No direct Mathlib equivalent. Searched: isDominant, dominant, monotone subset. -/
lemma isDominant_mono {n : ℕ} {T : Type}
    (ords : Fin (n + 1) → LinearOrder T)
    (σ : Finset T) (C D : Finset (Fin (n + 1)))
    (hdom : isDominant ords σ C) (hsub : C ⊆ D) :
    isDominant ords σ D := by
  intro y
  obtain ⟨i, hi, hx⟩ := hdom y
  exact ⟨i, hsub hi, hx⟩

/-- The candidate w = (σ, insert i₀ C) satisfies scarfAdjRel (σ, C) w when σ.card = C.card
    and i₀ ∉ C.

    Uses the first disjunction of scarfAdjRel with the right branch:
    v.1.card = v.2.card (i.e., σ.card = C.card), and witness i = i₀ with i₀ ∉ C,
    w.1 = σ = v.1, w.2 = insert i₀ C = insert i₀ v.2.
    The pair is distinct because insert i₀ C ≠ C (since i₀ ∉ C).
    No direct Mathlib equivalent. -/
lemma adj_insert_of_not_mem {n : ℕ} {T : Type} [DecidableEq T]
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (i₀ : Fin (n + 1))
    (hcard : σ.card = C.card) (hi₀ : i₀ ∉ C) :
    scarfAdjRel (σ, C) (σ, insert i₀ C) := by
  refine ⟨?_, Or.inl ⟨hcard, Or.inr ⟨i₀, hi₀, rfl, rfl⟩⟩⟩
  grind

/-- The candidate w = (σ, insert i₀ C) satisfies IsScarfVtx when (σ, C) is a colorful room
    with i₀ ∉ C.

    Verification:
    - (insert i₀ C).Nonempty: since C.Nonempty
    - isDominant ords σ (insert i₀ C): from isDominant ords σ C and C ⊆ insert i₀ C
    - Third disjunct: (insert i₀ C).card = σ.card + 1 (by `Finset.card_insert_of_not_mem`)
      and (insert i₀ C) \ σ.image c = {i₀} (by `Finset.insert_sdiff_cancel` since
      i₀ ∉ C = σ.image c).
    Uses `Finset.card_insert_of_not_mem : a ∉ s → (insert a s).card = s.card + 1`.
    Uses `Finset.insert_sdiff_cancel : a ∉ s → insert a s \ s = {a}`.
    No direct Mathlib equivalent. -/
lemma isScarfVtx_insert_of_not_mem {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hcard : σ.card = C.card) (hcolor : C = σ.image c)
    (hdom : isDominant ords σ C)
    (hi₀ : i₀ ∉ C) :
    IsScarfVtx ords c i₀ (σ, insert i₀ C) := by
  use Finset.insert_nonempty i₀ C, isDominant_mono ords σ C _ hdom (Finset.subset_insert i₀ C)
  grind

lemma colorful_room_unique_adj_not_mem {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hcard : σ.card = C.card) (hcolor : C = σ.image c)
    (hdom : isDominant ords σ C)
    (hi₀ : i₀ ∉ C) :
    ∃! w : Finset T × Finset (Fin (n + 1)),
      scarfAdjRel (σ, C) w ∧ IsScarfVtx ords c i₀ w := by
  refine ⟨(σ, insert i₀ C), ⟨adj_insert_of_not_mem σ C i₀ hcard hi₀,
    isScarfVtx_insert_of_not_mem ords c i₀ σ C hcard hcolor hdom hi₀⟩, ?_⟩
  intro w ⟨hadj, hvtx⟩
  have hinj : Set.InjOn c ↑σ := Finset.injOn_of_card_image_eq (by rw [← hcolor, hcard])
  obtain ⟨_, hadj'⟩ := hadj
  obtain ⟨_, _, hvtx_disj⟩ := hvtx
  -- Normalize (σ, C).1 → σ and (σ, C).2 → C in all hypotheses
  dsimp only at hadj'
  rcases hadj' with ⟨_, herase | hinsert⟩ | ⟨hwcard, herase' | hinsert'⟩
  · -- Case 1: erase case, w = (σ.erase x, C)
    obtain ⟨x, hx, hw1, hw2⟩ := herase
    exfalso
    have hcx_mem : c x ∈ C := hcolor ▸ Finset.mem_image_of_mem c hx
    have hcx_ne : c x ≠ i₀ := fun h ↦ hi₀ (h ▸ hcx_mem)
    have hpos : σ.card ≥ 1 := Finset.card_pos.mpr ⟨x, hx⟩
    rcases hvtx_disj with ⟨hcard', _⟩ | ⟨hcard', _⟩ | ⟨_, hsdiff⟩
    · rw [hw1, hw2, Finset.card_erase_of_mem hx] at hcard'; omega
    · rw [hw1, hw2, Finset.card_erase_of_mem hx] at hcard'; omega
    · have hcx_not : c x ∉ (σ.erase x).image c := by
        intro hmem
        obtain ⟨y, hy, hcy⟩ := Finset.mem_image.mp hmem
        have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
        have hyσ : y ∈ σ := (Finset.mem_erase.mp hy).2
        exact hyne (hinj (Finset.mem_coe.mpr hyσ) (Finset.mem_coe.mpr hx) hcy)
      have : c x ∈ w.2 \ w.1.image c := by
        rw [hw1, hw2]; exact Finset.mem_sdiff.mpr ⟨hcx_mem, hcx_not⟩
      rw [hsdiff] at this
      exact hcx_ne (Finset.mem_singleton.mp this)
  · -- Case 2: insert case, w = (σ, insert j C)
    obtain ⟨j, hj, hw1, hw2⟩ := hinsert
    have hsdiff_j : insert j C \ σ.image c = {j} := by
      rw [hcolor]
      exact Finset.insert_sdiff_cancel (hcolor ▸ hj)
    rcases hvtx_disj with ⟨hcard', _⟩ | ⟨_, hsdiff⟩ | ⟨_, hsdiff⟩
    · rw [hw1, hw2, Finset.card_insert_of_notMem hj] at hcard'; omega
    · grind
    · rw [hw1, hw2] at hsdiff
      rw [hsdiff_j] at hsdiff
      have hji : j = i₀ := Finset.singleton_injective hsdiff
      subst hji
      exact Prod.ext hw1 hw2
  · -- Case 3: second disjunction erase
    grind
  · -- Case 4: second disjunction insert
    grind

lemma colorful_room_unique_adj {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hcard : σ.card = C.card) (hcolor : C = σ.image c)
    (hdom : isDominant ords σ C) (hC : C.Nonempty) :
    ∃! w : Finset T × Finset (Fin (n + 1)),
      scarfAdjRel (σ, C) w ∧ IsScarfVtx ords c i₀ w := by
  by_cases hi₀ : i₀ ∈ C
  · exact colorful_room_unique_adj_mem ords c i₀ σ C hcard hcolor hdom hC hi₀
  · exact colorful_room_unique_adj_not_mem ords c i₀ σ C hcard hcolor hdom hi₀

lemma degree_one_of_unique_adj_raw {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (huniq : ∃! w : Finset T × Finset (Fin (n + 1)),
      scarfAdjRel v.val w ∧ IsScarfVtx ords c i₀ w) :
    G.degree v = 1 := by
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  obtain ⟨w₀, ⟨hadj₀, hscarf₀⟩, huniq'⟩ := huniq
  refine ⟨⟨w₀, hscarf₀⟩, (hG v ⟨w₀, hscarf₀⟩).mpr hadj₀, ?_⟩
  grind

lemma scarf_degree_colorful_room {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (hcard : v.val.1.card = v.val.2.card)
    (hcolor : v.val.2 = v.val.1.image c) :
    G.degree v = 1 :=
  degree_one_of_unique_adj_raw ords c i₀ G hG v
    (colorful_room_unique_adj ords c i₀ v.val.1 v.val.2 hcard hcolor v.property.2.1 v.property.1)

lemma nearly_colorful_image_card_cases {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (i₀ : Fin (n + 1))
    (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀}) :
    (σ.image c).card = σ.card ∨ (σ.image c).card + 1 = σ.card := by
  have h1 : (C \ σ.image c).card = 1 := by grind
  grind

/-- Given exactly two adjacent Scarf vertex pairs, the degree in the subtype graph is 2.
    Proved by constructing the neighbor finset as {w₁, w₂} and applying Finset.card_pair. -/
lemma scarf_degree_of_two_adj_pairs {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (p₁ p₂ : Finset T × Finset (Fin (n + 1)))
    (hne : p₁ ≠ p₂)
    (hp₁ : IsScarfVtx ords c i₀ p₁) (hadj₁ : scarfAdjRel v.val p₁)
    (hp₂ : IsScarfVtx ords c i₀ p₂) (hadj₂ : scarfAdjRel v.val p₂)
    (huniq : ∀ q : Finset T × Finset (Fin (n + 1)),
      IsScarfVtx ords c i₀ q → scarfAdjRel v.val q → q = p₁ ∨ q = p₂) :
    G.degree v = 2 := by
  let w₁ : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p } := ⟨p₁, hp₁⟩
  let w₂ : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p } := ⟨p₂, hp₂⟩
  have hw₁_adj : G.Adj v w₁ := by rw [hG]; exact hadj₁
  have hw₂_adj : G.Adj v w₂ := by rw [hG]; exact hadj₂
  have hw_ne : w₁ ≠ w₂ := by
    intro h; exact hne (congrArg Subtype.val h)
  have hfinset : G.neighborFinset v = {w₁, w₂} := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton, SimpleGraph.mem_neighborFinset]
    constructor <;> grind
  rw [SimpleGraph.degree, hfinset]
  exact Finset.card_pair hw_ne

lemma erase_image_eq_of_duplicate {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1))
    (σ : Finset T)
    (x y : T)
    (hy : y ∈ σ) (hne : x ≠ y) (hc : c x = c y) :
    (σ.erase x).image c = σ.image c := by
  grind

-- Key helper: if (σ.image c).card + 1 = σ.card, then c is injective on σ.erase x for
-- any x ∈ σ where c x = c y for some other y ∈ σ, and erasing preserves image.
-- This means (σ.erase x).card = (σ.erase x).image c.card = σ.image c.card = σ.card - 1.
-- If there were a third z with c z = c x, then σ.erase x would still have a collision
-- (between y and z), so its image would have < |σ.erase x| elements, contradicting
-- our knowledge that the image equals σ.image c which has exactly σ.card - 1 = |σ.erase x|
-- elements.

lemma collision_with_uniqueness {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1))
    (σ : Finset T)
    (himg : (σ.image c).card + 1 = σ.card) :
    ∃ x y, x ∈ σ ∧ y ∈ σ ∧ x ≠ y ∧ c x = c y ∧
    (∀ z ∈ σ, z ≠ x → z ≠ y → c z ≠ c x) := by
  -- Get a collision from pigeonhole
  have hlt : (σ.image c).card < σ.card := by omega
  have hmaps : Set.MapsTo c (↑σ) (↑(σ.image c)) := by
    intro a ha
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem c (Finset.mem_coe.mp ha))
  obtain ⟨x, hx, y, hy, hne, hc⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨x, y, hx, hy, hne, hc, ?_⟩
  -- Prove uniqueness: no third z with c z = c x
  intro z hz hzx hzy hcz
  -- We know (σ.erase x).image c = σ.image c (from erase_image_eq_of_duplicate)
  have heq := erase_image_eq_of_duplicate c σ x y hy hne hc
  -- So (σ.erase x).image c has the same cardinality as σ.image c
  -- But σ.erase x contains both y and z (distinct, both mapping to c x)
  -- So there's still a collision in σ.erase x
  -- This means (σ.erase x).image c has < |σ.erase x| elements
  -- But |σ.erase x| = σ.card - 1 = (σ.image c).card = |(σ.erase x).image c|
  -- Wait, that means (σ.erase x).image c has exactly |σ.erase x| elements
  -- which would require injectivity on σ.erase x, contradicting the collision y,z
  have hcard_erase : (σ.erase x).card = σ.card - 1 :=
    Finset.card_erase_of_mem hx
  -- So |(σ.erase x).image c| = |σ.image c| = σ.card - 1 = |σ.erase x|
  have hcard_eq : ((σ.erase x).image c).card = (σ.erase x).card := by
    rw [heq, hcard_erase]; omega
  -- This means c is injective on σ.erase x
  have hinj : Set.InjOn c (↑(σ.erase x)) :=
    Finset.injOn_of_card_image_eq hcard_eq
  -- But y, z ∈ σ.erase x (both ≠ x) and c y = c z
  have hy' : y ∈ σ.erase x := Finset.mem_erase.mpr ⟨hne.symm, hy⟩
  have hz' : z ∈ σ.erase x := Finset.mem_erase.mpr ⟨hzx, hz⟩
  have hyz_eq : c y = c z := by rw [← hc, ← hcz]
  -- So y = z by injectivity, but y ≠ z
  exact hzy.symm (hinj hy' hz' hyz_eq)

lemma noninjective_pair_exists {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1))
    (σ : Finset T)
    (himg : (σ.image c).card + 1 = σ.card) :
    ∃ x y, x ∈ σ ∧ y ∈ σ ∧ x ≠ y ∧ c x = c y ∧
    (∀ z ∈ σ, z ≠ x → z ≠ y → c z ≠ c x) ∧
    (σ.erase x).image c = σ.image c ∧
    (σ.erase y).image c = σ.image c := by
  obtain ⟨x, y, hx, hy, hne, hc, huniq⟩ := collision_with_uniqueness c σ himg
  exact ⟨x, y, hx, hy, hne, hc, huniq,
    erase_image_eq_of_duplicate c σ x y hy hne hc,
    erase_image_eq_of_duplicate c σ y x hx hne.symm hc.symm⟩

/-- If C \ σ.image c = {i₀} and |σ.image c| + 1 = |σ| = |C|, then σ.image c ⊆ C.
    From C \ σ.image c = {i₀} we get |C \ σ.image c| = 1. With |C| = |σ| = |σ.image c| + 1,
    we have |C ∩ σ.image c| = |C| - 1 = |σ.image c|. Since C ∩ σ.image c ⊆ σ.image c and
    they have the same cardinality, σ.image c = C ∩ σ.image c ⊆ C.
    Uses `Finset.card_sdiff_eq_sub : (t \ s).card = t.card - s.card` (when s ⊆ t, but here
    we use the general version or
    `Finset.card_sdiff_inter_add : (s \ t).card + (s ∩ t).card = s.card`).
    No direct Mathlib equivalent for this specific combination. -/
lemma image_subset_of_sdiff_singleton {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (i₀ : Fin (n + 1))
    (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀})
    (himg : (σ.image c).card + 1 = σ.card) :
    σ.image c ⊆ C := by
  have h₁ : (C \ σ.image c).card + (C ∩ σ.image c).card = C.card := by grind
  have h₂ : (C \ σ.image c).card = 1 := by grind
  have h₃ : (C ∩ σ.image c).card = (σ.image c).card := by grind
  have h₄ : C ∩ σ.image c = σ.image c :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right h₃.symm.le
  grind

/-- Given a nearly colorful room (σ, C) with non-injective coloring, for any z ∈ σ with
    c z unique in σ (c z ∉ (σ.erase z).image c), we have
    (C \ (σ.erase z).image c).card ≥ 2, so C \ (σ.erase z).image c ≠ {i₀}.
    This rules out (σ.erase z, C) being a Scarf vertex of the required type.
    Uses `sdiff_image_erase_card_ge_two` and `Finset.card_singleton : ({a}).card = 1`. -/
lemma not_scarf_erase_non_colliding_1 {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (i₀ : Fin (n + 1))
    (z : T) (hz : z ∈ σ)
    (hnearly : C \ σ.image c = {i₀})
    (himg_sub : σ.image c ⊆ C)
    (hz_unique : c z ∉ (σ.erase z).image c) :
    ¬ (C \ (σ.erase z).image c = {i₀}) := by
  have hc_z_in_image : c z ∈ σ.image c := by grind
  have hc_z_in_C : c z ∈ C := by grind
  have hc_z_in_diff : c z ∈ C \ (σ.erase z).image c := by grind
  grind

lemma not_scarf_insert_form {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀})
    (himg_sub : σ.image c ⊆ C)
    (j : Fin (n + 1)) (hj : j ∉ C) :
    ¬ IsScarfVtx ords c i₀ (σ, insert j C) := by
  intro ⟨_, _, h_disj⟩
  have hj_not_img : j ∉ σ.image c := fun h ↦ hj (himg_sub h)
  have hsdiff : insert j C \ σ.image c = {i₀, j} := by
    rw [Finset.insert_sdiff_of_notMem _ hj_not_img, hnearly, Finset.pair_comm]
  have hi0_ne_j : i₀ ≠ j := by grind
  have hcard2 : (insert j C \ σ.image c).card = 2 := by
    rw [hsdiff, Finset.card_pair hi0_ne_j]
  grind

/-- Given a nearly colorful room (σ, C) with non-injective coloring and the colliding pair x, y,
    any Scarf vertex q adjacent to (σ, C) must be (σ.erase x, C) or (σ.erase y, C).

    By scarfAdjRel, q is either:
    (1) (σ.erase z, C) for some z ∈ σ, or (σ, insert j C) for some j ∉ C (first disjunct),
    (2) a room q with (σ, C) as a door of q (second disjunct).

    Case (2) is impossible because it implies σ.card < C.card or σ.card = C.card - 1,
    contradicting hcard.
    Form B (σ, insert j C) is impossible by `not_scarf_insert_form`.
    Form A (σ.erase z, C) where z ∉ {x,y}: c z is unique in σ, so
    (σ.erase z).image c ⊊ σ.image c, giving |C \ (σ.erase z).image c| ≥ 2 by
    `sdiff_image_erase_card_ge_two`, which contradicts the Scarf vertex condition.

    Uses `not_scarf_insert_form`, `not_scarf_erase_non_colliding`, `sdiff_image_erase_card_ge_two`.
    Uses `Finset.card_erase_of_mem : ∀ {s a}, a ∈ s → (s.erase a).card = s.card - 1`.
    Uses `Finset.card_insert_of_not_mem : ∀ {s a}, a ∉ s → (insert a s).card = s.card + 1`.
    No direct Mathlib equivalent. -/
lemma card_erase_ne' {T : Type} [DecidableEq T] {α : Type} [DecidableEq α]
    (σ : Finset T) (C : Finset α) (z : T)
    (hz : z ∈ σ) (hcard : σ.card = C.card) (hC_ne : C.Nonempty) :
    (σ.erase z).card ≠ C.card := by
  grind

lemma image_card_eq' {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1)) (σ : Finset T) (C : Finset (Fin (n + 1)))
    (i₀ : Fin (n + 1)) (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀}) (himg_sub : σ.image c ⊆ C) :
    (σ.image c).card + 1 = σ.card := by
  have h1 : (C \ σ.image c).card = 1 := by rw [hnearly]; exact Finset.card_singleton i₀
  have h2 := Finset.card_sdiff_add_card_eq_card himg_sub
  omega

lemma image_erase_eq_of_cover' {T : Type} [DecidableEq T] {β : Type} [DecidableEq β]
    (f : T → β) (σ : Finset T) (z : T)
    (w : T) (hw : w ∈ σ.erase z) (hwz : f w = f z) :
    (σ.erase z).image f = σ.image f := by
  grind

lemma cz_unique' {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1)) (σ : Finset T) (C : Finset (Fin (n + 1)))
    (i₀ : Fin (n + 1)) (x y z : T)
    (hx : x ∈ σ) (hy : y ∈ σ) (hz : z ∈ σ)
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hcxy : c x = c y) (huniq : ∀ w ∈ σ, w ≠ x → w ≠ y → c w ≠ c x)
    (hcard : σ.card = C.card) (hnearly : C \ σ.image c = {i₀})
    (himg_sub : σ.image c ⊆ C) :
    c z ∉ (σ.erase z).image c := by
  have hcz_ne_cx : c z ≠ c x := huniq z hz hzx hzy
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨w, hw_mem, hw_eq⟩ := hmem
  by_cases hwx : w = x
  · exact hcz_ne_cx (hw_eq ▸ hwx ▸ rfl)
  by_cases hwy : w = y
  · exact hcz_ne_cx (hw_eq ▸ hwy ▸ hcxy.symm)
  have h_img_eq := image_erase_eq_of_cover' c σ z w hw_mem hw_eq
  have h_img_card := image_card_eq' c σ C i₀ hcard hnearly himg_sub
  have h_erase_card : (σ.erase z).card = σ.card - 1 := Finset.card_erase_of_mem hz
  have h_eq_card : ((σ.erase z).image c).card = (σ.erase z).card := by
    rw [h_img_eq, h_erase_card]; omega
  have h_inj := Finset.injOn_of_card_image_eq h_eq_card
  have hx_erase : x ∈ σ.erase z := Finset.mem_erase.mpr ⟨hzx.symm, hx⟩
  have hy_erase : y ∈ σ.erase z := Finset.mem_erase.mpr ⟨hzy.symm, hy⟩
  exact hxy (h_inj hx_erase hy_erase hcxy)

lemma not_scarf_vtx_erase_non_colliding' {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hC_ne : C.Nonempty)
    (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀})
    (himg_sub : σ.image c ⊆ C)
    (x y z : T) (hx : x ∈ σ) (hy : y ∈ σ) (hz : z ∈ σ)
    (hxy : x ≠ y)
    (hzx : z ≠ x) (hzy : z ≠ y)
    (hcxy : c x = c y)
    (huniq : ∀ w ∈ σ, w ≠ x → w ≠ y → c w ≠ c x) :
    ¬ IsScarfVtx ords c i₀ (σ.erase z, C) := by
  intro ⟨_, _, h⟩
  have hz_unique := cz_unique' c σ C i₀ x y z hx hy hz hxy hzx hzy hcxy huniq
    hcard hnearly himg_sub
  have hsdiff_ne := not_scarf_erase_non_colliding_1 c σ C i₀ z hz hnearly himg_sub hz_unique
  have hcard_ne := card_erase_ne' σ C z hz hcard hC_ne
  grind

lemma caseB_impossible' {n : ℕ} {T : Type} [DecidableEq T]
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hcard : σ.card = C.card)
    (q : Finset T × Finset (Fin (n + 1)))
    (hq_room : q.1.card = q.2.card)
    (hadj : (∃ x ∈ q.1, σ = q.1.erase x ∧ C = q.2) ∨
            (∃ i, i ∉ q.2 ∧ σ = q.1 ∧ C = insert i q.2)) :
    False := by
  have h_main : False := by grind
  grind

lemma ncr_noninjective_uniqueness {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hC_ne : C.Nonempty)
    (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀})
    (himg_sub : σ.image c ⊆ C)
    (x y : T) (hx : x ∈ σ) (hy : y ∈ σ) (hxy : x ≠ y)
    (hcxy : c x = c y)
    (huniq : ∀ z ∈ σ, z ≠ x → z ≠ y → c z ≠ c x) :
    ∀ q : Finset T × Finset (Fin (n + 1)),
      IsScarfVtx ords c i₀ q → scarfAdjRel (σ, C) q →
      q = (σ.erase x, C) ∨ q = (σ.erase y, C) := by
  intro q hscarf hadj
  obtain ⟨_hne, hadj⟩ := hadj
  rcases hadj with ⟨_, hforms⟩ | ⟨hqroom, hforms⟩
  · rcases hforms with ⟨z, hz, hq1, hq2⟩ | ⟨j, hj, hq1, hq2⟩
    · have hqeq : q = (σ.erase z, C) := Prod.ext (by simpa using hq1) (by simpa using hq2)
      rw [hqeq] at hscarf ⊢
      by_cases hzx : z = x
      · left; rw [hzx]
      · by_cases hzy : z = y
        · right; rw [hzy]
        · exfalso
          exact not_scarf_vtx_erase_non_colliding' ords c i₀ σ C hC_ne hcard hnearly himg_sub
            x y z hx hy hz hxy hzx hzy hcxy huniq hscarf
    · have hqeq : q = (σ, insert j C) := Prod.ext (by simpa using hq1) (by simpa using hq2)
      rw [hqeq] at hscarf
      exact absurd hscarf (not_scarf_insert_form ords c i₀ σ C hcard hnearly himg_sub j hj)
  · exact (caseB_impossible' σ C hcard q hqroom hforms).elim

lemma ncr_noninjective_two_adj_pairs {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hC_ne : C.Nonempty)
    (hdom : isDominant ords σ C)
    (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀})
    (himg : (σ.image c).card + 1 = σ.card) :
    ∃ p₁ p₂ : Finset T × Finset (Fin (n + 1)),
      p₁ ≠ p₂ ∧
      IsScarfVtx ords c i₀ p₁ ∧ scarfAdjRel (σ, C) p₁ ∧
      IsScarfVtx ords c i₀ p₂ ∧ scarfAdjRel (σ, C) p₂ ∧
      ∀ q : Finset T × Finset (Fin (n + 1)),
        IsScarfVtx ords c i₀ q → scarfAdjRel (σ, C) q → q = p₁ ∨ q = p₂ := by
  have himg_sub := image_subset_of_sdiff_singleton c σ C i₀ hcard hnearly himg
  obtain ⟨x, y, hx, hy, hxy, hcxy, huniq, himg_ex, himg_ey⟩ :=
    noninjective_pair_exists c σ himg
  refine ⟨(σ.erase x, C), (σ.erase y, C), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- p₁ ≠ p₂
    intro heq
    have : σ.erase x = σ.erase y := by exact Prod.mk.inj heq |>.1
    have : x ∈ σ.erase x := by rw [this]; exact Finset.mem_erase.mpr ⟨hxy, hx⟩
    exact (Finset.notMem_erase x σ) this
  · -- IsScarfVtx p₁
    refine ⟨hC_ne, isDominant_erase ords σ C x hdom, ?_⟩
    grind
  · -- scarfAdjRel (σ, C) p₁
    refine ⟨?_, Or.inl ⟨hcard, Or.inl ⟨x, hx, rfl, rfl⟩⟩⟩
    grind
  · -- IsScarfVtx p₂
    refine ⟨hC_ne, isDominant_erase ords σ C y hdom, ?_⟩
    grind
  · -- scarfAdjRel (σ, C) p₂
    refine ⟨?_, Or.inl ⟨hcard, Or.inl ⟨y, hy, rfl, rfl⟩⟩⟩
    grind
  · -- Uniqueness
    exact ncr_noninjective_uniqueness ords c i₀ σ C hC_ne hcard hnearly
      himg_sub x y hx hy hxy hcxy huniq

lemma scarf_degree_ncr_case_noninjective {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (hcard : v.val.1.card = v.val.2.card)
    (hnearly : v.val.2 \ v.val.1.image c = {i₀})
    (himg : (v.val.1.image c).card + 1 = v.val.1.card) :
    G.degree v = 2 := by
  obtain ⟨hC_ne, hdom, _⟩ := v.prop
  obtain ⟨p₁, p₂, hne, hp₁, hadj₁, hp₂, hadj₂, huniq⟩ :=
    ncr_noninjective_two_adj_pairs ords c i₀ v.val.1 v.val.2 hC_ne hdom hcard hnearly himg
  exact scarf_degree_of_two_adj_pairs ords c i₀ G hG v p₁ p₂ hne hp₁ hadj₁ hp₂ hadj₂ huniq

/-- In the injective case of a nearly colorful room, there exists a unique y ∈ σ
    with c(y) ∉ C, σ.image c \ C = {c y}, σ is nonempty, and for any x ∈ σ,
    c(x) ∉ (σ.erase x).image c (i.e. removing x loses color c(x)).

    From |σ.image c| = |σ| = |C| and C \ σ.image c = {i₀}, we get
    |C ∩ σ.image c| = |C| - 1 and |σ.image c \ C| = 1.
    By injectivity of c on σ (from |σ.image c| = |σ|), there's a unique y ∈ σ with c(y) ∉ C.
    The last property follows because c is injective on σ, so c(x) ∉ (σ.erase x).image c
    for any x ∈ σ.
    Uses `Finset.injOn_of_card_image_eq : ∀ {α β : Type} {s : Finset α} {f : α → β}
      [DecidableEq β], (Finset.image f s).card = s.card → Set.InjOn f ↑s`.
    No direct Mathlib equivalent for the combined statement. -/
lemma ncr_injective_unique_y {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (i₀ : Fin (n + 1))
    (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀})
    (himg : (σ.image c).card = σ.card) :
    ∃ y ∈ σ, c y ∉ C ∧ σ.image c \ C = {c y} ∧
      (∀ z ∈ σ, c z ∉ C → z = y) ∧ σ.Nonempty ∧
      (∀ x ∈ σ, c x ∉ (σ.erase x).image c) := by
  -- c is injective on σ
  have hinj : Set.InjOn c ↑σ := Finset.injOn_of_card_image_eq himg
  -- |σ.image c \ C| = 1
  have h_Csdiff : (C \ σ.image c).card = 1 := by rw [hnearly]; exact Finset.card_singleton i₀
  have h_inter_card : (σ.image c ∩ C).card = C.card - 1 := by grind
  have hCpos : 0 < C.card := by grind
  have hsdiff_card : (σ.image c \ C).card = 1 := by grind
  -- Get the unique element in σ.image c \ C
  rw [Finset.card_eq_one] at hsdiff_card
  obtain ⟨cy, hcy_eq⟩ := hsdiff_card
  have hcy_mem : cy ∈ σ.image c \ C := hcy_eq ▸ Finset.mem_singleton.mpr rfl
  have hcy_img : cy ∈ σ.image c := (Finset.mem_sdiff.mp hcy_mem).1
  have hcy_notC : cy ∉ C := (Finset.mem_sdiff.mp hcy_mem).2
  -- cy = c y for some y ∈ σ
  rw [Finset.mem_image] at hcy_img
  obtain ⟨y, hy, rfl⟩ := hcy_img
  refine ⟨y, hy, hcy_notC, hcy_eq, ?_, ⟨y, hy⟩, ?_⟩
  · -- uniqueness: if z ∈ σ and c z ∉ C, then z = y
    intro z hz hcz
    have : c z ∈ σ.image c \ C := Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem c hz, hcz⟩
    rw [hcy_eq] at this
    have hcz_eq : c z = c y := Finset.mem_singleton.mp this
    exact hinj (Finset.mem_coe.mpr hz) (Finset.mem_coe.mpr hy) hcz_eq
  · -- for all x ∈ σ, c x ∉ (σ.erase x).image c (injectivity)
    intro x hx habs
    rw [Finset.mem_image] at habs
    obtain ⟨z, hz, hzx⟩ := habs
    have hzσ : z ∈ σ := Finset.mem_of_mem_erase hz
    have hzne : z ≠ x := Finset.ne_of_mem_erase hz
    exact hzne (hinj (Finset.mem_coe.mpr hzσ) (Finset.mem_coe.mpr hx) hzx)

/-- isDominant is monotone in C: if C ⊆ D and σ is dominant wrt C, then σ is
    dominant wrt D.
    This follows directly from the definition: ∀ y, ∃ i ∈ C, ... implies
    ∀ y, ∃ i ∈ D, ... since C ⊆ D.
    No Mathlib equivalent needed; direct logical manipulation. -/
lemma isDominant_mono_C {n : ℕ} {T : Type}
    (ords : Fin (n + 1) → LinearOrder T)
    (σ : Finset T) (C D : Finset (Fin (n + 1)))
    (hCD : C ⊆ D)
    (hdom : isDominant ords σ C) :
    isDominant ords σ D := by
  intro y
  obtain ⟨i, hi, hx⟩ := hdom y
  exact ⟨i, hCD hi, hx⟩

/-- The uniqueness part of ncr_injective_two_adj_pairs: any adjacent Scarf vertex q
    must be equal to (σ.erase y, C) or (σ, insert (c y) C), where y is the unique
    element with c(y) ∉ C.

    Case B (q is room, (σ,C) is door) is eliminated because |σ| = |C| leads to
    cardinality contradictions: if σ = q.1.erase(x) then |σ| = |q.1| - 1 = |q.2| - 1
    but |σ| = |C| and q.2 = C, contradiction. If C = insert j q.2 then |C| = |q.2| + 1
    = |q.1| + 1 but |σ| = |C| and σ = q.1, contradiction.

    Case A erase: q = (σ.erase x, C). By injectivity, c(x) ∉ (σ.erase x).image c.
    If c(x) ∈ C then (C \ (σ.erase x).image c).card ≥ 2 (via sdiff_image_erase_card_ge_two
    since σ.image c ⊆ C when c is injective on σ and C \ σ.image c = {i₀} with
    |σ.image c| = |C|), failing all IsScarfVtx disjuncts. So c(x) ∉ C, giving x = y.

    Case A insert: q = (σ, insert j C). If j ∉ σ.image c then
    insert j C \ σ.image c = insert j (C \ σ.image c) = {j, i₀} has card 2, failing.
    So j ∈ σ.image c, and since j ∉ C, j ∈ σ.image c \ C = {c y}, giving j = c(y).

    Uses `Finset.insert_sdiff_of_notMem`, `Finset.insert_sdiff_of_mem`,
    reused lemma `sdiff_image_erase_card_ge_two`. -/
lemma ncr_injective_uniqueness {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀})
    (y : T) (hy : y ∈ σ) (hcy : c y ∉ C)
    (huniq : ∀ z ∈ σ, c z ∉ C → z = y)
    (hinj_erase : ∀ x ∈ σ, c x ∉ (σ.erase x).image c) :
    ∀ q : Finset T × Finset (Fin (n + 1)),
      IsScarfVtx ords c i₀ q → scarfAdjRel (σ, C) q →
        q = (σ.erase y, C) ∨ q = (σ, insert (c y) C) := by
  -- Derive img_sub: σ.image c ⊆ C ∪ {c y}
  -- Actually we need σ.image c not ⊆ C in general; we need to handle things through hsdiff_cy
  intro q ⟨hqne, hqdom, hqscarf⟩ ⟨hadj_ne, hadj⟩
  -- Need: σ.image c ⊆ C ∪ {c y} (for later use with sdiff_image_erase_card_ge_two)
  -- Actually need: for z with c z ∈ C, σ.image c ⊆ C  is NOT true.
  -- But we do have: for any x ∈ σ, c x ∈ C ↔ x ≠ y
  have hcx_C : ∀ x ∈ σ, x ≠ y → c x ∈ C := by
    intro x hx hne
    by_contra h
    exact hne (huniq x hx h)
  have hi₀C : i₀ ∈ C := by
    have := hnearly ▸ Finset.mem_singleton.mpr (rfl : i₀ = i₀)
    exact (Finset.mem_sdiff.mp this).1
  have hi₀_not_img : i₀ ∉ σ.image c := by
    have := hnearly ▸ Finset.mem_singleton.mpr (rfl : i₀ = i₀)
    exact (Finset.mem_sdiff.mp this).2
  rcases hadj with ⟨_, hA⟩ | ⟨hBcard, hB⟩
  · -- Case A: (σ, C) is the room
    rcases hA with ⟨x, hx, hq1, hq2⟩ | ⟨j, hj, hq1, hq2⟩
    · -- Erase case: q = (σ.erase x, C)
      -- hq1 : q.1 = (σ, C).1.erase x, hq2 : q.2 = (σ, C).2
      -- so q.1 = σ.erase x, q.2 = C
      simp only at hx hq1 hq2
      have hq_eq : q = (σ.erase x, C) := Prod.ext hq1 hq2
      rw [hq_eq] at hqscarf ⊢
      -- Need to show x = y
      by_cases hcx : c x ∈ C
      · -- c(x) ∈ C: show card ≥ 2, contradiction with IsScarfVtx
        exfalso
        have hcx_ne_i₀ : c x ≠ i₀ := by
          intro h; exact hi₀_not_img (h ▸ Finset.mem_image_of_mem c hx)
        have h_cx_not_erase : c x ∉ (σ.erase x).image c := hinj_erase x hx
        have h_i₀_not_erase : i₀ ∉ (σ.erase x).image c := by
          intro h; exact hi₀_not_img (Finset.image_mono c (Finset.erase_subset x σ) h)
        have h_pair_sub : {i₀, c x} ⊆ C \ (σ.erase x).image c := by
          intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact Finset.mem_sdiff.mpr ⟨hi₀C, h_i₀_not_erase⟩
          · exact Finset.mem_sdiff.mpr ⟨hcx, h_cx_not_erase⟩
        have hcard_ge_2 : (C \ (σ.erase x).image c).card ≥ 2 := by
          calc (C \ (σ.erase x).image c).card ≥ ({i₀, c x} : Finset _).card :=
                Finset.card_le_card h_pair_sub
            _ = 2 := Finset.card_pair hcx_ne_i₀.symm
        -- Now show this contradicts IsScarfVtx
        grind
      · -- c(x) ∉ C: then x = y by uniqueness
        grind
    · -- Insert case: q = (σ, insert j C)
      simp only at hj hq1 hq2
      have hq_eq : q = (σ, insert j C) := Prod.ext hq1 hq2
      rw [hq_eq] at hqscarf ⊢
      -- Need to show j = c y
      by_cases hj_img : j ∈ σ.image c
      · -- j ∈ σ.image c: since j ∉ C and σ.image c \ C = {c y}, j = c y
        grind
      · -- j ∉ σ.image c: insert j C \ σ.image c = insert j (C \ σ.image c) has card 2
        exfalso
        have h_sdiff_eq : insert j C \ σ.image c = insert j (C \ σ.image c) :=
          Finset.insert_sdiff_of_notMem _ hj_img
        grind
  · -- Case B: q is the room, (σ, C) is obtained from q
    grind

/-- Verifies that (σ.erase y, C) is an IsScarfVtx when y is the unique element with
    c(y) ∉ C, in the injective case.

    - C is nonempty (given).
    - σ.erase y is dominant wrt C by isDominant_erase.
    - C.card = (σ.erase y).card + 1 since |σ.erase y| = |σ| - 1 = |C| - 1.
    - C \ (σ.erase y).image c = {i₀}: since c is injective on σ,
      c(y) ∉ (σ.erase y).image c and c(y) ∉ C, so
      C \ (σ.erase y).image c = C \ (σ.image c \ {c y}) = C \ σ.image c = {i₀}.

    Uses reused lemma `isDominant_erase`.
    Uses `Finset.card_erase_of_mem : a ∈ s → (s.erase a).card = s.card - 1`. -/
lemma ncr_injective_p1_isScarfVtx {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hnonempty_C : C.Nonempty)
    (hdom : isDominant ords σ C)
    (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀})
    (himg : (σ.image c).card = σ.card)
    (y : T) (hy : y ∈ σ) (hcy : c y ∉ C) :
    IsScarfVtx ords c i₀ (σ.erase y, C) := by
  refine ⟨hnonempty_C, isDominant_erase ords σ C y hdom, Or.inr (Or.inr ⟨?_, ?_⟩)⟩ <;> grind

/-- Verifies that (σ, insert (c y) C) is an IsScarfVtx when y is the unique element
    with c(y) ∉ C, in the injective case.

    - insert (c y) C is nonempty since C is nonempty.
    - σ is dominant wrt insert (c y) C by isDominant_mono_C (C ⊆ insert (c y) C).
    - (insert (c y) C).card = C.card + 1 = σ.card + 1 since c(y) ∉ C.
    - insert (c y) C \ σ.image c = C \ σ.image c = {i₀} since c(y) ∈ σ.image c.

    Uses reused lemma `isDominant_mono_C`.
    Uses `Finset.card_insert_of_notMem : a ∉ s → (insert a s).card = s.card + 1`.
    Uses `Finset.insert_sdiff_of_mem : x ∈ t → insert x s \ t = s \ t`. -/
lemma ncr_injective_p2_isScarfVtx {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hdom : isDominant ords σ C)
    (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀})
    (y : T) (hy : y ∈ σ) (hcy : c y ∉ C) :
    IsScarfVtx ords c i₀ (σ, insert (c y) C) := by
  refine ⟨?_, ?_, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
  · exact (Finset.insert_nonempty _ _)
  · exact isDominant_mono_C ords σ C _ (Finset.subset_insert _ _) hdom
  · rw [Finset.card_insert_of_notMem hcy, hcard]
  · rw [Finset.insert_sdiff_of_mem _ (Finset.mem_image_of_mem c hy), hnearly]

lemma ncr_injective_two_adj_pairs {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (C : Finset (Fin (n + 1)))
    (hnonempty_C : C.Nonempty)
    (hdom : isDominant ords σ C)
    (hcard : σ.card = C.card)
    (hnearly : C \ σ.image c = {i₀})
    (himg : (σ.image c).card = σ.card) :
    ∃ p₁ p₂ : Finset T × Finset (Fin (n + 1)),
      p₁ ≠ p₂ ∧
      IsScarfVtx ords c i₀ p₁ ∧
      scarfAdjRel (σ, C) p₁ ∧
      IsScarfVtx ords c i₀ p₂ ∧
      scarfAdjRel (σ, C) p₂ ∧
      ∀ q : Finset T × Finset (Fin (n + 1)),
        IsScarfVtx ords c i₀ q → scarfAdjRel (σ, C) q → q = p₁ ∨ q = p₂ := by
  -- Step 1: Find the unique y ∈ σ with c(y) ∉ C
  obtain ⟨y, hy, hcy, hsdiff_cy, huniq, hσne, hinj_erase⟩ :=
    ncr_injective_unique_y c σ C i₀ hcard hnearly himg
  -- Step 2: Define the two candidates
  refine ⟨(σ.erase y, C), (σ, insert (c y) C), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- p₁ ≠ p₂: first components differ since y ∈ σ
    grind
  · -- IsScarfVtx for p₁
    exact ncr_injective_p1_isScarfVtx ords c i₀ σ C hnonempty_C hdom hcard hnearly himg
      y hy hcy
  · -- scarfAdjRel for p₁ = (σ.erase y, C)
    refine ⟨?_, Or.inl ⟨hcard, Or.inl ⟨y, hy, rfl, rfl⟩⟩⟩
    grind
  · -- IsScarfVtx for p₂
    exact ncr_injective_p2_isScarfVtx ords c i₀ σ C hdom hcard hnearly
      y hy hcy
  · -- scarfAdjRel for p₂ = (σ, insert (c y) C)
    refine ⟨?_, Or.inl ⟨hcard, Or.inr ⟨c y, hcy, rfl, rfl⟩⟩⟩
    grind
  · -- Uniqueness
    exact ncr_injective_uniqueness ords c i₀ σ C hcard hnearly
      y hy hcy huniq hinj_erase

lemma scarf_degree_ncr_case_injective {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (hcard : v.val.1.card = v.val.2.card)
    (hnearly : v.val.2 \ v.val.1.image c = {i₀})
    (himg : (v.val.1.image c).card = v.val.1.card) :
    G.degree v = 2 := by
  obtain ⟨hnonempty_C, hdom, _⟩ := v.prop
  obtain ⟨p₁, p₂, hne, hp₁, hadj₁, hp₂, hadj₂, huniq⟩ :=
    ncr_injective_two_adj_pairs ords c i₀ v.val.1 v.val.2 hnonempty_C hdom hcard hnearly himg
  exact scarf_degree_of_two_adj_pairs ords c i₀ G hG v p₁ p₂ hne hp₁ hadj₁ hp₂ hadj₂ huniq

lemma scarf_degree_nearly_colorful_room {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (hcard : v.val.1.card = v.val.2.card)
    (hnearly : v.val.2 \ v.val.1.image c = {i₀}) :
    G.degree v = 2 := by
  rcases nearly_colorful_image_card_cases c v.val.1 v.val.2 i₀ hcard hnearly with hinj | hninj
  · exact scarf_degree_ncr_case_injective ords c i₀ G hG v hcard hnearly hinj
  · exact scarf_degree_ncr_case_noninjective ords c i₀ G hG v hcard hnearly hninj

lemma scarf_degree_outside_door {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (hdoor : v.val.2.card = v.val.1.card + 1)
    (hnearly : v.val.2 \ v.val.1.image c = {i₀})
    (hempty : v.val.1 = ∅) :
    G.degree v = 1 := by
  have hC : v.val.2 = {i₀} := by grind
  have hv_not_room : v.val.1.card ≠ v.val.2.card := by
    rw [hempty, hC]; simp
  -- Any neighbor w must have w.val = ({x}, {i₀}) for some x
  have adj_char : ∀ w : { p // IsScarfVtx ords c i₀ p },
      G.Adj v w → ∃ x : T, w.val = ({x}, {i₀}) := by
    intro w hw
    rw [hG] at hw
    obtain ⟨_, hcases⟩ := hw
    rcases hcases with ⟨hroom_v, _⟩ | ⟨hroom_w, hmod⟩
    · exact absurd hroom_v hv_not_room
    · rcases hmod with ⟨x, hxw, hv1eq, hv2eq⟩ | ⟨i, _, hv1eq, hv2eq⟩
      · exact ⟨x, Prod.ext
          (Finset.eq_singleton_iff_unique_mem.mpr ⟨hxw, fun a ha ↦ by
            by_contra hne
            have := Finset.mem_erase.mpr ⟨hne, ha⟩
            rw [← hv1eq, hempty] at this; simp at this⟩)
          (by rw [← hv2eq, hC])⟩
      · rw [hempty] at hv1eq
        have : w.val.2.card = 0 := by
          have := hroom_w; rw [← hv1eq] at this; simp at this; omega
        exact absurd (Finset.card_eq_zero.mp this ▸ w.prop.1) (by simp)
  -- Any neighbor's x must be max under ords i₀
  have adj_max : ∀ w : { p // IsScarfVtx ords c i₀ p },
      G.Adj v w → ∀ x : T, w.val = ({x}, {i₀}) →
        ∀ y : T, ¬ (ords i₀).lt x y := by
    intro w _ x hwx y
    have hdom := w.prop.2.1; rw [hwx] at hdom
    obtain ⟨i, hi, hlt⟩ := hdom y
    rw [Finset.mem_singleton] at hi; subst hi
    exact hlt x (Finset.mem_singleton.mpr rfl)
  -- Any two neighbors are equal
  have adj_unique : ∀ w₁ w₂ : { p // IsScarfVtx ords c i₀ p },
      G.Adj v w₁ → G.Adj v w₂ → w₁ = w₂ := by
    intro w₁ w₂ hw₁ hw₂
    obtain ⟨x₁, hx₁⟩ := adj_char w₁ hw₁
    obtain ⟨x₂, hx₂⟩ := adj_char w₂ hw₂
    have hmax₁ := adj_max w₁ hw₁ x₁ hx₁
    have hmax₂ := adj_max w₂ hw₂ x₂ hx₂
    have : x₁ = x₂ := by
      by_contra hne
      rcases @lt_or_gt_of_ne T (ords i₀) x₁ x₂ hne with h | h
      · exact hmax₁ x₂ h
      · exact hmax₂ x₁ h
    subst this
    exact Subtype.ext (hx₁.symm ▸ hx₂.symm ▸ rfl)
  -- Construct the max element
  let linord := ords i₀
  let x_max : T := @Finset.max' T linord Finset.univ Finset.univ_nonempty
  have hx_max : ∀ y : T, ¬ (ords i₀).lt x_max y :=
    fun y ↦ not_lt.mpr (@Finset.le_max' T linord Finset.univ y (Finset.mem_univ y))
  -- ({x_max}, {i₀}) is a Scarf vertex
  have hscarf : IsScarfVtx ords c i₀ ({x_max}, {i₀}) := by
    refine ⟨⟨i₀, Finset.mem_singleton.mpr rfl⟩, ?_, ?_⟩
    · intro y; exact ⟨i₀, Finset.mem_singleton.mpr rfl,
        fun z hz ↦ by rw [Finset.mem_singleton] at hz; subst hz; exact hx_max y⟩
    · by_cases hci : c x_max = i₀
      · left; exact ⟨by simp, by simp [hci]⟩
      · right; left; refine ⟨by simp, ?_⟩
        ext i; simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_image]
        constructor
        · rintro ⟨rfl, h⟩; push Not at h; rfl
        · intro hi; subst hi; exact ⟨rfl, by push Not; intro a ha; subst ha; exact hci⟩
  let w_max : { p // IsScarfVtx ords c i₀ p } := ⟨({x_max}, {i₀}), hscarf⟩
  -- Show v and w_max are adjacent via scarfAdjRel
  have hadj : G.Adj v w_max := by
    rw [hG]
    constructor
    · -- v.val ≠ w_max.val
      grind
    · -- scarfAdjRel structural part
      right; constructor
      · -- w_max is a room: ({x_max} : Finset T).card = ({i₀} : Finset (Fin (n+1))).card
        show ({x_max} : Finset T).card = ({i₀} : Finset (Fin (n + 1))).card; simp
      · left; refine ⟨x_max, Finset.mem_singleton.mpr rfl, ?_, ?_⟩
        · -- v.1 = w_max.1.erase x_max = {x_max}.erase x_max = ∅
          change v.val.1 = ({x_max} : Finset T).erase x_max
          rw [hempty, Finset.erase_singleton]
        · -- v.2 = w_max.2
          change v.val.2 = ({i₀} : Finset (Fin (n + 1)))
          exact hC
  -- Conclude degree = 1
  rw [SimpleGraph.degree.eq_1, Finset.card_eq_one]
  exact ⟨w_max, Finset.ext (fun u ↦ by
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    exact ⟨fun hu ↦ adj_unique u w_max hu hadj, fun hu ↦ hu ▸ hadj⟩)⟩

/-- For each i ∈ D, define the minimum of τ under order (ords i) as the element t ∈ τ
    such that t ≤_i x for all x ∈ τ. This exists because τ is nonempty and T has a
    linear order from (ords i).

    Uses `Finset.min' (s : Finset α) (h : s.Nonempty) : α` with
    `Finset.min'_mem : ∀ (s : Finset α) (h : s.Nonempty), s.min' h ∈ s` and
    `Finset.min'_le : ∀ (s : Finset α) (x : α) (h : x ∈ s), s.min' ⋯ ≤ x`. -/
def ordMin {n : ℕ} {T : Type}
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (hne : τ.Nonempty) (i : Fin (n + 1)) : T :=
  @Finset.min' T (ords i) τ hne

/-- The minimum element of τ under order i belongs to τ.
    Direct from `Finset.min'_mem : ∀ {α : Type} [inst : LinearOrder α] (s : Finset α)
    (H : s.Nonempty), s.min' H ∈ s`. -/
lemma ordMin_mem {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (hne : τ.Nonempty) (i : Fin (n + 1)) :
    ordMin ords τ hne i ∈ τ :=
  @Finset.min'_mem T (ords i) τ hne

/-- The minimum element of τ under order i satisfies ¬(x <_i ordMin) for all x ∈ τ.
    Direct from `Finset.min'_le : ∀ {α : Type} [inst : LinearOrder α] (s : Finset α)
    (x : α) (H : x ∈ s), s.min' ⋯ ≤ x` and the fact that ≤ means ¬ lt in a LinearOrder. -/
lemma ordMin_le {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (hne : τ.Nonempty) (i : Fin (n + 1)) (x : T) (hx : x ∈ τ) :
    ¬ (ords i).lt x (ordMin ords τ hne i) := by
  unfold ordMin
  have hle := @Finset.min'_le T (ords i) τ x hx
  exact @not_lt_of_ge T (ords i).toPreorder _ _ hle

/-- The image of the ordMin map covers all of τ:
    for every t ∈ τ, there exists i ∈ D such that ordMin ords τ hne i = t.

    Proof: Suppose t ∈ τ but t ≠ ordMin i for all i ∈ D. Then for all i ∈ D,
    ordMin i <_i t (since ordMin i ≤_i t and ordMin i ≠ t in a linear order).
    Consider y = t in the dominance condition: we need some i ∈ D with
    ∀ x ∈ τ, ¬(x <_i t). But ordMin i ∈ τ and ordMin i <_i t, contradiction.

    No direct Mathlib equivalent. Uses isDominant definition and ordMin properties. -/
lemma ordMin_surj_on_tau {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hne : τ.Nonempty) (hdom : isDominant ords τ D) (t : T) (ht : t ∈ τ) :
    ∃ i ∈ D, ordMin ords τ hne i = t := by
  by_contra h
  push Not at h
  obtain ⟨i₀, hi₀D, hi₀⟩ := hdom t
  have hne_eq := h i₀ hi₀D
  have h1 := ordMin_le ords τ hne i₀ t ht
  have h2 := hi₀ (ordMin ords τ hne i₀) (ordMin_mem ords τ hne i₀)
  exact hne_eq (@le_antisymm T (ords i₀).toPartialOrder _ _
    (@not_lt _ (ords i₀) _ _ |>.mp h2) (@not_lt _ (ords i₀) _ _ |>.mp h1)).symm

lemma ordMin_image_eq_tau {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hne : τ.Nonempty) (hdom : isDominant ords τ D) :
    Finset.image (ordMin ords τ hne) D = τ := by
  ext t
  constructor
  · intro ht
    simp only [Finset.mem_image] at ht
    obtain ⟨i, _, hi_eq⟩ := ht
    rw [← hi_eq]
    exact ordMin_mem ords τ hne i
  · intro ht
    simp only [Finset.mem_image]
    obtain ⟨i, hi, heq⟩ := ordMin_surj_on_tau ords τ D hne hdom t ht
    exact ⟨i, hi, heq⟩

lemma ordMin_collision_unique {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hne : τ.Nonempty)
    (hdom : isDominant ords τ D)
    (hdoor : D.card = τ.card + 1)
    (a : Fin (n + 1)) (ha : a ∈ D) (b : Fin (n + 1)) (hb : b ∈ D)
    (hab : a ≠ b) (heq : ordMin ords τ hne a = ordMin ords τ hne b) :
    ∀ c ∈ D, ∀ d ∈ D, c ≠ d → ordMin ords τ hne c = ordMin ords τ hne d →
      ({c, d} : Finset (Fin (n + 1))) = {a, b} := by
  have himg_erase : Finset.image (ordMin ords τ hne) (D.erase b) = τ := by
    have hfull := ordMin_image_eq_tau ords τ D hne hdom
    grind
  have hcard_erase : (D.erase b).card = τ.card := by
    rw [Finset.card_erase_of_mem hb]; omega
  have hinj : Set.InjOn (ordMin ords τ hne) ↑(D.erase b) := by grind
  have ha_erase : a ∈ D.erase b := Finset.mem_erase.mpr ⟨fun h ↦ hab (h ▸ rfl), ha⟩
  intro c hc d hd hcd hcd_eq
  by_cases hcb : c = b
  · have hd_ne_b : d ≠ b := fun h ↦ hcd (hcb.trans h.symm)
    have hd_erase : d ∈ D.erase b := Finset.mem_erase.mpr ⟨hd_ne_b, hd⟩
    have hval : ordMin ords τ hne d = ordMin ords τ hne a := by
      rw [← hcd_eq, hcb, heq]
    have hda := hinj hd_erase ha_erase hval
    rw [hda, hcb]
    exact Finset.pair_comm b a
  · by_cases hdb : d = b
    · have hc_erase : c ∈ D.erase b := Finset.mem_erase.mpr ⟨hcb, hc⟩
      have hval : ordMin ords τ hne c = ordMin ords τ hne a := by
        rw [hcd_eq, hdb, heq]
      have hca := hinj hc_erase ha_erase hval
      rw [hca, hdb]
    · have hc_erase : c ∈ D.erase b := Finset.mem_erase.mpr ⟨hcb, hc⟩
      have hd_erase : d ∈ D.erase b := Finset.mem_erase.mpr ⟨hdb, hd⟩
      exact absurd (hinj hc_erase hd_erase hcd_eq) hcd

lemma ordMin_unique_collision {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hne : τ.Nonempty)
    (hdom : isDominant ords τ D)
    (hdoor : D.card = τ.card + 1) :
    ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ ordMin ords τ hne a = ordMin ords τ hne b ∧
      (∀ c ∈ D, ∀ d ∈ D, c ≠ d → ordMin ords τ hne c = ordMin ords τ hne d →
        ({c, d} : Finset (Fin (n + 1))) = {a, b}) := by
  have hmaps : Set.MapsTo (ordMin ords τ hne) ↑D ↑τ := by
    intro i _
    exact ordMin_mem ords τ hne i
  have hcard : τ.card < D.card := by omega
  obtain ⟨a, ha, b, hb, hab, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  exact ⟨a, ha, b, hb, hab, heq, ordMin_collision_unique ords τ D hne hdom hdoor a ha b hb hab heq⟩

/-- For a door (τ, D) with D.card = τ.card + 1, any pair q adjacent via scarfAdjRel
    must be a room with q obtained by adding an element to τ (with index set D)
    or by removing an element from D (with vertex set τ).

    Since D.card = τ.card + 1, the pair (τ, D) is not a room (τ.card ≠ D.card).
    Therefore in scarfAdjRel (τ, D) q, we must use the second disjunct:
    q is a room (q.1.card = q.2.card) and (τ, D) is obtained from q by
    erasing from q.1 or inserting into q.2.

    Case 1: ∃ x ∈ q.1, τ = q.1.erase x ∧ D = q.2 → q.1 = insert x τ, q.2 = D
    Case 2: ∃ i, i ∉ q.2 ∧ τ = q.1 ∧ D = insert i q.2 → q.1 = τ, q.2 = D.erase i

    Uses `Finset.card_erase_of_mem`, `Finset.insert_erase`, `Finset.card_insert_of_not_mem`. -/
lemma adj_door_neighbor_form {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hdoor : D.card = τ.card + 1)
    (q : Finset T × Finset (Fin (n + 1)))
    (hscarf : IsScarfVtx ords c i₀ q)
    (hadj : scarfAdjRel (τ, D) q) :
    (∃ x, x ∉ τ ∧ q.1 = insert x τ ∧ q.2 = D ∧ isDominant ords (insert x τ) D) ∨
    (∃ i, i ∈ D ∧ q.1 = τ ∧ q.2 = D.erase i ∧ isDominant ords τ (D.erase i)) := by
  obtain ⟨_, hdom, _⟩ := hscarf
  obtain ⟨_, hcases⟩ := hadj
  dsimp only at hcases
  rcases hcases with ⟨hcard, _⟩ | ⟨_, hmod⟩
  · omega
  · rcases hmod with ⟨x, hx, hτeq, hDeq⟩ | ⟨i, hi, hτeq, hDeq⟩
    · left
      refine ⟨x, ?_, ?_, hDeq.symm, ?_⟩
      · rw [hτeq]; exact Finset.notMem_erase x q.1
      · rw [hτeq, Finset.insert_erase hx]
      · rw [hτeq, Finset.insert_erase hx, hDeq]; exact hdom
    · right
      refine ⟨i, ?_, hτeq.symm, ?_, ?_⟩
      · rw [hDeq]; exact Finset.mem_insert_self i q.2
      · rw [hDeq, Finset.erase_insert hi]
      · rw [hτeq, hDeq, Finset.erase_insert hi]; exact hdom

lemma isDominant_erase_of_empty_Mi {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hnonempty : τ.Nonempty)
    (i : Fin (n + 1))
    (hMi : ∀ y : T, ∃ k ∈ D.erase i, ¬ (ords k).lt (ordMin ords τ hnonempty k) y) :
    isDominant ords τ (D.erase i) := by
  intro y
  obtain ⟨k, hk_mem, hk_not_lt⟩ := hMi y
  refine ⟨k, hk_mem, fun x hx hxy ↦ ?_⟩
  have hle := ordMin_le ords τ hnonempty k x hx
  exact hk_not_lt <| @lt_of_le_of_lt T (_) _ _ _ (@le_of_not_gt T (ords k) _ _ hle) hxy

lemma erase_nonempty_of_card_ge_two {α : Type} [DecidableEq α]
    (D : Finset α) (i : α) (hi : i ∈ D) (hcard : D.card ≥ 2) :
    (D.erase i).Nonempty := by
  have h₁ : (D.erase i).card = D.card - 1 := by
    rw [Finset.card_erase_of_mem hi]
  have h₂ : D.card - 1 ≥ 1 := by
    have h₄ : D.card - 1 ≥ 1 := by
      omega
    exact h₄
  have h₃ : (D.erase i).Nonempty := by
    have h₄ : (D.erase i).card > 0 := by
      omega
    exact Finset.card_pos.mp h₄
  exact h₃

lemma erase_eq_image_of_eq_i₀ {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (i₀ : Fin (n + 1))
    (hiD : i₀ ∈ D)
    (hdoor : D.card = τ.card + 1)
    (hnearly : D \ τ.image c = {i₀}) :
    D.erase i₀ = τ.image c := by
  have hsub : D.erase i₀ ⊆ τ.image c := by
    rw [Finset.subset_iff]
    intro x hx
    by_contra hxnot
    have hx' : x ∈ D.erase i₀ \ τ.image c := Finset.mem_sdiff.mpr ⟨hx, hxnot⟩
    rw [Finset.erase_sdiff_comm, hnearly] at hx'
    simp at hx'
  have hcard : (τ.image c).card ≤ (D.erase i₀).card := by grind
  exact (Finset.eq_of_superset_of_card_ge hsub hcard).symm

lemma erase_sdiff_image_eq_singleton {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (i i₀ : Fin (n + 1))
    (hne : i ≠ i₀)
    (hnearly : D \ τ.image c = {i₀}) :
    (D.erase i) \ τ.image c = {i₀} := by
  grind

lemma isScarfVtx_erase_case {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hiD : i ∈ D)
    (hdom_erase : isDominant ords τ (D.erase i))
    (hdoor : D.card = τ.card + 1)
    (hnearly : D \ τ.image c = {i₀})
    (hcard2 : D.card ≥ 2) :
    IsScarfVtx ords c i₀ (τ, D.erase i) := by
  refine ⟨erase_nonempty_of_card_ge_two D i hiD hcard2, hdom_erase, ?_⟩
  have hcard_erase : (D.erase i).card = τ.card := by
    rw [Finset.card_erase_of_mem hiD, hdoor]; omega
  by_cases h : i = i₀
  · subst h
    left
    exact ⟨hcard_erase.symm, erase_eq_image_of_eq_i₀ c τ D _ hiD hdoor hnearly⟩
  · right; left
    exact ⟨hcard_erase.symm, erase_sdiff_image_eq_singleton c τ D i i₀ h hnearly⟩

lemma scarfAdjRel_erase {n : ℕ} {T : Type} [DecidableEq T]
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hdoor : D.card = τ.card + 1)
    (i : Fin (n + 1)) (hiD : i ∈ D) :
    scarfAdjRel (τ, D) (τ, D.erase i) := by
  have h_i_not_in_erase : i ∉ D.erase i := by grind
  grind [=scarfAdjRel]

lemma not_lt_ordMin_of_max_Mi {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hdom : isDominant ords τ D)
    (hnonempty : τ.Nonempty)
    (i : Fin (n + 1))
    (x : T) (hx_in_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x) :
    ¬ (ords i).lt (ordMin ords τ hnonempty i) x := by
  intro hcontra
  obtain ⟨k, hkD, hk⟩ := hdom x
  have hmin_mem := ordMin_mem ords τ hnonempty k
  grind

lemma ordMin_eq_of_mem_of_not_lt {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (hne : τ.Nonempty) (i : Fin (n + 1))
    (x : T) (hx : x ∈ τ) (hnotlt : ¬ (ords i).lt (ordMin ords τ hne i) x) :
    ordMin ords τ hne i = x := by
  unfold ordMin
  have hle := @Finset.min'_le T (ords i) τ x hx
  exact @eq_of_le_of_not_lt T (ords i).toPartialOrder _ _ hle hnotlt

lemma not_mem_tau_of_max_Mi {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hnonempty : τ.Nonempty)
    (a b : Fin (n + 1)) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hcoll : ordMin ords τ hnonempty a = ordMin ords τ hnonempty b)
    (i : Fin (n + 1)) (hi : i ∈ ({a, b} : Finset (Fin (n + 1))))
    (x : T) (hx_in_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x)
    (hx_not_lt : ¬ (ords i).lt (ordMin ords τ hnonempty i) x) :
    x ∉ τ := by
  intro hx_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  obtain rfl | rfl := hi
  · have hb_erase : b ∈ D.erase i := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    have hlt_b : (ords b).lt (ordMin ords τ hnonempty b) x := hx_in_Mi b hb_erase
    have heq : ordMin ords τ hnonempty i = x :=
      ordMin_eq_of_mem_of_not_lt ords τ hnonempty i x hx_mem hx_not_lt
    have heq_b : ordMin ords τ hnonempty b = x := hcoll.symm.trans heq
    rw [heq_b] at hlt_b
    exact @lt_irrefl T (ords b).toPreorder x hlt_b
  · have ha_erase : a ∈ D.erase i := Finset.mem_erase.mpr ⟨hab, ha⟩
    have hlt_a : (ords a).lt (ordMin ords τ hnonempty a) x := hx_in_Mi a ha_erase
    have heq : ordMin ords τ hnonempty i = x :=
      ordMin_eq_of_mem_of_not_lt ords τ hnonempty i x hx_mem hx_not_lt
    have heq_a : ordMin ords τ hnonempty a = x := hcoll.trans heq
    rw [heq_a] at hlt_a
    exact @lt_irrefl T (ords a).toPreorder x hlt_a

lemma isDominant_insert_case1 {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (x y : T)
    (k₀ : Fin (n + 1))
    (hk₀_τ : ∀ z ∈ τ, ¬ (ords k₀).lt z y)
    (hk₀_x : ¬ (ords k₀).lt x y) :
    ∀ z ∈ insert x τ, ¬ (ords k₀).lt z y := by
  grind

lemma case2_k0_eq_i {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hnonempty : τ.Nonempty)
    (i : Fin (n + 1))
    (x y : T)
    (k₀ : Fin (n + 1)) (hk₀D : k₀ ∈ D)
    (hk₀_τ : ∀ z ∈ τ, ¬ (ords k₀).lt z y)
    (hx_lt_k₀ : (ords k₀).lt x y)
    (hx_in_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x) :
    k₀ = i := by
  by_contra hne
  have hk₀_mem : k₀ ∈ D.erase i := Finset.mem_erase.mpr ⟨hne, hk₀D⟩
  have h1 := hx_in_Mi k₀ hk₀_mem
  have h2 : ordMin ords τ hnonempty k₀ ∈ τ := @Finset.min'_mem T (ords k₀) τ hnonempty
  exact hk₀_τ _ h2 (@lt_trans T (ords k₀).toPreorder _ _ _ h1 hx_lt_k₀)

lemma case2_witness_k1_tau {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (hnonempty : τ.Nonempty)
    (y : T)
    (k₁ : Fin (n + 1))
    (hk₁_not : ¬ (ords k₁).lt (ordMin ords τ hnonempty k₁) y) :
    ∀ z ∈ τ, ¬ (ords k₁).lt z y := by
  intro z hz hzy
  apply hk₁_not
  let := ords k₁
  exact lt_of_le_of_lt (@Finset.min'_le T _ τ z hz) hzy

lemma case2_witness_k1_x {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (hnonempty : τ.Nonempty)
    (x y : T)
    (k₁ : Fin (n + 1))
    (hk₁_not : ¬ (ords k₁).lt (ordMin ords τ hnonempty k₁) y)
    (hk₁_lt_x : (ords k₁).lt (ordMin ords τ hnonempty k₁) x) :
    ¬ (ords k₁).lt x y := by
  intro hxy
  apply hk₁_not
  let := ords k₁
  exact lt_trans hk₁_lt_x hxy

lemma case2_witness_k1 {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hnonempty : τ.Nonempty)
    (i : Fin (n + 1))
    (x y : T)
    (k₁ : Fin (n + 1)) (hk₁ : k₁ ∈ D.erase i)
    (hk₁_not : ¬ (ords k₁).lt (ordMin ords τ hnonempty k₁) y)
    (hx_in_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x) :
    ∀ z ∈ insert x τ, ¬ (ords k₁).lt z y := by
  intro z hz
  rw [Finset.mem_insert] at hz
  rcases hz with rfl | hz
  · exact case2_witness_k1_x ords τ hnonempty _ y k₁ hk₁_not (hx_in_Mi k₁ hk₁)
  · exact case2_witness_k1_tau ords τ hnonempty y k₁ hk₁_not z hz

lemma isDominant_insert_of_max_Mi {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hdom : isDominant ords τ D)
    (hnonempty : τ.Nonempty)
    (i : Fin (n + 1)) (x : T)
    (hx_in_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x)
    (hx_max : ∀ y : T, (∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) y) →
      ¬ (ords i).lt x y) :
    isDominant ords (insert x τ) D := by
  intro y
  obtain ⟨k₀, hk₀D, hk₀_τ⟩ := hdom y
  by_cases hcase : (ords k₀).lt x y
  · have hk₀_eq : k₀ = i := case2_k0_eq_i ords τ D hnonempty i x y k₀ hk₀D hk₀_τ hcase hx_in_Mi
    rw [hk₀_eq] at hcase
    have hnotall : ¬ ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) y := by
      intro hall
      exact hx_max y hall hcase
    push Not at hnotall
    obtain ⟨k₁, hk₁, hk₁_not⟩ := hnotall
    have hk₁_not' : ¬ (ords k₁).lt (ordMin ords τ hnonempty k₁) y := by
      rwa [@not_lt T (ords k₁)]
    exact ⟨k₁, Finset.mem_of_mem_erase hk₁,
      case2_witness_k1 ords τ D hnonempty i x y k₁ hk₁ hk₁_not' hx_in_Mi⟩
  · exact ⟨k₀, hk₀D, isDominant_insert_case1 ords τ x y k₀ hk₀_τ hcase⟩

lemma isScarfVtx_insert_case_cx_eq {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (x : T) (hx_not_mem : x ∉ τ)
    (hdoor : D.card = τ.card + 1)
    (hnearly : D \ τ.image c = {i₀})
    (hcx : c x = i₀) :
    (insert x τ).card = D.card ∧ D = (insert x τ).image c := by
  constructor
  · rw [Finset.card_insert_of_notMem hx_not_mem, hdoor]
  · rw [Finset.image_insert]
    have h1 : D \ insert (c x) (τ.image c) = (D \ τ.image c).erase (c x) :=
      Finset.sdiff_insert D (τ.image c) (c x)
    rw [hnearly] at h1
    have h2 : ({i₀} : Finset (Fin (n + 1))).erase (c x) = ∅ := by
      rw [hcx]; simp
    rw [h2] at h1
    have hsub : D ⊆ insert (c x) (τ.image c) :=
      Finset.sdiff_eq_empty_iff_subset.mp h1
    apply Finset.eq_of_subset_of_card_le hsub
    calc (insert (c x) (τ.image c)).card
        ≤ (insert x τ).card := by rw [← Finset.image_insert]; exact Finset.card_image_le
      _ = τ.card + 1 := Finset.card_insert_of_notMem hx_not_mem
      _ = D.card := hdoor.symm

lemma isScarfVtx_insert_case_cx_ne {n : ℕ} {T : Type} [DecidableEq T]
    (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (x : T) (hx_not_mem : x ∉ τ)
    (hdoor : D.card = τ.card + 1)
    (hnearly : D \ τ.image c = {i₀})
    (hcx : c x ≠ i₀) :
    (insert x τ).card = D.card ∧ D \ (insert x τ).image c = {i₀} := by
  constructor
  · rw [Finset.card_insert_of_notMem hx_not_mem, hdoor]
  · rw [Finset.image_insert, Finset.sdiff_insert, hnearly]
    exact Finset.erase_eq_of_notMem (Finset.notMem_singleton.mpr hcx)

lemma isScarfVtx_insert_case {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (x : T) (hx_not_mem : x ∉ τ)
    (hdom_ins : isDominant ords (insert x τ) D)
    (hne : D.Nonempty)
    (hdoor : D.card = τ.card + 1)
    (hnearly : D \ τ.image c = {i₀}) :
    IsScarfVtx ords c i₀ (insert x τ, D) := by
  refine ⟨hne, hdom_ins, ?_⟩
  by_cases hcx : c x = i₀
  · left
    exact isScarfVtx_insert_case_cx_eq c i₀ τ D x hx_not_mem hdoor hnearly hcx
  · right; left
    exact isScarfVtx_insert_case_cx_ne c i₀ τ D x hx_not_mem hdoor hnearly hcx

lemma scarfAdjRel_insert {n : ℕ} {T : Type} [DecidableEq T]
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hdoor : D.card = τ.card + 1)
    (x : T) (hx_not_mem : x ∉ τ) :
    scarfAdjRel (τ, D) (insert x τ, D) := by
  refine ⟨?_, Or.inr ⟨?_, Or.inl ⟨x, Finset.mem_insert_self x τ, ?_, rfl⟩⟩⟩ <;> grind

/-- For each i ∈ {a, b} (the colliding pair), exactly one of two cases holds:
    (1) M_i = ∅ (no y strictly above all ordMin k for k ∈ D \ {i}), giving neighbor (τ, D.erase i)
    (2) M_i ≠ ∅, giving neighbor (insert m_i τ, D) where m_i is the max of M_i under <_i

    The resulting neighbor satisfies IsScarfVtx and scarfAdjRel.

    In the insert case, x satisfies the index-specific conditions:
    - ∀ k ∈ D.erase i, ordMin_k(τ) <_k x  (x is in M_i)
    - ¬ ordMin_i(τ) <_i x  (x ≤_i ordMin_i(τ), so x becomes the new min under order i)
    These conditions uniquely tie x to the specific index i, which is crucial for
    proving the two neighbors are distinct (M_a ∩ M_b = ∅).

    No direct Mathlib equivalent. Combines dominance characterization with IsScarfVtx. -/
lemma scarf_neighbor_from_collision_index {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hne : D.Nonempty) (hdom : isDominant ords τ D)
    (hdoor : D.card = τ.card + 1)
    (hnearly : D \ τ.image c = {i₀})
    (hnonempty : τ.Nonempty)
    (a b : Fin (n + 1)) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hcoll : ordMin ords τ hnonempty a = ordMin ords τ hnonempty b)
    (huniq : ∀ c' ∈ D, ∀ d ∈ D, c' ≠ d →
      ordMin ords τ hnonempty c' = ordMin ords τ hnonempty d →
        ({c', d} : Finset (Fin (n + 1))) = {a, b})
    (i : Fin (n + 1)) (hi : i ∈ ({a, b} : Finset (Fin (n + 1)))) :
    ∃ p : Finset T × Finset (Fin (n + 1)),
      IsScarfVtx ords c i₀ p ∧ scarfAdjRel (τ, D) p ∧
      ((p.1 = τ ∧ p.2 = D.erase i) ∨
       (∃ x, x ∉ τ ∧ p.1 = insert x τ ∧ p.2 = D ∧
        (∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x) ∧
        ¬ (ords i).lt (ordMin ords τ hnonempty i) x)) := by
  have hiD : i ∈ D := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption
  have hcard2 : D.card ≥ 2 := by
    have := hnonempty.card_pos; omega
  let inMi := fun y ↦ ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) y
  by_cases hMi : ∃ y : T, inMi y
  · obtain ⟨y₀, hy₀⟩ := hMi
    let Mi : Finset T := Finset.univ.filter inMi
    have hMi_ne : Mi.Nonempty := ⟨y₀, Finset.mem_filter.mpr ⟨Finset.mem_univ y₀, hy₀⟩⟩
    let mi := @Finset.max' T (ords i) Mi hMi_ne
    have hmi_mem_Mi : mi ∈ Mi := @Finset.max'_mem T (ords i) Mi hMi_ne
    have hmi_in_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) mi :=
      (Finset.mem_filter.mp hmi_mem_Mi).2
    have hmi_max : ∀ y : T, (∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) y) →
        ¬ (ords i).lt mi y := by
      intro y hy hlt
      have hy_mem : y ∈ Mi := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩
      have hle := @Finset.le_max' T (ords i) Mi y hy_mem
      exact absurd hlt (@not_lt_of_ge T (ords i).toPreorder y mi hle)
    have hmi_not_lt := not_lt_ordMin_of_max_Mi ords τ D hdom hnonempty i mi hmi_in_Mi
    have hmi_not_mem := not_mem_tau_of_max_Mi ords τ D hnonempty a b ha hb hab hcoll
      i hi mi hmi_in_Mi hmi_not_lt
    have hdom_ins := isDominant_insert_of_max_Mi ords τ D hdom hnonempty i mi hmi_in_Mi hmi_max
    have hscarf := isScarfVtx_insert_case ords c i₀ τ D mi hmi_not_mem hdom_ins hne hdoor hnearly
    have hadj := scarfAdjRel_insert τ D hdoor mi hmi_not_mem
    exact ⟨(insert mi τ, D), hscarf, hadj, .inr ⟨mi, hmi_not_mem, rfl, rfl, hmi_in_Mi, hmi_not_lt⟩⟩
  · simp only [inMi] at hMi
    push Not at hMi
    have hMi_empty : ∀ y : T, ∃ k ∈ D.erase i, ¬ (ords k).lt (ordMin ords τ hnonempty k) y := by
      intro y
      obtain ⟨k, hk, hkle⟩ := hMi y
      exact ⟨k, hk, @not_lt_of_ge T (ords k).toPreorder y (ordMin ords τ hnonempty k) hkle⟩
    have hdom_er := isDominant_erase_of_empty_Mi ords τ D hnonempty i hMi_empty
    have hscarf := isScarfVtx_erase_case ords c i₀ τ D i hiD hdom_er hdoor hnearly hcard2
    have hadj := scarfAdjRel_erase τ D hdoor i hiD
    exact ⟨(τ, D.erase i), hscarf, hadj, Or.inl ⟨rfl, rfl⟩⟩

lemma insert_elements_ne_of_collision {n : ℕ} {T : Type}
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (hnonempty : τ.Nonempty)
    (D : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (ha : a ∈ D) (hab : a ≠ b)
    (x₁ x₂ : T)
    (hx₁_not : ¬ (ords a).lt (ordMin ords τ hnonempty a) x₁)
    (hx₂_lt : ∀ k ∈ D.erase b, (ords k).lt (ordMin ords τ hnonempty k) x₂) :
    x₁ ≠ x₂ := by
  grind

lemma scarf_two_neighbors_distinct {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hnonempty : τ.Nonempty)
    (a b : Fin (n + 1)) (ha : a ∈ D) (hab : a ≠ b)
    (p₁ p₂ : Finset T × Finset (Fin (n + 1)))
    (hp₁ : IsScarfVtx ords c i₀ p₁ ∧ scarfAdjRel (τ, D) p₁ ∧
      ((p₁.1 = τ ∧ p₁.2 = D.erase a) ∨
       (∃ x, x ∉ τ ∧ p₁.1 = insert x τ ∧ p₁.2 = D ∧
        (∀ k ∈ D.erase a, (ords k).lt (ordMin ords τ hnonempty k) x) ∧
        ¬ (ords a).lt (ordMin ords τ hnonempty a) x)))
    (hp₂ : IsScarfVtx ords c i₀ p₂ ∧ scarfAdjRel (τ, D) p₂ ∧
      ((p₂.1 = τ ∧ p₂.2 = D.erase b) ∨
       (∃ x, x ∉ τ ∧ p₂.1 = insert x τ ∧ p₂.2 = D ∧
        (∀ k ∈ D.erase b, (ords k).lt (ordMin ords τ hnonempty k) x) ∧
        ¬ (ords b).lt (ordMin ords τ hnonempty b) x))) :
    p₁ ≠ p₂ := by
  obtain ⟨_, _, h1⟩ := hp₁
  obtain ⟨_, _, h2⟩ := hp₂
  rcases h1 with ⟨h1l, h1r⟩ | ⟨x₁, hx₁_nmem, h1l, h1r, hx₁_lt, hx₁_not⟩
  · rcases h2 with ⟨h2l, h2r⟩ | ⟨x₂, hx₂_nmem, h2l, h2r, hx₂_lt, hx₂_not⟩
    · intro heq
      have hsnd : D.erase a = D.erase b := by
        have := congr_arg Prod.snd heq; simp only [h1r, h2r] at this; exact this
      have : a ∈ D.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
      rw [← hsnd] at this
      exact absurd this (Finset.notMem_erase a D)
    · intro heq
      have hfst : τ = insert x₂ τ := by
        have := congr_arg Prod.fst heq; simp only [h1l, h2l] at this; exact this
      have : x₂ ∈ τ := hfst ▸ Finset.mem_insert_self x₂ τ
      exact hx₂_nmem this
  · rcases h2 with ⟨h2l, h2r⟩ | ⟨x₂, hx₂_nmem, h2l, h2r, hx₂_lt, hx₂_not⟩
    · intro heq
      have hfst : insert x₁ τ = τ := by
        have := congr_arg Prod.fst heq; simp only [h1l, h2l] at this; exact this
      have : x₁ ∈ τ := hfst ▸ Finset.mem_insert_self x₁ τ
      exact hx₁_nmem this
    · have hne_elts : x₁ ≠ x₂ :=
        insert_elements_ne_of_collision ords τ hnonempty D a b ha hab x₁ x₂ hx₁_not hx₂_lt
      intro heq
      have hfst : insert x₁ τ = insert x₂ τ := by
        have := congr_arg Prod.fst heq; simp only [h1l, h2l] at this; exact this
      have : x₁ ∈ insert x₂ τ := hfst ▸ Finset.mem_insert_self x₁ τ
      rcases Finset.mem_insert.mp this with rfl | hmem
      · exact hne_elts rfl
      · exact hx₁_nmem hmem

lemma i_mem_pair_ab {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hdoor : D.card = τ.card + 1)
    (hnonempty : τ.Nonempty)
    (a b : Fin (n + 1)) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hcoll : ordMin ords τ hnonempty a = ordMin ords τ hnonempty b)
    (i : Fin (n + 1)) (hi : i ∈ D)
    (hqi : isDominant ords τ (D.erase i)) :
    i = a ∨ i = b := by
  by_contra h
  push Not at h
  obtain ⟨hia, hib⟩ := h
  have ha' : a ∈ D.erase i := Finset.mem_erase.mpr ⟨Ne.symm hia, ha⟩
  have hb' : b ∈ D.erase i := Finset.mem_erase.mpr ⟨Ne.symm hib, hb⟩
  have hcard : (D.erase i).card = τ.card := by
    rw [Finset.card_erase_of_mem hi, hdoor]; omega
  have hsurj : τ ⊆ (D.erase i).image (ordMin ords τ hnonempty) := by
    intro t ht
    obtain ⟨j, hj, hjt⟩ := ordMin_surj_on_tau ords τ (D.erase i) hnonempty hqi t ht
    exact Finset.mem_image.mpr ⟨j, hj, hjt⟩
  have hinj : Set.InjOn (ordMin ords τ hnonempty) ↑(D.erase i) := by
    rw [← Finset.card_image_iff]
    have h1 := Finset.card_le_card hsurj
    have h2 := Finset.card_image_le (s := D.erase i) (f := ordMin ords τ hnonempty)
    omega
  exact absurd (hinj ha' hb' hcoll) hab

lemma insert_branch_absurd {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hnonempty : τ.Nonempty) (j : Fin (n + 1))
    (hqi : isDominant ords τ (D.erase j))
    (x : T) (hx : ∀ k ∈ D.erase j, (ords k).lt (ordMin ords τ hnonempty k) x) :
    False := by
  obtain ⟨k, hk_mem, hk_prop⟩ := hqi x
  exact hk_prop (ordMin ords τ hnonempty k) (ordMin_mem ords τ hnonempty k) (hx k hk_mem)

lemma erase_case_q_eq_p1_or_p2 {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hdoor : D.card = τ.card + 1)
    (hnonempty : τ.Nonempty)
    (a b : Fin (n + 1)) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hcoll : ordMin ords τ hnonempty a = ordMin ords τ hnonempty b)
    (p₁ p₂ : Finset T × Finset (Fin (n + 1)))
    (hp₁ : IsScarfVtx ords c i₀ p₁ ∧ scarfAdjRel (τ, D) p₁ ∧
      ((p₁.1 = τ ∧ p₁.2 = D.erase a) ∨
       (∃ x, x ∉ τ ∧ p₁.1 = insert x τ ∧ p₁.2 = D ∧
        (∀ k ∈ D.erase a, (ords k).lt (ordMin ords τ hnonempty k) x) ∧
        ¬ (ords a).lt (ordMin ords τ hnonempty a) x)))
    (hp₂ : IsScarfVtx ords c i₀ p₂ ∧ scarfAdjRel (τ, D) p₂ ∧
      ((p₂.1 = τ ∧ p₂.2 = D.erase b) ∨
       (∃ x, x ∉ τ ∧ p₂.1 = insert x τ ∧ p₂.2 = D ∧
        (∀ k ∈ D.erase b, (ords k).lt (ordMin ords τ hnonempty k) x) ∧
        ¬ (ords b).lt (ordMin ords τ hnonempty b) x)))
    (i : Fin (n + 1)) (hi : i ∈ D)
    (hqi : isDominant ords τ (D.erase i))
    (q : Finset T × Finset (Fin (n + 1)))
    (hq1 : q.1 = τ) (hq2 : q.2 = D.erase i) :
    q = p₁ ∨ q = p₂ := by
  have hmem : i = a ∨ i = b :=
    i_mem_pair_ab ords τ D hdoor hnonempty a b ha hb hab hcoll i hi hqi
  rcases hmem with hia | hib
  · left
    rw [hia] at hqi hq2
    rcases hp₁.2.2 with ⟨hp₁_fst, hp₁_snd⟩ | ⟨x, _, _, _, hxlt, _⟩
    · exact Prod.ext (hq1.trans hp₁_fst.symm) (hq2.trans hp₁_snd.symm)
    · exact absurd (insert_branch_absurd ords τ D hnonempty a hqi x hxlt) False.elim
  · right
    rw [hib] at hqi hq2
    rcases hp₂.2.2 with ⟨hp₂_fst, hp₂_snd⟩ | ⟨x, _, _, _, hxlt, _⟩
    · exact Prod.ext (hq1.trans hp₂_fst.symm) (hq2.trans hp₂_snd.symm)
    · exact absurd (insert_branch_absurd ords τ D hnonempty b hqi x hxlt) False.elim

lemma insert_dominant_gives_ordMin_conditions {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (x : T) (hx : x ∉ τ)
    (hdom_ins : isDominant ords (insert x τ) D)
    (hdoor : D.card = τ.card + 1)
    (hnonempty : τ.Nonempty) :
    ∃ i ∈ D, (∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x) ∧
      ¬ (ords i).lt (ordMin ords τ hnonempty i) x := by
  have hne' : (insert x τ).Nonempty := Finset.insert_nonempty x τ
  set f := ordMin ords (insert x τ) hne' with hf_def
  have hsurj : ∀ t ∈ insert x τ, ∃ i ∈ D, f i = t :=
    fun t ht ↦ ordMin_surj_on_tau ords (insert x τ) D hne' hdom_ins t ht
  have himg_supset : insert x τ ⊆ D.image f := by grind
  have himg_subset : D.image f ⊆ insert x τ := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨i, _, hfi⟩ := ht
    rw [← hfi]
    exact ordMin_mem ords (insert x τ) hne' i
  have himg_eq : D.image f = insert x τ :=
    Finset.Subset.antisymm himg_subset himg_supset
  have hcard_ins : (insert x τ).card = τ.card + 1 :=
    Finset.card_insert_of_notMem hx
  have hcard_img : (D.image f).card = D.card := by
    rw [himg_eq, hcard_ins, ← hdoor]
  have hinj : Set.InjOn f ↑D := Finset.card_image_iff.mp hcard_img
  obtain ⟨i, hiD, hfi⟩ := hsurj x (Finset.mem_insert_self x τ)
  refine ⟨i, hiD, ?_, ?_⟩
  · intro k hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hki, hkD⟩ := hk
    have hfk_ne_x : f k ≠ x := by
      intro heq; exact hki (hinj hkD hiD (by rw [heq, hfi]))
    have hfk_in_tau : f k ∈ τ :=
      (Finset.mem_insert.mp (ordMin_mem ords (insert x τ) hne' k)).resolve_left hfk_ne_x
    have hmin_le_tau : @LE.le T (ords k).toLE (f k) (ordMin ords τ hnonempty k) :=
      @Finset.min'_le T (ords k) (insert x τ) (ordMin ords τ hnonempty k)
        (Finset.mem_insert.mpr (Or.inr (ordMin_mem ords τ hnonempty k)))
    have htau_le_min : @LE.le T (ords k).toLE (ordMin ords τ hnonempty k) (f k) :=
      @Finset.min'_le T (ords k) τ (f k) hfk_in_tau
    have heq_mins : ordMin ords τ hnonempty k = f k :=
      @le_antisymm T (ords k).toPartialOrder _ _ htau_le_min hmin_le_tau
    have hfk_le_x : @LE.le T (ords k).toLE (f k) x :=
      @Finset.min'_le T (ords k) (insert x τ) x (Finset.mem_insert_self x τ)
    rw [heq_mins]
    exact @lt_of_le_of_ne T (ords k).toPartialOrder _ _ hfk_le_x hfk_ne_x
  · have hmin_i_mem : ordMin ords τ hnonempty i ∈ insert x τ :=
      Finset.mem_insert.mpr (Or.inr (ordMin_mem ords τ hnonempty i))
    have hx_le : @LE.le T (ords i).toLE x (ordMin ords τ hnonempty i) := by
      have := @Finset.min'_le T (ords i) (insert x τ) (ordMin ords τ hnonempty i) hmin_i_mem
      rwa [show @Finset.min' T (ords i) (insert x τ) hne' = x from hfi] at this
    exact @not_lt_of_ge T (ords i).toPreorder _ _ hx_le

lemma ordMin_insert_eq_of_lt {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (hne : τ.Nonempty)
    (k : Fin (n + 1)) (x : T)
    (hlt : (ords k).lt (ordMin ords τ hne k) x) :
    ordMin ords (insert x τ) (Finset.insert_nonempty x τ) k = ordMin ords τ hne k := by
  simp only [ordMin]
  have h := @Finset.min'_insert T (ords k) x τ hne
  have hmr := @min_eq_right T (ords k) _ _ (@le_of_lt T (ords k).toPreorder _ _ hlt)
  convert h.trans hmr using 2
  all_goals first | rfl | (ext y; simp [Finset.mem_insert])

lemma ordMin_conditions_not_outside_ab {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hdoor : D.card = τ.card + 1)
    (hnonempty : τ.Nonempty)
    (a b : Fin (n + 1)) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hcoll : ordMin ords τ hnonempty a = ordMin ords τ hnonempty b)
    (i : Fin (n + 1)) (hi : i ∈ D)
    (hia : i ≠ a) (hib : i ≠ b)
    (x : T) (hx : x ∉ τ)
    (hdom_ins : isDominant ords (insert x τ) D)
    (hx_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x) :
    False := by
  have hne_ins : (insert x τ).Nonempty := Finset.insert_nonempty x τ
  have hordMin_eq : ∀ k ∈ D.erase i,
      ordMin ords (insert x τ) hne_ins k = ordMin ords τ hnonempty k :=
    fun k hk ↦ ordMin_insert_eq_of_lt ords τ hnonempty k x (hx_Mi k hk)
  have ⟨jx, hjx_mem, hjx_eq⟩ := ordMin_surj_on_tau ords (insert x τ) D hne_ins hdom_ins x
    (Finset.mem_insert_self x τ)
  have hjx_eq_i : jx = i := by
    by_contra hjx_ne
    have hjx_ei : jx ∈ D.erase i := Finset.mem_erase.mpr ⟨hjx_ne, hjx_mem⟩
    have : ordMin ords (insert x τ) hne_ins jx = ordMin ords τ hnonempty jx := hordMin_eq jx hjx_ei
    rw [this] at hjx_eq
    exact hx (hjx_eq ▸ ordMin_mem ords τ hnonempty jx)
  have hsub : τ ⊆ (D.erase i).image (fun k ↦ ordMin ords τ hnonempty k) := by
    intro t ht
    have ht_ins : t ∈ insert x τ := Finset.mem_insert_of_mem ht
    obtain ⟨j, hj_mem, hj_eq⟩ := ordMin_surj_on_tau ords (insert x τ) D hne_ins hdom_ins t ht_ins
    grind
  have ha_ei : a ∈ D.erase i := Finset.mem_erase.mpr ⟨hia.symm, ha⟩
  have hb_ei : b ∈ D.erase i := Finset.mem_erase.mpr ⟨hib.symm, hb⟩
  have hcard_ei : (D.erase i).card = τ.card := by
    rw [Finset.card_erase_of_mem hi, hdoor]; omega
  have hninj : ¬ Set.InjOn (fun k ↦ ordMin ords τ hnonempty k) ↑(D.erase i) := by
    intro hinj
    exact absurd (hinj ha_ei hb_ei hcoll) hab
  have hlt : ((D.erase i).image (fun k ↦ ordMin ords τ hnonempty k)).card < τ.card := by
    rw [← hcard_ei]
    exact lt_of_le_of_ne Finset.card_image_le (fun h ↦ hninj (Finset.card_image_iff.mp h))
  have hle := Finset.card_le_card hsub
  omega

lemma ordMin_conditions_index_in_ab {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hdoor : D.card = τ.card + 1)
    (hnonempty : τ.Nonempty)
    (a b : Fin (n + 1)) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hcoll : ordMin ords τ hnonempty a = ordMin ords τ hnonempty b)
    (i : Fin (n + 1)) (hi : i ∈ D)
    (x : T) (hx : x ∉ τ)
    (hdom_ins : isDominant ords (insert x τ) D)
    (hx_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x) :
    i ∈ ({a, b} : Finset (Fin (n + 1))) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_contra h
  push Not at h
  exact ordMin_conditions_not_outside_ab ords τ D hdoor hnonempty a b ha hb hab hcoll
    i hi h.1 h.2 x hx hdom_ins hx_Mi

lemma x_maximal_in_Mi {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hnonempty : τ.Nonempty)
    (i : Fin (n + 1)) (hi : i ∈ D)
    (x : T)
    (hdom_x : isDominant ords (insert x τ) D)
    (hx_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x)
    (y : T) (hy_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) y) :
    ¬ (ords i).lt x y := by
  obtain ⟨k₀, hk₀D, hk₀_wit⟩ := hdom_x y
  by_cases hk₀ : k₀ = i
  · subst hk₀
    exact hk₀_wit x (Finset.mem_insert_self x τ)
  · have hk₀_erase : k₀ ∈ D.erase i := Finset.mem_erase.mpr ⟨hk₀, hk₀D⟩
    have hmin_mem : ordMin ords τ hnonempty k₀ ∈ τ := ordMin_mem ords τ hnonempty k₀
    have hmin_insert : ordMin ords τ hnonempty k₀ ∈ insert x τ :=
      Finset.mem_insert_of_mem hmin_mem
    have hmin_lt : (ords k₀).lt (ordMin ords τ hnonempty k₀) y := hy_Mi k₀ hk₀_erase
    exact absurd hmin_lt (hk₀_wit _ hmin_insert)

lemma insert_elements_equal {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (τ : Finset T) (D : Finset (Fin (n + 1))) (hnonempty : τ.Nonempty)
    (i : Fin (n + 1)) (hi : i ∈ D) (x x' : T)
    (hdom_x : isDominant ords (insert x τ) D)
    (hdom_x' : isDominant ords (insert x' τ) D)
    (hx_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x)
    (hx'_Mi : ∀ k ∈ D.erase i, (ords k).lt (ordMin ords τ hnonempty k) x') :
    x = x' := by
  by_contra hne
  have hlt_or := @lt_or_gt_of_ne T (ords i) x x' hne
  rcases hlt_or with h_lt | h_gt
  · exact absurd h_lt (x_maximal_in_Mi ords τ D hnonempty i hi x hdom_x hx_Mi x' hx'_Mi)
  · exact absurd h_gt (x_maximal_in_Mi ords τ D hnonempty i hi x' hdom_x' hx'_Mi x hx_Mi)

lemma insert_case_q_eq_p1_or_p2 {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hdoor : D.card = τ.card + 1)
    (hnonempty : τ.Nonempty)
    (a b : Fin (n + 1)) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hcoll : ordMin ords τ hnonempty a = ordMin ords τ hnonempty b)
    (huniq : ∀ c' ∈ D, ∀ d ∈ D, c' ≠ d →
      ordMin ords τ hnonempty c' = ordMin ords τ hnonempty d →
        ({c', d} : Finset (Fin (n + 1))) = {a, b})
    (p₁ p₂ : Finset T × Finset (Fin (n + 1)))
    (hp₁ : IsScarfVtx ords c i₀ p₁ ∧ scarfAdjRel (τ, D) p₁ ∧
      ((p₁.1 = τ ∧ p₁.2 = D.erase a) ∨
       (∃ x, x ∉ τ ∧ p₁.1 = insert x τ ∧ p₁.2 = D ∧
        (∀ k ∈ D.erase a, (ords k).lt (ordMin ords τ hnonempty k) x) ∧
        ¬ (ords a).lt (ordMin ords τ hnonempty a) x)))
    (hp₂ : IsScarfVtx ords c i₀ p₂ ∧ scarfAdjRel (τ, D) p₂ ∧
      ((p₂.1 = τ ∧ p₂.2 = D.erase b) ∨
       (∃ x, x ∉ τ ∧ p₂.1 = insert x τ ∧ p₂.2 = D ∧
        (∀ k ∈ D.erase b, (ords k).lt (ordMin ords τ hnonempty k) x) ∧
        ¬ (ords b).lt (ordMin ords τ hnonempty b) x)))
    (x : T) (hx : x ∉ τ)
    (hdom_ins : isDominant ords (insert x τ) D)
    (q : Finset T × Finset (Fin (n + 1)))
    (hq1 : q.1 = insert x τ) (hq2 : q.2 = D) :
    q = p₁ ∨ q = p₂ := by
  obtain ⟨i, hi, hx_Mi, hx_not_lt⟩ :=
    insert_dominant_gives_ordMin_conditions ords τ D x hx hdom_ins hdoor hnonempty
  have hi_ab := ordMin_conditions_index_in_ab ords τ D hdoor hnonempty a b ha hb hab
    hcoll i hi x hx hdom_ins hx_Mi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi_ab
  obtain hi_eq | hi_eq := hi_ab
  · subst hi_eq
    left
    obtain ⟨hp₁_scarf, hp₁_adj, hp₁_form⟩ := hp₁
    rcases hp₁_form with ⟨hp₁_fst, hp₁_snd⟩ | ⟨x₁, hx₁_nmem, hp₁_fst, hp₁_snd, hx₁_Mi, hx₁_not_lt⟩
    · exfalso
      have hdom_erase : isDominant ords τ (D.erase i) := by
        have := hp₁_scarf.2.1; rw [hp₁_fst, hp₁_snd] at this; exact this
      exact insert_branch_absurd ords τ D hnonempty i hdom_erase x hx_Mi
    · have hdom_x₁ : isDominant ords (insert x₁ τ) D := by
        rw [← hp₁_fst, ← hp₁_snd]; exact hp₁_scarf.2.1
      have hx_eq : x = x₁ :=
        insert_elements_equal ords τ D hnonempty i hi x x₁ hdom_ins hdom_x₁ hx_Mi hx₁_Mi
      ext1
      · simp [hq1, hp₁_fst, hx_eq]
      · simp [hq2, hp₁_snd]
  · subst hi_eq
    right
    obtain ⟨hp₂_scarf, hp₂_adj, hp₂_form⟩ := hp₂
    rcases hp₂_form with ⟨hp₂_fst, hp₂_snd⟩ | ⟨x₂, hx₂_nmem, hp₂_fst, hp₂_snd, hx₂_Mi, hx₂_not_lt⟩
    · exfalso
      have hdom_erase : isDominant ords τ (D.erase i) := by
        have := hp₂_scarf.2.1; rw [hp₂_fst, hp₂_snd] at this; exact this
      exact insert_branch_absurd ords τ D hnonempty i hdom_erase x hx_Mi
    · have hdom_x₂ : isDominant ords (insert x₂ τ) D := by
        rw [← hp₂_fst, ← hp₂_snd]; exact hp₂_scarf.2.1
      have hx_eq : x = x₂ :=
        insert_elements_equal ords τ D hnonempty i hi x x₂ hdom_ins hdom_x₂ hx_Mi hx₂_Mi
      ext1
      · simp [hq1, hp₂_fst, hx_eq]
      · simp [hq2, hp₂_snd]

lemma scarf_neighbor_uniqueness {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hdoor : D.card = τ.card + 1)
    (hnonempty : τ.Nonempty)
    (a b : Fin (n + 1)) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hcoll : ordMin ords τ hnonempty a = ordMin ords τ hnonempty b)
    (huniq : ∀ c' ∈ D, ∀ d ∈ D, c' ≠ d →
      ordMin ords τ hnonempty c' = ordMin ords τ hnonempty d →
        ({c', d} : Finset (Fin (n + 1))) = {a, b})
    (p₁ p₂ : Finset T × Finset (Fin (n + 1)))
    (hp₁ : IsScarfVtx ords c i₀ p₁ ∧ scarfAdjRel (τ, D) p₁ ∧
      ((p₁.1 = τ ∧ p₁.2 = D.erase a) ∨
       (∃ x, x ∉ τ ∧ p₁.1 = insert x τ ∧ p₁.2 = D ∧
        (∀ k ∈ D.erase a, (ords k).lt (ordMin ords τ hnonempty k) x) ∧
        ¬ (ords a).lt (ordMin ords τ hnonempty a) x)))
    (hp₂ : IsScarfVtx ords c i₀ p₂ ∧ scarfAdjRel (τ, D) p₂ ∧
      ((p₂.1 = τ ∧ p₂.2 = D.erase b) ∨
       (∃ x, x ∉ τ ∧ p₂.1 = insert x τ ∧ p₂.2 = D ∧
        (∀ k ∈ D.erase b, (ords k).lt (ordMin ords τ hnonempty k) x) ∧
        ¬ (ords b).lt (ordMin ords τ hnonempty b) x)))
    (q : Finset T × Finset (Fin (n + 1)))
    (hqscarf : IsScarfVtx ords c i₀ q)
    (hqadj : scarfAdjRel (τ, D) q) :
    q = p₁ ∨ q = p₂ := by
  obtain hinsert | herase := adj_door_neighbor_form ords c i₀ τ D hdoor q hqscarf hqadj
  · obtain ⟨x, hx, hq1, hq2, hdom_ins⟩ := hinsert
    have hqscarf' : IsScarfVtx ords c i₀ (insert x τ, D) := by
      rwa [show q = (insert x τ, D) from Prod.ext hq1 hq2] at hqscarf
    exact insert_case_q_eq_p1_or_p2 ords c i₀ τ D hdoor hnonempty
      a b ha hb hab hcoll huniq p₁ p₂ hp₁ hp₂ x hx hdom_ins q hq1 hq2
  · obtain ⟨i, hi, hq1, hq2, hdom_er⟩ := herase
    exact erase_case_q_eq_p1_or_p2 ords c i₀ τ D hdoor hnonempty
      a b ha hb hab hcoll p₁ p₂ hp₁ hp₂ i hi hdom_er q hq1 hq2

lemma scarf_internal_door_two_adj_pairs {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (τ : Finset T) (D : Finset (Fin (n + 1)))
    (hne : D.Nonempty) (hdom : isDominant ords τ D)
    (hdoor : D.card = τ.card + 1)
    (hnearly : D \ τ.image c = {i₀})
    (hnonempty : τ.Nonempty) :
    ∃ p₁ p₂ : Finset T × Finset (Fin (n + 1)),
      p₁ ≠ p₂ ∧
      IsScarfVtx ords c i₀ p₁ ∧ scarfAdjRel (τ, D) p₁ ∧
      IsScarfVtx ords c i₀ p₂ ∧ scarfAdjRel (τ, D) p₂ ∧
      (∀ q : Finset T × Finset (Fin (n + 1)),
        IsScarfVtx ords c i₀ q → scarfAdjRel (τ, D) q → q = p₁ ∨ q = p₂) := by
  -- Step 1: Get the unique collision pair (a, b) from pigeonhole
  obtain ⟨a, ha, b, hb, hab, hcoll, huniq⟩ := ordMin_unique_collision ords τ D hnonempty hdom hdoor
  -- Step 2: Get the two neighbors from collision indices a and b
  obtain ⟨p₁, hp₁scarf, hp₁adj, hp₁form⟩ :=
    scarf_neighbor_from_collision_index ords c i₀ τ D hne hdom hdoor hnearly hnonempty
      a b ha hb hab hcoll huniq a (Finset.mem_insert_self a {b})
  obtain ⟨p₂, hp₂scarf, hp₂adj, hp₂form⟩ :=
    scarf_neighbor_from_collision_index ords c i₀ τ D hne hdom hdoor hnearly hnonempty
      a b ha hb hab hcoll huniq b (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  -- Step 3: Show they are distinct
  have hdist : p₁ ≠ p₂ :=
    scarf_two_neighbors_distinct ords c i₀ τ D hnonempty a b ha hab p₁ p₂
      ⟨hp₁scarf, hp₁adj, hp₁form⟩ ⟨hp₂scarf, hp₂adj, hp₂form⟩
  -- Step 4: Show uniqueness
  exact ⟨p₁, p₂, hdist, hp₁scarf, hp₁adj, hp₂scarf, hp₂adj,
    fun q hqscarf hqadj ↦
      scarf_neighbor_uniqueness ords c i₀ τ D hdoor hnonempty a b ha hb hab hcoll huniq p₁ p₂
        ⟨hp₁scarf, hp₁adj, hp₁form⟩ ⟨hp₂scarf, hp₂adj, hp₂form⟩ q hqscarf hqadj⟩

lemma scarf_degree_internal_door {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (hdoor : v.val.2.card = v.val.1.card + 1)
    (hnearly : v.val.2 \ v.val.1.image c = {i₀})
    (hnonempty : v.val.1.Nonempty) :
    G.degree v = 2 := by
  obtain ⟨hDne, hdom, _⟩ := v.prop
  obtain ⟨p₁, p₂, hne, hp₁, hadj₁, hp₂, hadj₂, huniq⟩ :=
    scarf_internal_door_two_adj_pairs ords c i₀ v.val.1 v.val.2 hDne hdom hdoor hnearly hnonempty
  exact scarf_degree_of_two_adj_pairs ords c i₀ G hG v p₁ p₂ hne hp₁ hadj₁ hp₂ hadj₂ huniq

lemma scarf_degree_one_or_two {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val) :
    ∀ v, G.degree v = 1 ∨ G.degree v = 2 := by
  intro v
  obtain ⟨hne, hdom, htype⟩ := v.prop
  rcases htype with ⟨hcard, hcolor⟩ | ⟨hcard, hnearly⟩ | ⟨hdoor, hnearly⟩
  · exact Or.inl (scarf_degree_colorful_room ords c i₀ G hG v hcard hcolor)
  · exact Or.inr (scarf_degree_nearly_colorful_room ords c i₀ G hG v hcard hnearly)
  · rcases Finset.eq_empty_or_nonempty v.val.1 with hempty | hnonempty
    · exact Or.inl (scarf_degree_outside_door ords c i₀ G hG v hdoor hnearly hempty)
    · exact Or.inr (scarf_degree_internal_door ords c i₀ G hG v hdoor hnearly hnonempty)

lemma scarfAdjRel_symm {n : ℕ} {T : Type} [DecidableEq T]
    (v w : Finset T × Finset (Fin (n + 1)))
    (h : scarfAdjRel v w) : scarfAdjRel w v := by
  grind [scarfAdjRel]

lemma empty_singleton_isScarfVtx {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1)) :
    IsScarfVtx ords c i₀ (∅, {i₀}) := by
  dsimp [IsScarfVtx, isDominant]
  constructor
  · -- Prove that {i₀} is nonempty
    exact Finset.singleton_nonempty i₀
  constructor
  · -- Prove that ∅ is dominant with respect to {i₀}
    intro y
    use i₀
    simp
  · -- Prove the third disjunct: {i₀}.card = ∅.card + 1 and {i₀} \ ∅.image c = {i₀}
    simp [Finset.card_singleton, Finset.ext_iff]

lemma scarfAdjRel_v0_max {n : ℕ} {T : Type} [DecidableEq T]
    (i₀ : Fin (n + 1))
    (x_max : T) :
    scarfAdjRel ((∅ : Finset T), ({i₀} : Finset (Fin (n + 1)))) ({x_max}, {i₀}) := by
  refine ⟨?_, Or.inr ⟨?_, Or.inl ⟨x_max, ?_, ?_, ?_⟩⟩⟩
  · intro h; have := congr_arg Prod.fst h; simp at this
  · simp
  · simp
  · simp
  · rfl

lemma scarfAdjRel_v0_iff {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (w : Finset T × Finset (Fin (n + 1)))
    (hw : IsScarfVtx ords c i₀ w) :
    scarfAdjRel (∅, {i₀}) w ↔
      (∃ x : T, (∀ y : T, ¬ (ords i₀).lt x y) ∧
        w = ({x}, {i₀})) := by
  constructor
  · intro ⟨hne, hadj⟩
    rcases hadj with ⟨hcard, _⟩ | ⟨hcard, hadj'⟩
    · -- Case 1: v₀ = (∅, {i₀}) is a room: |∅| = |{i₀}|, but 0 ≠ 1
      simp at hcard
    · -- Case 2: w is a room
      rcases hadj' with ⟨x, hx, hv1, hv2⟩ | ⟨i, hi, hv1, hv2⟩
      · -- Sub-case 2a: ∃ x ∈ w.1, ∅ = w.1.erase x ∧ {i₀} = w.2
        have hw1 : w.1 = {x} := by
          ext a; simp only [Finset.mem_singleton]
          constructor
          · intro ha
            by_contra hne'
            have hmem : a ∈ w.1.erase x := Finset.mem_erase.mpr ⟨hne', ha⟩
            rw [← hv1] at hmem; exact absurd hmem (Finset.notMem_empty _)
          · intro ha; subst ha; exact hx
        have hw_eq : w = ({x}, {i₀}) := Prod.ext hw1 hv2.symm
        refine ⟨x, ?_, hw_eq⟩
        intro y
        have hdom := hw.2.1
        rw [hw_eq] at hdom
        obtain ⟨j, hj, hj'⟩ := hdom y
        rw [Finset.mem_singleton] at hj; subst hj
        exact hj' x (Finset.mem_singleton_self x)
      · -- Sub-case 2b: ∃ i ∉ w.2, ∅ = w.1 ∧ {i₀} = insert i w.2
        rw [← hv1] at hcard; simp at hcard
        have : w.2 = ∅ := Finset.card_eq_zero.mp hcard.symm
        exact absurd (this ▸ hw.1) Finset.not_nonempty_empty
  · intro ⟨x, _, hw_eq⟩
    subst hw_eq
    exact scarfAdjRel_v0_max i₀ x

lemma exists_unique_max {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    (ords : Fin (n + 1) → LinearOrder T)
    (i₀ : Fin (n + 1)) :
    ∃! x : T, ∀ y : T, ¬ (ords i₀).lt x y := by
  let : LinearOrder T := ords i₀
  refine ⟨Finset.max' Finset.univ Finset.univ_nonempty, ?_, ?_⟩
  · intro y
    exact not_lt.mpr (Finset.le_max' _ _ (Finset.mem_univ y))
  · intro x hx
    apply le_antisymm
    · exact Finset.le_max' _ _ (Finset.mem_univ x)
    · exact not_lt.mp (hx (Finset.max' Finset.univ Finset.univ_nonempty))

lemma max_isScarfVtx {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (x_max : T) (hmax : ∀ y : T, ¬ (ords i₀).lt x_max y) :
    IsScarfVtx ords c i₀ ({x_max}, {i₀}) := by
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · intro y
    exact ⟨i₀, Finset.mem_singleton_self _, fun x hx ↦ by grind⟩
  · grind

lemma scarf_v0_degree_one {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v₀ : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (hv₀ : v₀.val = (∅, {i₀})) :
    G.degree v₀ = 1 := by
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  obtain ⟨x_max, hmax, huniq⟩ := exists_unique_max ords i₀
  have hscarf : IsScarfVtx ords c i₀ ({x_max}, {i₀}) := max_isScarfVtx ords c i₀ x_max hmax
  let w₀ : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p } :=
    ⟨({x_max}, {i₀}), hscarf⟩
  refine ⟨w₀, ?_, ?_⟩
  · exact (hG v₀ w₀).mpr (hv₀ ▸ scarfAdjRel_v0_max i₀ x_max)
  · intro w hw
    have hw' := (hG v₀ w).mp hw
    rw [hv₀] at hw'
    have := (scarfAdjRel_v0_iff ords c i₀ w.val w.property).mp hw'
    obtain ⟨x, hx_max, hx_eq⟩ := this
    have : x = x_max := huniq x hx_max
    subst this
    exact Subtype.ext hx_eq

def μ' {n : ℕ} {T : Type} (ords : Fin (n + 1) → LinearOrder T)
    (σ : Finset T) (hσne : σ.Nonempty) (i : Fin (n + 1)) : T :=
  @Finset.min' T (ords i) σ hσne

def admSet {n : ℕ} {T : Type} [Fintype T]
    (ords : Fin (n + 1) → LinearOrder T) (σ : Finset T)
    (hσne : σ.Nonempty) (CC : Finset (Fin (n + 1))) (i : Fin (n + 1)) : Finset T :=
  Finset.univ.filter fun y ↦ ∀ k ∈ CC.erase i, (ords k).lt (μ' ords σ hσne k) y

/-- If τ ⊆ σ and σ is dominant w.r.t. C, then τ is dominant w.r.t. C.
    isDominant requires ∀ y, ∃ i ∈ C, ∀ x ∈ σ, ¬(ords i).lt x y.
    Since τ ⊆ σ, the inner quantifier ∀ x ∈ τ becomes weaker, so dominance is preserved.
    No direct Mathlib equivalent found. Searched: isDominant, dominant, Finset monotone. -/
lemma isDominant_subset {n : ℕ} {T : Type}
    (ords : Fin (n + 1) → LinearOrder T)
    (σ τ : Finset T) (C : Finset (Fin (n + 1)))
    (hsub : τ ⊆ σ) (hdom : isDominant ords σ C) :
    isDominant ords τ C := by
  intro y; obtain ⟨i, hi, hmin⟩ := hdom y; exact ⟨i, hi, fun x hx ↦ hmin x (hsub hx)⟩

/-- If σ is dominant w.r.t. C and C ⊆ D, then σ is dominant w.r.t. D.
    isDominant requires ∀ y, ∃ i ∈ C, ∀ x ∈ σ, ¬(ords i).lt x y.
    Since C ⊆ D, the witness i ∈ C also satisfies i ∈ D.
    No direct Mathlib equivalent found. Searched: isDominant, dominant, Finset supset. -/
lemma isDominant_supset {n : ℕ} {T : Type}
    (ords : Fin (n + 1) → LinearOrder T)
    (σ : Finset T) (C D : Finset (Fin (n + 1)))
    (hsub : C ⊆ D) (hdom : isDominant ords σ C) :
    isDominant ords σ D := by
  intro y; obtain ⟨i, hi, hmin⟩ := hdom y; exact ⟨i, hsub hi, hmin⟩

/-- admSet(a) and admSet(b) are disjoint for distinct a, b ∈ CC when σ is dominant w.r.t. CC.
    If y ∈ admSet(a) ∩ admSet(b), then ∀ k ∈ CC, μ'(k) <_k y, contradicting isDominant.
    Uses `Finset.disjoint_filter`, `Finset.min'_mem`, `Finset.mem_erase`.
    No direct Mathlib equivalent. -/
lemma admSet_disjoint {n : ℕ} {T : Type} [Fintype T]
    (ords : Fin (n + 1) → LinearOrder T)
    (σ : Finset T) (CC : Finset (Fin (n + 1)))
    (hσne : σ.Nonempty)
    (hDom : isDominant ords σ CC)
    (a b : Fin (n + 1)) (hab : a ≠ b) :
    Disjoint (admSet ords σ hσne CC a) (admSet ords σ hσne CC b) := by
  simp only [admSet]
  rw [Finset.disjoint_filter]
  intro y _ hya hyb
  have : ∀ k ∈ CC, (ords k).lt (μ' ords σ hσne k) y := by grind
  obtain ⟨i, hi, hmin⟩ := hDom y
  exact hmin _ (@Finset.min'_mem T (ords i) σ hσne) (this i hi)

/-- If admSet(i) = ∅, then σ is dominant w.r.t. CC.erase i.
    For every y, y ∉ admSet(i) means ∃ k ∈ CC.erase i with ¬(μ'(k) <_k y).
    Since μ'(k) ≤ x for all x ∈ σ, this gives ¬(x <_k y), establishing dominance.
    Uses `Finset.min'_le`, `lt_of_le_of_lt`.
    No direct Mathlib equivalent. -/
lemma isDominant_erase_of_admSet_empty {n : ℕ} {T : Type} [Fintype T]
    (ords : Fin (n + 1) → LinearOrder T)
    (σ : Finset T) (CC : Finset (Fin (n + 1)))
    (hσne : σ.Nonempty)
    (i : Fin (n + 1))
    (hempty : admSet ords σ hσne CC i = ∅) :
    isDominant ords σ (CC.erase i) := by
  intro y
  have hy : y ∉ admSet ords σ hσne CC i := by rw [hempty]; exact Finset.notMem_empty _
  simp only [admSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  have hy' : ∃ k ∈ CC.erase i, ¬(ords k).lt (μ' ords σ hσne k) y := by grind
  obtain ⟨k, hk, hle⟩ := hy'
  exact ⟨k, hk, fun x hx hxy ↦
    hle (@lt_of_le_of_lt T (ords k).toPreorder _ _ _ (@Finset.min'_le T (ords k) σ x hx) hxy)⟩

/-- If (σ, CC) is a nearly colorful door and σ is dominant w.r.t. CC.erase i, then
    (σ, CC.erase i) is IsScarfVtx. Room has σ.card = (CC.erase i).card. The sdiff
    (CC.erase i) \ σ.image c ⊆ CC \ σ.image c = {i₀}, giving colorful or nearly colorful.
    Uses `Finset.card_erase_of_mem`, `Finset.sdiff_subset_sdiff`, `Finset.eq_of_subset_of_card_le`,
    `Finset.eq_singleton_iff_nonempty_unique_mem`.
    No direct Mathlib equivalent. -/
lemma isScarfVtx_erase {n : ℕ} {T : Type} [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (CC : Finset (Fin (n + 1)))
    (hσne : σ.Nonempty)
    (i : Fin (n + 1)) (hi : i ∈ CC)
    (hDom_erase : isDominant ords σ (CC.erase i))
    (hdoor_card : CC.card = σ.card + 1)
    (hnear : CC \ σ.image c = {i₀}) :
    IsScarfVtx ords c i₀ (σ, CC.erase i) := by
  have hCe_ne : (CC.erase i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    have : CC.card ≤ 1 := by
      rw [← Finset.card_erase_add_one hi, h]; simp
    have := Finset.card_pos.mpr hσne
    omega
  have hcard_room : σ.card = (CC.erase i).card := by
    rw [Finset.card_erase_of_mem hi]; omega
  refine ⟨hCe_ne, hDom_erase, ?_⟩
  have hsub : (CC.erase i) \ σ.image c ⊆ CC \ σ.image c :=
    Finset.sdiff_subset_sdiff (Finset.erase_subset _ _) Finset.Subset.rfl
  rw [hnear] at hsub
  cases Finset.eq_empty_or_nonempty ((CC.erase i) \ σ.image c) with
  | inl h =>
    left
    rw [Finset.sdiff_eq_empty_iff_subset] at h
    constructor
    · show σ.card = (CC.erase i).card; exact hcard_room
    · show CC.erase i = σ.image c
      have hle : (σ.image c).card ≤ (CC.erase i).card :=
        le_trans Finset.card_image_le (le_of_eq hcard_room)
      exact Finset.eq_of_subset_of_card_le h hle
  | inr h =>
    right; left
    constructor
    · show σ.card = (CC.erase i).card; exact hcard_room
    · show (CC.erase i) \ σ.image c = {i₀}
      exact Finset.eq_singleton_iff_nonempty_unique_mem.mpr
        ⟨h, fun x hx ↦ Finset.mem_singleton.mp (hsub hx)⟩

/-- If m is the max of admSet(i) and m ∈ admSet(i), then insert m σ is dominant w.r.t. CC.
    For k ≠ i, μ'(k) <_k m so min_k stays μ'(k). For k = i, m <_i μ'(i). If ∃ y with
    all new mins <_k y, then y ∈ admSet(i) with m <_i y, contradicting maximality.
    Uses `lt_trans`, `lt_of_le_of_lt`, `Finset.min'_le`, `Finset.min'_mem`, `Finset.mem_insert`.
    No direct Mathlib equivalent. -/
lemma isDominant_insert_of_admSet_max {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (σ : Finset T) (CC : Finset (Fin (n + 1)))
    (hσne : σ.Nonempty)
    (hDom : isDominant ords σ CC)
    (i : Fin (n + 1)) (hi : i ∈ CC)
    (m : T) (hm_adm : m ∈ admSet ords σ hσne CC i)
    (hm_max : ∀ y ∈ admSet ords σ hσne CC i, ¬ (ords i).lt m y) :
    isDominant ords (insert m σ) CC := by
  simp only [admSet, Finset.mem_filter, Finset.mem_univ, true_and] at hm_adm hm_max
  by_contra hnd
  simp only [isDominant, not_forall] at hnd
  obtain ⟨y, hy⟩ := hnd
  simp only [not_exists, not_and, not_forall, not_not] at hy
  have h_adm_y : ∀ k ∈ CC.erase i, (ords k).lt (μ' ords σ hσne k) y := by
    intro k hk
    obtain ⟨x, hx, hlt⟩ := hy k (Finset.mem_of_mem_erase hk)
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact @lt_trans T (ords k).toPreorder _ _ _ (hm_adm k hk) hlt
    · exact @lt_of_le_of_lt T (ords k).toPreorder _ _ _
        (@Finset.min'_le T (ords k) σ x hx) hlt
  obtain ⟨x, hx, hlt_i⟩ := hy i hi
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact hm_max y h_adm_y hlt_i
  · have hμi_lt : (ords i).lt (μ' ords σ hσne i) y :=
      @lt_of_le_of_lt T (ords i).toPreorder _ _ _
        (@Finset.min'_le T (ords i) σ x hx) hlt_i
    have hall : ∀ k ∈ CC, (ords k).lt (μ' ords σ hσne k) y := by grind
    obtain ⟨k, hk, hmin⟩ := hDom y
    exact hmin _ (@Finset.min'_mem T (ords k) σ hσne) (hall k hk)

/-- If m ∈ admSet(i) for i ∈ {a,b} with μ'(a) = μ'(b) and a ≠ b, then m ∉ σ.
    If m ∈ σ, by dominance m = μ'(j) for some j. If j ≠ i, get μ'(j) <_j m = μ'(j),
    contradiction. If j = i, use μ'(a) = μ'(b) to get similar contradiction.
    Uses `Finset.min'_mem`, `Finset.min'_le`, `le_antisymm`, `lt_irrefl`, `le_of_not_lt`.
    No direct Mathlib equivalent. -/
lemma m_not_mem_σ_aux {n : ℕ} {T : Type} [Fintype T]
    (ords : Fin (n + 1) → LinearOrder T)
    (σ : Finset T) (CC : Finset (Fin (n + 1)))
    (hσne : σ.Nonempty)
    (hDom : isDominant ords σ CC)
    (a b : Fin (n + 1)) (ha : a ∈ CC) (hb : b ∈ CC) (hab : a ≠ b)
    (hμeq : μ' ords σ hσne a = μ' ords σ hσne b)
    (i : Fin (n + 1)) (hi_ab : i = a ∨ i = b)
    (m : T) (hm_adm : m ∈ admSet ords σ hσne CC i) (hm_σ : m ∈ σ) :
    False := by
  simp only [admSet, Finset.mem_filter, Finset.mem_univ, true_and] at hm_adm
  obtain ⟨j, hj, hmin_j⟩ := hDom m
  have hj_not_lt : ¬(ords j).lt (μ' ords σ hσne j) m :=
    hmin_j _ (@Finset.min'_mem T (ords j) σ hσne)
  have hji : j = i := by
    by_contra hne_ji
    exact hj_not_lt (hm_adm j (Finset.mem_erase.mpr ⟨hne_ji, hj⟩))
  have hj_not_lt_i : ¬(ords i).lt (μ' ords σ hσne i) m := hji ▸ hj_not_lt
  have hμi_le : (ords i).le (μ' ords σ hσne i) m :=
    @Finset.min'_le T (ords i) σ m hm_σ
  have hm_le_μ : (ords i).le m (μ' ords σ hσne i) :=
    @le_of_not_gt T (ords i) m _ hj_not_lt_i
  have hm_eq : m = μ' ords σ hσne i :=
    @le_antisymm T (ords i).toPartialOrder m _ hm_le_μ hμi_le
  rcases hi_ab with rfl | rfl
  · have hlt_b := hm_adm b (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)
    rw [hm_eq, hμeq] at hlt_b
    exact @lt_irrefl T (ords b).toPreorder _ hlt_b
  · have hlt_a := hm_adm a (Finset.mem_erase.mpr ⟨hab, ha⟩)
    rw [hm_eq, ← hμeq] at hlt_a
    exact @lt_irrefl T (ords a).toPreorder _ hlt_a

/-- If G.Adj v w₁ and G.Adj v w₂ with w₁ ≠ w₂, then G.degree v ≥ 2.
    Uses `Finset.card_pair`, `Finset.card_le_card`, `SimpleGraph.card_neighborFinset_eq_degree`.
    No direct Mathlib equivalent as a combined statement. -/
lemma degree_ge_two_of_two_adj {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v w₁ w₂ : V) (h1 : G.Adj v w₁) (h2 : G.Adj v w₂) (hne : w₁ ≠ w₂) :
    2 ≤ G.degree v := by
  have hsub : {w₁, w₂} ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, SimpleGraph.mem_neighborFinset] at hx ⊢
    rcases hx with rfl | rfl <;> assumption
  calc 2 = ({w₁, w₂} : Finset V).card := (Finset.card_pair hne).symm
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub
    _ = G.degree v := G.card_neighborFinset_eq_degree v

/-- If q satisfies IsScarfVtx and scarfAdjRel v.val q holds, then G.Adj v ⟨q, hq⟩.
    Direct application of hG. -/
lemma mk_adj_of_scarfAdjRel {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1)) (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (q : Finset T × Finset (Fin (n + 1)))
    (hq : IsScarfVtx ords c i₀ q)
    (hadj : scarfAdjRel v.val q) :
    G.Adj v ⟨q, hq⟩ := by
  rw [hG]; exact hadj

/-- If m ∉ σ, insert m σ is dominant w.r.t. CC, CC.card = σ.card + 1, CC \ σ.image c = {i₀},
    then (insert m σ, CC) is IsScarfVtx. Card: (insert m σ).card = CC.card. Sdiff:
    CC \ (insert m σ).image c ⊆ CC \ σ.image c = {i₀}.
    Uses `Finset.card_insert_of_notMem`, `Finset.sdiff_subset_sdiff`,
    `Finset.eq_of_subset_of_card_le`, `Finset.eq_singleton_iff_nonempty_unique_mem`.
    No direct Mathlib equivalent. -/
lemma isScarfVtx_insert {n : ℕ} {T : Type} [Fintype T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (σ : Finset T) (CC : Finset (Fin (n + 1)))
    (m : T) (hm_not_mem : m ∉ σ)
    (hCne : CC.Nonempty) (hDom_ins : isDominant ords (insert m σ) CC)
    (hdoor_card : CC.card = σ.card + 1)
    (hnear : CC \ σ.image c = {i₀}) :
    IsScarfVtx ords c i₀ (insert m σ, CC) := by
  constructor
  · exact hCne
  constructor
  · exact hDom_ins
  have hcard : (insert m σ).card = CC.card := by
    rw [Finset.card_insert_of_notMem hm_not_mem]; omega
  have hsub : CC \ (insert m σ).image c ⊆ CC \ σ.image c :=
    Finset.sdiff_subset_sdiff Finset.Subset.rfl
      (Finset.image_subset_image (Finset.subset_insert _ _))
  rw [hnear] at hsub
  cases Finset.eq_empty_or_nonempty (CC \ (insert m σ).image c) with
  | inl h =>
    left
    rw [Finset.sdiff_eq_empty_iff_subset] at h
    show (insert m σ).card = CC.card ∧ CC = (insert m σ).image c
    exact ⟨hcard, Finset.eq_of_subset_of_card_le h
      (le_trans Finset.card_image_le (le_of_eq hcard))⟩
  | inr h =>
    right; left
    show (insert m σ).card = CC.card ∧ CC \ (insert m σ).image c = {i₀}
    exact ⟨hcard, Finset.eq_singleton_iff_nonempty_unique_mem.mpr
        ⟨h, fun x hx ↦ Finset.mem_singleton.mp (hsub hx)⟩⟩

/-- If c is injective on σ and y ∈ σ, then (σ.erase y).image c = (σ.image c).erase (c y).
    Uses `Set.InjOn c ↑σ` to ensure c(y) is uniquely realized by y.
    No direct Mathlib equivalent. -/
lemma image_erase_of_injOn' {T : Type} [DecidableEq T] {n : ℕ}
    (σ : Finset T) (c : T → Fin (n + 1))
    (y : T) (hy : y ∈ σ) (hinj : Set.InjOn c ↑σ) :
    (σ.erase y).image c = (σ.image c).erase (c y) := by
  ext j; simp only [Finset.mem_image, Finset.mem_erase]; constructor
  · rintro ⟨a, ⟨hay, ha⟩, rfl⟩
    exact ⟨fun h ↦ hay (hinj ha hy h), a, ha, rfl⟩
  · rintro ⟨hjcy, a, ha, rfl⟩
    exact ⟨a, ⟨fun h ↦ hjcy (h ▸ rfl), ha⟩, rfl⟩

/-- If CC \ Im = {i₀} and j ∉ CC, then CC \ Im.erase j = {i₀}.
    Erasing j from Im cannot affect the sdiff since j ∉ CC.
    Uses `Finset.mem_sdiff`, `Finset.mem_erase`, `Finset.mem_singleton`.
    No direct Mathlib equivalent. -/
lemma sdiff_erase_of_not_mem {α : Type} [DecidableEq α]
    (CC Im : Finset α) (i₀ j : α) (hj : j ∉ CC)
    (h : CC \ Im = {i₀}) :
    CC \ Im.erase j = {i₀} := by
  grind

/-- If CC \ Im = {i₀} and j ∈ Im, then (insert j CC) \ Im = {i₀}.
    Uses `Finset.insert_sdiff_of_mem : a ∈ t → insert a s \ t = s \ t`. -/
lemma insert_sdiff_of_mem' {α : Type} [DecidableEq α]
    (CC Im : Finset α) (i₀ j : α) (hj : j ∈ Im)
    (h : CC \ Im = {i₀}) :
    (insert j CC) \ Im = {i₀} := by
  rw [Finset.insert_sdiff_of_mem _ hj]; exact h

/-- An internal nearly colorful door has degree ≥ 2 in the Scarf graph.
    By pigeonhole, ∃ distinct a, b ∈ CC with μ'(a) = μ'(b). For each i ∈ {a,b}:
    if admSet(i) = ∅, room is (σ, CC.erase i); if admSet(i) ≠ ∅, room is (insert m_i σ, CC).
    The two rooms are distinct (admSet disjointness or different components) and adjacent.
    Uses `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`, `Finset.max'_mem`, `Finset.le_max'`.
    No direct Mathlib equivalent. -/
lemma internal_door_degree_ge_two {n : ℕ} {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (σ : Finset T) (CC : Finset (Fin (n + 1)))
    (hv : v.val = (σ, CC))
    (hCne : CC.Nonempty) (hDom : isDominant ords σ CC)
    (hdoor_card : CC.card = σ.card + 1)
    (hnear : CC \ σ.image c = {i₀})
    (hσne : σ.Nonempty) :
    2 ≤ G.degree v := by
  -- Pigeonhole: find a ≠ b ∈ CC with μ'(a) = μ'(b)
  have hμ_maps : ∀ k ∈ CC, μ' ords σ hσne k ∈ σ :=
    fun k _ ↦ @Finset.min'_mem T (ords k) σ hσne
  have hcard_lt : σ.card < CC.card := by omega
  obtain ⟨a, ha, b, hb, hab, hμeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard_lt hμ_maps
  -- For each i ∈ {a,b}, construct a room adjacent to (σ, CC)
  -- Construct room for a
  by_cases ha_empty : admSet ords σ hσne CC a = ∅
  · -- admSet(a) = ∅ → room is (σ, CC.erase a)
    have hDom_ea := isDominant_erase_of_admSet_empty ords σ CC hσne a ha_empty
    have hvtx_a := isScarfVtx_erase ords c i₀ σ CC hσne a ha hDom_ea hdoor_card hnear
    by_cases hb_empty : admSet ords σ hσne CC b = ∅
    · -- Both empty → rooms are (σ, CC.erase a) and (σ, CC.erase b)
      have hDom_eb := isDominant_erase_of_admSet_empty ords σ CC hσne b hb_empty
      have hvtx_b := isScarfVtx_erase ords c i₀ σ CC hσne b hb hDom_eb hdoor_card hnear
      have hadj_a : scarfAdjRel v.val (σ, CC.erase a) := by
        rw [hv]; show scarfAdjRel (σ, CC) (σ, CC.erase a)
        refine ⟨?_, Or.inr ⟨?_, Or.inr ⟨a, Finset.notMem_erase a CC, rfl,
          (Finset.insert_erase ha).symm⟩⟩⟩
        · intro h
          have : CC.card = (CC.erase a).card := congr_arg Finset.card (congr_arg Prod.snd h)
          have := Finset.card_erase_lt_of_mem ha; omega
        · show σ.card = (CC.erase a).card
          rw [Finset.card_erase_of_mem ha]; omega
      have hadj_b : scarfAdjRel v.val (σ, CC.erase b) := by
        rw [hv]; show scarfAdjRel (σ, CC) (σ, CC.erase b)
        refine ⟨?_, Or.inr ⟨?_, Or.inr ⟨b, Finset.notMem_erase b CC, rfl,
          (Finset.insert_erase hb).symm⟩⟩⟩
        · intro h
          have : CC.card = (CC.erase b).card := congr_arg Finset.card (congr_arg Prod.snd h)
          have := Finset.card_erase_lt_of_mem hb; omega
        · show σ.card = (CC.erase b).card
          rw [Finset.card_erase_of_mem hb]; omega
      have hdist : (⟨(σ, CC.erase a), hvtx_a⟩ : {p // IsScarfVtx ords c i₀ p}) ≠
                   ⟨(σ, CC.erase b), hvtx_b⟩ := by
        intro h
        have heq : CC.erase a = CC.erase b := congr_arg Prod.snd (congr_arg Subtype.val h)
        have hab' : a ∈ CC.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
        rw [← heq] at hab'
        exact Finset.notMem_erase a CC hab'
      have hg1 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx_a hadj_a
      have hg2 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx_b hadj_b
      exact degree_ge_two_of_two_adj G v _ _ hg1 hg2 hdist
    · -- admSet(a) empty, admSet(b) nonempty
      have hb_ne : (admSet ords σ hσne CC b).Nonempty := by
        rwa [Finset.nonempty_iff_ne_empty]
      let m_b := @Finset.max' T (ords b) (admSet ords σ hσne CC b) hb_ne
      have hm_b_mem : m_b ∈ admSet ords σ hσne CC b := @Finset.max'_mem T (ords b) _ hb_ne
      have hm_b_max : ∀ y ∈ admSet ords σ hσne CC b, ¬(ords b).lt m_b y := by
        intro y hy
        exact (@not_lt T (ords b)).mpr (@Finset.le_max' T (ords b) _ y hy)
      have hm_b_not_σ : m_b ∉ σ := fun h ↦
        m_not_mem_σ_aux ords σ CC hσne hDom a b ha hb hab hμeq b (Or.inr rfl) m_b hm_b_mem h
      have hDom_ins := isDominant_insert_of_admSet_max ords σ CC hσne hDom b hb _ hm_b_mem hm_b_max
      have hvtx_b := isScarfVtx_insert ords c i₀ σ CC m_b hm_b_not_σ hCne hDom_ins hdoor_card hnear
      have hadj_a : scarfAdjRel v.val (σ, CC.erase a) := by
        rw [hv]; show scarfAdjRel (σ, CC) (σ, CC.erase a)
        refine ⟨?_, Or.inr ⟨?_, Or.inr ⟨a, Finset.notMem_erase a CC, rfl,
          (Finset.insert_erase ha).symm⟩⟩⟩
        · intro h
          have : CC.card = (CC.erase a).card := congr_arg Finset.card (congr_arg Prod.snd h)
          have := Finset.card_erase_lt_of_mem ha; omega
        · show σ.card = (CC.erase a).card
          rw [Finset.card_erase_of_mem ha]; omega
      have hadj_b : scarfAdjRel v.val (insert m_b σ, CC) := by
        rw [hv]; show scarfAdjRel (σ, CC) (insert m_b σ, CC)
        refine ⟨?_, Or.inr ⟨?_, Or.inl ⟨m_b, Finset.mem_insert_self _ _, ?_, rfl⟩⟩⟩ <;> grind
      have hdist : (⟨(σ, CC.erase a), hvtx_a⟩ : {p // IsScarfVtx ords c i₀ p}) ≠
                   ⟨(insert m_b σ, CC), hvtx_b⟩ := by
        intro h
        have : (CC.erase a).card = CC.card :=
          congr_arg Finset.card (congr_arg Prod.snd (congr_arg Subtype.val h))
        have := Finset.card_erase_lt_of_mem ha; omega
      have hg1 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx_a hadj_a
      have hg2 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx_b hadj_b
      exact degree_ge_two_of_two_adj G v _ _ hg1 hg2 hdist
  · -- admSet(a) nonempty
    have ha_ne : (admSet ords σ hσne CC a).Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty]
    let m_a := @Finset.max' T (ords a) (admSet ords σ hσne CC a) ha_ne
    have hm_a_mem : m_a ∈ admSet ords σ hσne CC a := @Finset.max'_mem T (ords a) _ ha_ne
    have hm_a_max : ∀ y ∈ admSet ords σ hσne CC a, ¬(ords a).lt m_a y := by
      intro y hy
      exact (@not_lt T (ords a)).mpr (@Finset.le_max' T (ords a) _ y hy)
    have hm_a_not_σ : m_a ∉ σ :=
      fun h ↦ m_not_mem_σ_aux ords σ CC hσne hDom a b ha hb hab hμeq a (Or.inl rfl) m_a hm_a_mem h
    have hDom_ins_a := isDominant_insert_of_admSet_max ords σ CC hσne hDom a ha _ hm_a_mem hm_a_max
    have hvtx_a := isScarfVtx_insert ords c i₀ σ CC m_a hm_a_not_σ hCne hDom_ins_a hdoor_card hnear
    by_cases hb_empty : admSet ords σ hσne CC b = ∅
    · -- admSet(b) empty → room b is (σ, CC.erase b)
      have hDom_eb := isDominant_erase_of_admSet_empty ords σ CC hσne b hb_empty
      have hvtx_b := isScarfVtx_erase ords c i₀ σ CC hσne b hb hDom_eb hdoor_card hnear
      have hadj_a : scarfAdjRel v.val (insert m_a σ, CC) := by
        rw [hv]; show scarfAdjRel (σ, CC) (insert m_a σ, CC)
        refine ⟨?_, Or.inr ⟨?_, Or.inl ⟨m_a, Finset.mem_insert_self _ _, ?_, rfl⟩⟩⟩
        · intro h
          have h1 : σ = insert m_a σ := congr_arg Prod.fst h
          have : m_a ∈ σ := by rw [h1]; exact Finset.mem_insert_self _ _
          exact hm_a_not_σ this
        · show (insert m_a σ).card = CC.card
          rw [Finset.card_insert_of_notMem hm_a_not_σ]; omega
        · show σ = (insert m_a σ).erase m_a
          rw [Finset.erase_insert hm_a_not_σ]
      have hadj_b : scarfAdjRel v.val (σ, CC.erase b) := by
        rw [hv]; show scarfAdjRel (σ, CC) (σ, CC.erase b)
        refine ⟨?_, Or.inr ⟨?_, Or.inr ⟨b, Finset.notMem_erase b CC, rfl,
          (Finset.insert_erase hb).symm⟩⟩⟩
        · intro h
          have : CC.card = (CC.erase b).card := congr_arg Finset.card (congr_arg Prod.snd h)
          have := Finset.card_erase_lt_of_mem hb; omega
        · show σ.card = (CC.erase b).card
          rw [Finset.card_erase_of_mem hb]; omega
      have hdist : (⟨(insert m_a σ, CC), hvtx_a⟩ : {p // IsScarfVtx ords c i₀ p}) ≠
                   ⟨(σ, CC.erase b), hvtx_b⟩ := by
        intro h
        have : CC.card = (CC.erase b).card :=
          congr_arg Finset.card (congr_arg Prod.snd (congr_arg Subtype.val h))
        have := Finset.card_erase_lt_of_mem hb; omega
      have hg1 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx_a hadj_a
      have hg2 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx_b hadj_b
      exact degree_ge_two_of_two_adj G v _ _ hg1 hg2 hdist
    · -- Both nonempty → rooms are (insert m_a σ, CC) and (insert m_b σ, CC)
      have hb_ne : (admSet ords σ hσne CC b).Nonempty := by
        rwa [Finset.nonempty_iff_ne_empty]
      let m_b := @Finset.max' T (ords b) (admSet ords σ hσne CC b) hb_ne
      have hm_b_mem : m_b ∈ admSet ords σ hσne CC b := @Finset.max'_mem T (ords b) _ hb_ne
      have hm_b_max : ∀ y ∈ admSet ords σ hσne CC b, ¬(ords b).lt m_b y := by
        intro y hy
        exact (@not_lt T (ords b)).mpr (@Finset.le_max' T (ords b) _ y hy)
      have hm_b_not_σ : m_b ∉ σ := fun h ↦
        m_not_mem_σ_aux ords σ CC hσne hDom a b ha hb hab hμeq b (Or.inr rfl) m_b hm_b_mem h
      have hDom_ins_b := isDominant_insert_of_admSet_max ords σ _ hσne hDom b hb _ hm_b_mem hm_b_max
      have hvtx_b := isScarfVtx_insert ords c i₀ σ CC _ hm_b_not_σ hCne hDom_ins_b hdoor_card hnear
      -- m_a ≠ m_b because admSet(a) ∩ admSet(b) = ∅
      have hm_ne : m_a ≠ m_b := by
        intro heq
        have hdisj := admSet_disjoint ords σ CC hσne hDom a b hab
        exact Finset.disjoint_iff_ne.mp hdisj m_a hm_a_mem m_b hm_b_mem heq
      have hadj_a : scarfAdjRel v.val (insert m_a σ, CC) := by
        rw [hv]; show scarfAdjRel (σ, CC) (insert m_a σ, CC)
        refine ⟨?_, Or.inr ⟨?_, Or.inl ⟨m_a, Finset.mem_insert_self _ _, ?_, rfl⟩⟩⟩
        · intro h
          have h1 : σ = insert m_a σ := congr_arg Prod.fst h
          have : m_a ∈ σ := by rw [h1]; exact Finset.mem_insert_self _ _
          exact hm_a_not_σ this
        · show (insert m_a σ).card = CC.card
          rw [Finset.card_insert_of_notMem hm_a_not_σ]; omega
        · show σ = (insert m_a σ).erase m_a
          rw [Finset.erase_insert hm_a_not_σ]
      have hadj_b : scarfAdjRel v.val (insert m_b σ, CC) := by
        rw [hv]; show scarfAdjRel (σ, CC) (insert m_b σ, CC)
        refine ⟨?_, Or.inr ⟨?_, Or.inl ⟨m_b, Finset.mem_insert_self _ _, ?_, rfl⟩⟩⟩
        · intro h
          have h1 : σ = insert m_b σ := congr_arg Prod.fst h
          have : m_b ∈ σ := by rw [h1]; exact Finset.mem_insert_self _ _
          exact hm_b_not_σ this
        · show (insert m_b σ).card = CC.card
          rw [Finset.card_insert_of_notMem hm_b_not_σ]; omega
        · show σ = (insert m_b σ).erase m_b
          rw [Finset.erase_insert hm_b_not_σ]
      have hdist : (⟨(insert m_a σ, CC), hvtx_a⟩ : {p // IsScarfVtx ords c i₀ p}) ≠
                   ⟨(insert m_b σ, CC), hvtx_b⟩ := by
        intro h
        have h1 : insert m_a σ = insert m_b σ := congr_arg Prod.fst (congr_arg Subtype.val h)
        have hmem : m_a ∈ insert m_b σ := by rw [← h1]; exact Finset.mem_insert_self _ _
        simp only [Finset.mem_insert] at hmem
        cases hmem with
        | inl h => exact hm_ne h
        | inr h => exact hm_a_not_σ h
      have hg1 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx_a hadj_a
      have hg2 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx_b hadj_b
      exact degree_ge_two_of_two_adj G v _ _ hg1 hg2 hdist

lemma scarf_degree_one_is_colorful {n : ℕ} {T : Type} [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T) (c : T → Fin (n + 1))
    (i₀ : Fin (n + 1))
    (G : SimpleGraph { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    [DecidableRel G.Adj]
    (hG : ∀ v w, G.Adj v w ↔ scarfAdjRel v.val w.val)
    (v₀ : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (hv₀ : v₀.val = (∅, {i₀}))
    (v : { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p })
    (hne : v ≠ v₀) (hdeg : G.degree v = 1) :
    ∃ (σ₀ : Finset T) (C : Finset (Fin (n + 1))),
      σ₀.Nonempty ∧ C.Nonempty ∧ σ₀.card = C.card ∧
      C = σ₀.image c ∧ isDominant ords σ₀ C := by
  obtain ⟨hCne, hDom, hcases⟩ := v.property
  set σ := v.val.1 with hσ_def
  set CC := v.val.2 with hCC_def
  rcases hcases with ⟨hcard, hcol⟩ | ⟨hcard, hnear⟩ | ⟨hdoor_card, hnear⟩
  · -- Case A: colorful room → produce witnesses
    refine ⟨σ, CC, ?_, hCne, hcard, hcol, hDom⟩
    rw [Finset.nonempty_iff_ne_empty]
    intro h; simp only [h, Finset.image_empty] at hcol; exact hCne.ne_empty hcol
  · -- Case B: nearly colorful room → degree ≥ 2, contradiction
    exfalso
    by_cases hinj : (σ.image c).card = σ.card
    · -- Subcase B2: c is injective on σ
      have hIm_inj : Set.InjOn c ↑σ := Finset.card_image_iff.mp hinj
      have hne_sets : σ.image c ≠ CC := by
        intro heq
        have : i₀ ∈ CC \ σ.image c := hnear ▸ Finset.mem_singleton_self _
        rw [← heq] at this
        exact (Finset.mem_sdiff.mp this).2 (Finset.mem_sdiff.mp this).1
      have hcard_im : (σ.image c).card = CC.card := hinj.trans hcard
      have : (σ.image c \ CC).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        rw [Finset.sdiff_eq_empty_iff_subset] at h
        exact hne_sets (Finset.eq_of_subset_of_card_le h (le_of_eq hcard_im.symm))
      obtain ⟨j, hj⟩ := this
      rw [Finset.mem_sdiff] at hj
      obtain ⟨y, hy, hcy⟩ := Finset.mem_image.mp hj.1
      subst hcy
      have hvtx1 : IsScarfVtx ords c i₀ (σ.erase y, CC) := by
        refine ⟨hCne, isDominant_subset ords σ _ CC (Finset.erase_subset y σ) hDom, ?_⟩
        right; right
        constructor
        · show CC.card = (σ.erase y).card + 1
          have h1 := Finset.card_erase_of_mem hy
          have hpos : 0 < σ.card := Finset.card_pos.mpr ⟨y, hy⟩
          omega
        · show CC \ (σ.erase y).image c = {i₀}
          rw [image_erase_of_injOn' σ c y hy hIm_inj]
          exact sdiff_erase_of_not_mem CC (σ.image c) i₀ (c y) hj.2 hnear
      have hvtx2 : IsScarfVtx ords c i₀ (σ, insert (c y) CC) := by
        refine ⟨⟨c y, Finset.mem_insert_self _ _⟩,
               isDominant_supset ords σ CC _ (Finset.subset_insert _ _) hDom, ?_⟩
        right; right
        constructor
        · show (insert (c y) CC).card = σ.card + 1
          rw [Finset.card_insert_of_notMem hj.2]; omega
        · show (insert (c y) CC) \ σ.image c = {i₀}
          exact insert_sdiff_of_mem' CC (σ.image c) i₀ (c y) (Finset.mem_image_of_mem c hy) hnear
      have hadj1 : scarfAdjRel v.val (σ.erase y, CC) := by
        show scarfAdjRel (σ, CC) (σ.erase y, CC)
        refine ⟨?_, Or.inl ⟨hcard, Or.inl ⟨y, hy, rfl, rfl⟩⟩⟩
        intro h
        have h1 : σ.erase y = σ := (congr_arg Prod.fst h).symm
        exact absurd (h1 ▸ Finset.card_erase_lt_of_mem hy) (lt_irrefl _)
      have hadj2 : scarfAdjRel v.val (σ, insert (c y) CC) := by
        show scarfAdjRel (σ, CC) (σ, insert (c y) CC)
        refine ⟨?_, Or.inl ⟨hcard, Or.inr ⟨c y, hj.2, rfl, rfl⟩⟩⟩
        intro h
        have : CC = insert (c y) CC := congr_arg Prod.snd h
        rw [this] at hj; exact hj.2 (Finset.mem_insert_self _ _)
      have hdist : (⟨(σ.erase y, CC), hvtx1⟩ : {p // IsScarfVtx ords c i₀ p}) ≠
                   ⟨(σ, insert (c y) CC), hvtx2⟩ := by
        intro h
        have : CC = insert (c y) CC := congr_arg Prod.snd (congr_arg Subtype.val h)
        rw [this] at hj; exact hj.2 (Finset.mem_insert_self _ _)
      have hg1 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx1 hadj1
      have hg2 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx2 hadj2
      have := degree_ge_two_of_two_adj G v _ _ hg1 hg2 hdist
      omega
    · -- Subcase B1: c is NOT injective on σ
      push Not at hinj
      have hlt : (σ.image c).card < σ.card := lt_of_le_of_ne (Finset.card_image_le) hinj
      have : ∃ x ∈ σ, ∃ y ∈ σ, x ≠ y ∧ c x = c y := by
        by_contra hall
        push Not at hall
        have : Set.InjOn c ↑σ := by
          intro a ha b hb hab
          by_contra hne
          exact hall a ha b hb hne hab
        rw [Finset.card_image_of_injOn this] at hlt
        exact lt_irrefl _ hlt
      obtain ⟨x, hx, y, hy, hxy, hcxy⟩ := this
      have hvtx1 : IsScarfVtx ords c i₀ (σ.erase x, CC) := by
        refine ⟨hCne, isDominant_subset ords σ _ CC (Finset.erase_subset x σ) hDom, ?_⟩
        grind
      have hvtx2 : IsScarfVtx ords c i₀ (σ.erase y, CC) := by
        refine ⟨hCne, isDominant_subset ords σ _ CC (Finset.erase_subset y σ) hDom, ?_⟩
        grind
      have hadj1 : scarfAdjRel v.val (σ.erase x, CC) := by
        show scarfAdjRel (σ, CC) (σ.erase x, CC)
        refine ⟨?_, Or.inl ⟨hcard, Or.inl ⟨x, hx, rfl, rfl⟩⟩⟩
        intro h
        have h1 : σ.erase x = σ := (congr_arg Prod.fst h).symm
        have h2 := Finset.card_erase_lt_of_mem hx; rw [h1] at h2; exact lt_irrefl _ h2
      have hadj2 : scarfAdjRel v.val (σ.erase y, CC) := by
        show scarfAdjRel (σ, CC) (σ.erase y, CC)
        refine ⟨?_, Or.inl ⟨hcard, Or.inl ⟨y, hy, rfl, rfl⟩⟩⟩
        intro h
        have h1 : σ.erase y = σ := (congr_arg Prod.fst h).symm
        have h2 := Finset.card_erase_lt_of_mem hy; rw [h1] at h2; exact lt_irrefl _ h2
      have hdist : (⟨(σ.erase x, CC), hvtx1⟩ : {p // IsScarfVtx ords c i₀ p}) ≠
                   ⟨(σ.erase y, CC), hvtx2⟩ := by
        intro h
        have h1 : σ.erase x = σ.erase y := congr_arg Prod.fst (congr_arg Subtype.val h)
        have : x ∈ σ.erase y := Finset.mem_erase.mpr ⟨hxy, hx⟩
        rw [← h1] at this
        exact (Finset.notMem_erase x σ) this
      have hg1 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx1 hadj1
      have hg2 := mk_adj_of_scarfAdjRel ords c i₀ G hG v _ hvtx2 hadj2
      have := degree_ge_two_of_two_adj G v _ _ hg1 hg2 hdist
      omega
  · -- Case C: nearly colorful door
    exfalso
    by_cases hσne : σ.Nonempty
    · -- Internal door → degree ≥ 2
      have h2 := internal_door_degree_ge_two ords c i₀ G hG v σ CC rfl
        hCne hDom hdoor_card hnear hσne
      omega
    · -- Outside door → v = v₀
      rw [Finset.not_nonempty_iff_eq_empty] at hσne
      simp only [hσne, Finset.image_empty, Finset.sdiff_empty] at hnear
      apply hne; apply Subtype.ext; rw [hv₀]
      exact Prod.ext hσne hnear

lemma scarf_graph_construction (n : ℕ) (T : Type) [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (c : T → Fin (n + 1)) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (v₀ : V),
      (∀ v : V, G.degree v = 1 ∨ G.degree v = 2) ∧
      G.degree v₀ = 1 ∧
      (∀ v : V, v ≠ v₀ → G.degree v = 1 →
        ∃ (σ₀ : Finset T) (C : Finset (Fin (n + 1))),
          σ₀.Nonempty ∧ C.Nonempty ∧ σ₀.card = C.card ∧
          C = σ₀.image c ∧ isDominant ords σ₀ C) := by
  let i₀ : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let V := { p : Finset T × Finset (Fin (n + 1)) // IsScarfVtx ords c i₀ p }
  let G : SimpleGraph V := {
    Adj := fun v w ↦ scarfAdjRel v.val w.val
    symm := ⟨fun v w (h : scarfAdjRel v.val w.val) ↦ scarfAdjRel_symm v.val w.val h⟩
    loopless := ⟨fun v (h : scarfAdjRel v.val v.val) ↦ h.1 rfl⟩
  }
  have hDecAdj : DecidableRel G.Adj := by
    intro v w; exact Classical.dec _
  let v₀ : V := ⟨(∅, {i₀}), empty_singleton_isScarfVtx ords c i₀⟩
  have hG : ∀ v w : V, G.Adj v w ↔ scarfAdjRel v.val w.val := by
    intro v w; exact Iff.rfl
  exact ⟨V, inferInstance, inferInstance, G, hDecAdj, v₀,
    scarf_degree_one_or_two ords c i₀ G hG,
    scarf_v0_degree_one ords c i₀ G hG v₀ rfl,
    fun v hne hdeg ↦ scarf_degree_one_is_colorful ords c i₀ G hG v₀ rfl v hne hdeg⟩

lemma degree_two_other_adj {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v w : V) (hadj : G.Adj v w) (hdeg : G.degree v = 2) :
    ∃ w' : V, w' ≠ w ∧ G.Adj v w' ∧ ∀ u : V, G.Adj v u → u = w ∨ u = w' := by
  have h₁ : (G.neighborFinset v).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    simp [hdeg]
  have h₂ : ∃ (a b : V), a ≠ b ∧ G.neighborFinset v = {a, b} := by
    rw [Finset.card_eq_two] at h₁
    obtain ⟨a, b, hab, h⟩ := h₁
    refine' ⟨a, b, hab, _⟩
    simp_all [Finset.ext_iff]
  obtain ⟨a, b, hab, h₃⟩ := h₂
  have h₄ : w = a ∨ w = b := by
    have h₄₁ : w ∈ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]
      exact hadj
    have h₄₂ : w ∈ ({a, b} : Finset V) := by
      rw [h₃] at h₄₁
      exact h₄₁
    simp only [Finset.mem_insert, Finset.mem_singleton] at h₄₂
    tauto
  have h₅ : (if w = a then b else a) ≠ w := by
    split_ifs with h
    · intro h₅
      apply hab
      simp_all
    · intro h₅
      apply hab
      simp_all
  have h₆ : G.Adj v (if w = a then b else a) := by
    have h₆₁ : (if w = a then b else a) ∈ ({a, b} : Finset V) := by
      split_ifs with h <;> simp
    have h₆₂ : (if w = a then b else a) ∈ G.neighborFinset v := by
      rw [h₃]
      exact h₆₁
    rw [SimpleGraph.mem_neighborFinset] at h₆₂
    exact h₆₂
  have h₇ : ∀ (u : V), G.Adj v u → u = w ∨ u = (if w = a then b else a) := by
    intro u hu
    have h₇₁ : u ∈ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]
      exact hu
    grind
  grind

lemma path_next_not_in_support {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, G.degree v = 1 ∨ G.degree v = 2)
    (v₀ : V) (hv₀ : G.degree v₀ = 1)
    {v : V} (p : G.Walk v₀ v) (hp : p.IsPath) (hnil : ¬p.Nil)
    (hdeg2 : G.degree v = 2)
    (w : V) (hadj : G.Adj v w) (hne : w ≠ p.penultimate) :
    w ∉ p.support := by
  intro hmem
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
  obtain ⟨i, hi_eq, hi_le⟩ := hmem
  by_cases h0 : i = 0
  · -- Case C: i = 0, so w = v₀
    subst h0
    simp only [SimpleGraph.Walk.getVert_zero] at hi_eq
    subst hi_eq
    by_cases hlen1 : p.length = 1
    · -- p.length = 1: penultimate = v₀, contradicts hne
      have : p.penultimate = v₀ := by
        rw [SimpleGraph.Walk.penultimate.eq_1, hlen1]
        simp
      exact hne this.symm
    · -- p.length ≥ 2
      have hlen_pos : 0 < p.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hnil
      have hlen2 : 2 ≤ p.length := by omega
      have hsnd_adj : G.Adj v₀ p.snd := (p.toSubgraph_adj_snd hnil).adj_sub
      have hsnd_ne_v : p.snd ≠ v := by
        intro heq
        have h_snd_supp : p.snd = p.getVert 1 := by
          have := p.snd_eq_support_getElem_one hnil
          have h_idx : (1 : ℕ) < p.support.length := by
            rw [SimpleGraph.Walk.length_support]; omega
          rw [this, p.support_getElem_eq_getVert h_idx]
        have h_v_last : v = p.getVert p.length := (SimpleGraph.Walk.getVert_length p).symm
        have : (1 : ℕ) = p.length := hp.getVert_injOn
          (show (1 : ℕ) ∈ {j | j ≤ p.length} by simp; omega)
          (show p.length ∈ {j | j ≤ p.length} by simp)
          (by rw [← h_snd_supp, ← h_v_last, heq])
        omega
      have : G.degree v₀ ≥ 2 := by
        rw [SimpleGraph.degree]
        have hsub : {p.snd, v} ⊆ G.neighborFinset v₀ := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [SimpleGraph.mem_neighborFinset]
          rcases hx with rfl | rfl
          · exact hsnd_adj
          · exact hadj.symm
        calc (G.neighborFinset v₀).card ≥ ({p.snd, v} : Finset V).card :=
              Finset.card_le_card hsub
          _ = 2 := Finset.card_pair hsnd_ne_v
      omega
  · by_cases hlen : i = p.length
    · -- Case A: i = p.length, so w = v
      subst hlen
      rw [SimpleGraph.Walk.getVert_length] at hi_eq
      exact G.irrefl (hi_eq ▸ hadj)
    · -- Case B: 0 < i < p.length, w is internal
      have hi_lt : i < p.length := Nat.lt_of_le_of_ne hi_le hlen
      -- First handle special case: if i + 1 = p.length, then w = penultimate
      by_cases hip1 : i + 1 = p.length
      · have : w = p.penultimate := by
          rw [SimpleGraph.Walk.penultimate.eq_1]
          have : p.length - 1 = i := by omega
          rw [this, hi_eq]
        exact hne this
      · -- i + 1 < p.length
        have hip1_lt : i + 1 < p.length := by omega
        -- v ≠ getVert(i-1) and v ≠ getVert(i+1) by path injectivity
        have hv_ne_prev : v ≠ p.getVert (i - 1) := by
          intro heq
          have h1 : p.getVert p.length = p.getVert (i - 1) := by
            rw [SimpleGraph.Walk.getVert_length]; exact heq
          exact absurd (hp.getVert_injOn
            (show p.length ∈ {j | j ≤ p.length} by simp)
            (show i - 1 ∈ {j | j ≤ p.length} by simp; omega)
            h1) (by omega)
        have hv_ne_next : v ≠ p.getVert (i + 1) := by
          intro heq
          have h1 : p.getVert p.length = p.getVert (i + 1) := by
            rw [SimpleGraph.Walk.getVert_length]; exact heq
          exact absurd (hp.getVert_injOn
            (show p.length ∈ {j | j ≤ p.length} by simp)
            (show i + 1 ∈ {j | j ≤ p.length} by simp; omega)
            h1) (by omega)
        -- w's neighbors in p.toSubgraph are {getVert(i-1), getVert(i+1)}
        have hns := hp.neighborSet_toSubgraph_internal h0 hi_lt
        rw [hi_eq] at hns
        -- getVert(i-1) and getVert(i+1) are neighbors of w in G
        have hadj_prev : G.Adj w (p.getVert (i - 1)) := by
          have hmem : p.getVert (i - 1) ∈ p.toSubgraph.neighborSet w := by
            rw [hns]; exact Set.mem_insert _ _
          exact ((p.toSubgraph.mem_neighborSet w _).mp hmem).adj_sub
        have hadj_next : G.Adj w (p.getVert (i + 1)) := by
          have hmem : p.getVert (i + 1) ∈ p.toSubgraph.neighborSet w := by
            rw [hns]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
          exact ((p.toSubgraph.mem_neighborSet w _).mp hmem).adj_sub
        -- getVert(i-1) ≠ getVert(i+1)
        have hprev_ne_next : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
          intro heq
          exact absurd (hp.getVert_injOn
            (show i - 1 ∈ {j | j ≤ p.length} by simp; omega)
            (show i + 1 ∈ {j | j ≤ p.length} by simp; omega)
            heq) (by omega)
        -- w has ≥ 3 neighbors: getVert(i-1), getVert(i+1), v
        have : G.degree w ≥ 3 := by
          rw [SimpleGraph.degree]
          have hsub : {p.getVert (i - 1), p.getVert (i + 1), v} ⊆ G.neighborFinset w := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rw [SimpleGraph.mem_neighborFinset]
            rcases hx with rfl | rfl | rfl
            · exact hadj_prev
            · exact hadj_next
            · exact hadj.symm
          have hcard : ({p.getVert (i - 1), p.getVert (i + 1), v} : Finset V).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_pair hv_ne_next.symm]
            simp only [Finset.mem_insert, Finset.mem_singleton]
            push Not
            exact ⟨hprev_ne_next, hv_ne_prev.symm⟩
          linarith [Finset.card_le_card hsub]
        have := hdeg w
        omega

lemma degree_one_two_path_aux {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, G.degree v = 1 ∨ G.degree v = 2)
    (v₀ : V) (hv₀ : G.degree v₀ = 1)
    {v : V} (p : G.Walk v₀ v) (hp : p.IsPath) (hnil : ¬p.Nil)
    (hdeg2 : G.degree v = 2) :
    ∃ v₁ : V, v₁ ≠ v₀ ∧ G.degree v₁ = 1 ∧ G.Reachable v₀ v₁ := by
  have hadj_pen : G.Adj p.penultimate v := p.adj_penultimate hnil
  obtain ⟨w, hw_ne, hw_adj, _⟩ := degree_two_other_adj G v p.penultimate hadj_pen.symm hdeg2
  have hw_notin : w ∉ p.support :=
    path_next_not_in_support G hdeg v₀ hv₀ p hp hnil hdeg2 w hw_adj hw_ne
  let p' := p.concat hw_adj
  have hp' : p'.IsPath := hp.concat hw_notin hw_adj
  rcases hdeg w with hw1 | hw2
  · exact ⟨w, fun h ↦ hw_notin (h ▸ p.start_mem_support), hw1, p'.reachable⟩
  · have hnil' : ¬p'.Nil := by
      apply SimpleGraph.Walk.not_nil_of_ne; intro heq
      exact hw_notin (heq ▸ p.start_mem_support)
    exact degree_one_two_path_aux G hdeg v₀ hv₀ p' hp' hnil' hw2
termination_by Fintype.card V - p.length
decreasing_by
  simp only [SimpleGraph.Walk.length_concat]
  have := hp.length_lt (V := V)
  omega

lemma degree_one_two_path {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, G.degree v = 1 ∨ G.degree v = 2)
    (v₀ : V) (hv₀ : G.degree v₀ = 1) :
    ∃ v₁ : V, v₁ ≠ v₀ ∧ G.degree v₁ = 1 ∧ G.Reachable v₀ v₁ := by
  -- v₀ has degree 1, so it has a unique neighbor w₁
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hv₀
  obtain ⟨w₁, hw₁_adj, hw₁_unique⟩ := hv₀
  -- Consider whether w₁ has degree 1 or 2
  have hv₀_deg : G.degree v₀ = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    exact ⟨w₁, hw₁_adj, hw₁_unique⟩
  rcases hdeg w₁ with hdeg1 | hdeg2
  · -- w₁ has degree 1: done
    exact ⟨w₁, (G.ne_of_adj hw₁_adj).symm, hdeg1, hw₁_adj.reachable⟩
  · -- w₁ has degree 2: extend the path
    exact degree_one_two_path_aux G hdeg v₀ hv₀_deg
      hw₁_adj.toWalk
      (SimpleGraph.Walk.IsPath.of_adj hw₁_adj)
      (SimpleGraph.Walk.not_nil_of_ne (G.ne_of_adj hw₁_adj))
      hdeg2

/-- **Existence of a colorful room (core Scarf combinatorial argument).** -/
lemma scarf_colorful_room_exists (n : ℕ) (T : Type) [Fintype T] [Nonempty T]
    [DecidableEq T]
    (ords : Fin (n + 1) → LinearOrder T)
    (c : T → Fin (n + 1)) :
    ∃ (σ₀ : Finset T) (C : Finset (Fin (n + 1))),
      σ₀.Nonempty ∧ C.Nonempty ∧ σ₀.card = C.card ∧
      C = σ₀.image c ∧
      (∀ y : T, ∃ i ∈ C, ∀ x ∈ σ₀, ¬ (ords i).lt x y) := by
  obtain ⟨V, hFin, hDec, G, hDecAdj, v₀, hdeg, hv₀, hext⟩ :=
    scarf_graph_construction n T ords c
  obtain ⟨v₁, hne, hdeg1, _⟩ := @degree_one_two_path V hFin hDec G hDecAdj hdeg v₀ hv₀
  exact hext v₁ hne hdeg1

lemma scarf_abstract (n : ℕ) (T : Type) [Fintype T] [Nonempty T]
    (ords : Fin (n + 1) → LinearOrder T)
    (c : T → Fin (n + 1)) :
    ∃ (σ₀ : Finset T) (C : Finset (Fin (n + 1))),
      σ₀.Nonempty ∧ C.Nonempty ∧ σ₀.card = C.card ∧
      (∀ x ∈ σ₀, c x ∈ C) ∧
      (∀ i ∈ C, ∃ x ∈ σ₀, c x = i) ∧
      (∀ y : T, ∃ i ∈ C, ∀ x ∈ σ₀, ¬ (ords i).lt x y) := by
  obtain ⟨σ₀, C, hσ, hC, hcard, himg, hdom⟩ := scarf_colorful_room_exists n T ords c
  exact ⟨σ₀, C, hσ, hC, hcard, fun x hx ↦ himg ▸ Finset.mem_image_of_mem c hx,
    fun i hi ↦ by rw [himg] at hi; exact Finset.mem_image.mp hi, hdom⟩

def DiscreteSimplex (n l : ℕ) : Type :=
  { x : ↑(stdSimplex ℝ (Fin (n + 1))) //
    ∀ i : Fin (n + 1), ∃ k : ℕ, (x : Fin (n + 1) → ℝ) i = ↑k / ↑l }

lemma scarf_on_finite_type (n l : ℕ)
    [inst : Fintype (DiscreteSimplex n l)]
    [inh : Nonempty (DiscreteSimplex n l)]
    (ords : Fin (n + 1) → LinearOrder (DiscreteSimplex n l))
    (c : ↑(stdSimplex ℝ (Fin (n + 1))) → Fin (n + 1)) :
    ∃ (σ₀ : Finset (DiscreteSimplex n l)) (C : Finset (Fin (n + 1))),
      σ₀.Nonempty ∧ C.Nonempty ∧ σ₀.card = C.card ∧
      (∀ x ∈ σ₀, c x.1 ∈ C) ∧
      (∀ i ∈ C, ∃ x ∈ σ₀, c x.1 = i) ∧
      (∀ y : DiscreteSimplex n l, ∃ i ∈ C, ∀ x ∈ σ₀, ¬ (ords i).lt x y) :=
  scarf_abstract n (DiscreteSimplex n l) ords (fun x ↦ c x.1)

lemma discreteSimplex_numerator_bound {n l : ℕ} (hl : 0 < l)
    (x : ↑(stdSimplex ℝ (Fin (n + 1))))
    (hx : ∀ i : Fin (n + 1), ∃ k : ℕ, (x : Fin (n + 1) → ℝ) i = ↑k / ↑l)
    (i : Fin (n + 1)) :
    (hx i).choose < l + 1 := by
  have hle : (x : Fin (n + 1) → ℝ) i ≤ 1 := (mem_Icc_of_mem_stdSimplex x.2 i).2
  have hk := (hx i).choose_spec
  rw [hk] at hle
  have hl' : (0 : ℝ) < ↑l := Nat.cast_pos.mpr hl
  rw [div_le_one hl'] at hle
  exact Nat.lt_add_one_iff.mpr (Nat.cast_le.mp hle)

def discreteSimplex_encode (n l : ℕ) (hl : 0 < l) :
    DiscreteSimplex n l → (Fin (n + 1) → Fin (l + 1)) :=
  fun ⟨x, hx⟩ i ↦ ⟨(hx i).choose, discreteSimplex_numerator_bound hl x hx i⟩

lemma discreteSimplex_encode_injective (n l : ℕ) (hl : 0 < l) :
    Function.Injective (discreteSimplex_encode n l hl) := by
  intro ⟨⟨a, ha_mem⟩, ha_disc⟩ ⟨⟨b, hb_mem⟩, hb_disc⟩ h
  have key : ∀ i : Fin (n + 1), (ha_disc i).choose = (hb_disc i).choose := by
    intro i
    have := congr_fun h i
    simp only [discreteSimplex_encode, Fin.mk.injEq] at this
    exact this
  have coord_eq : ∀ i : Fin (n + 1), a i = b i := by
    intro i
    have ha_spec : a i = ↑(ha_disc i).choose / ↑l := (ha_disc i).choose_spec
    have hb_spec : b i = ↑(hb_disc i).choose / ↑l := (hb_disc i).choose_spec
    rw [ha_spec, hb_spec, key i]
  exact Subtype.ext (Subtype.ext (funext coord_eq))

lemma discreteSimplex_finite (n l : ℕ) (hl : 0 < l) :
    Finite (DiscreteSimplex n l) :=
  Finite.of_injective (discreteSimplex_encode n l hl) (discreteSimplex_encode_injective n l hl)

lemma discreteSimplex_nonempty (n l : ℕ) (hl : 0 < l) :
    Nonempty (DiscreteSimplex n l) := by
  refine ⟨⟨stdSimplex.vertex 0, fun i ↦ ?_⟩⟩
  simp only [stdSimplex.vertex_coe, Pi.single_apply]
  split
  · exact ⟨l, by simp [ne_of_gt (Nat.cast_pos.mpr hl), div_self]⟩
  · exact ⟨0, by simp⟩

/-- The coordinate rotation map: rotates coordinates so that coordinate i becomes first.
    rotate_i(x)(j) = x(i+j), where addition is in Fin(n+1).

    This is the key construction: we use this to pull back the lexicographic order,
    ensuring that coordinate i is compared first. -/
def rotateCoord (n l : ℕ) (i : Fin (n + 1)) (x : DiscreteSimplex n l) :
    Lex (Fin (n + 1) → ℝ) :=
  toLex (fun j ↦ (x.1 : Fin (n + 1) → ℝ) (i + j))

/-- The rotation map rotateCoord is injective for any fixed i.

    If rotateCoord i x = rotateCoord i y, then for all j, x(i+j) = y(i+j).
    Since j ↦ i+j is a bijection on Fin(n+1) (it is addition by a constant in
    a finite cyclic group), this means x(k) = y(k) for all k, hence x = y.

    Uses `Function.Injective : (α → β) → Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂`
    Uses `Subtype.val_injective : Function.Injective Subtype.val`
    The bijectivity of j ↦ i+j follows from Fin(n+1) being an additive group. -/
lemma rotateCoord_injective (n l : ℕ) (i : Fin (n + 1)) :
    Function.Injective (rotateCoord n l i : DiscreteSimplex n l → Lex (Fin (n + 1) → ℝ)) := by
  intro a b hab
  have hab' : (fun j ↦ (a.1 : Fin (n + 1) → ℝ) (i + j)) = fun j ↦ b.1 (i + j) := by
    exact toLex_inj.mp hab
  have heq : (a.1 : Fin (n + 1) → ℝ) = (b.1 : Fin (n + 1) → ℝ) := by
    ext k
    have := congr_fun hab' (k - i)
    simp only [add_sub_cancel] at this
    exact this
  exact Subtype.ext (Subtype.ext heq)

/-- If x_i < y_i, then toLex(rotate_i(x)) < toLex(rotate_i(y)) in the lexicographic order.

    Since rotate_i(x)(0) = x(i+0) = x(i) and similarly for y, we have
    rotate_i(x)(0) < rotate_i(y)(0). By the definition of lexicographic order,
    if the value at position 0 (the smallest index) is strictly smaller, then
    the whole function is strictly smaller in the lex order.

    Uses `Pi.Lex.eq_1 : Pi.Lex r s x y = ∃ i, (∀ (j : ι), r j i → x j = y j) ∧ s (x i) (y i)`
    applied with r = (<) and s = (<) on Fin(n+1), using i = 0 (since no j < 0 in Fin). -/
lemma rotateCoord_lt_of_coord_lt (n l : ℕ) (i : Fin (n + 1))
    (x y : DiscreteSimplex n l)
    (h : (x.1 : Fin (n + 1) → ℝ) i < (y.1 : Fin (n + 1) → ℝ) i) :
    rotateCoord n l i x < rotateCoord n l i y := by
  show Pi.Lex (· < ·) (fun {_} ↦ (· < ·))
    (fun j ↦ (x.1 : Fin (n + 1) → ℝ) (i + j))
    (fun j ↦ (y.1 : Fin (n + 1) → ℝ) (i + j))
  rw [Pi.Lex.eq_1]
  exact ⟨0, fun j hj ↦ absurd hj (Fin.not_lt.mpr (Fin.zero_le j)), by simpa using h⟩

lemma build_coord_compatible_orders (n l : ℕ) :
    ∃ ords : Fin (n + 1) → LinearOrder (DiscreteSimplex n l),
      ∀ i : Fin (n + 1), ∀ x y : DiscreteSimplex n l,
        (x.1 : Fin (n + 1) → ℝ) i < (y.1 : Fin (n + 1) → ℝ) i → (ords i).lt x y := by
  refine ⟨fun i ↦ LinearOrder.lift' (rotateCoord n l i) (rotateCoord_injective n l i), ?_⟩
  intro i x y hlt
  exact rotateCoord_lt_of_coord_lt n l i x y hlt

lemma discrete_simplex_scarf (n : ℕ) (l : ℕ) (hl : 0 < l)
    (c : ↑(stdSimplex ℝ (Fin (n + 1))) → Fin (n + 1)) :
    ∃ (σ₀ : Finset (DiscreteSimplex n l)) (C : Finset (Fin (n + 1)))
      (ords : Fin (n + 1) → LinearOrder (DiscreteSimplex n l)),
      σ₀.Nonempty ∧ C.Nonempty ∧ σ₀.card = C.card ∧
      (∀ x ∈ σ₀, c x.1 ∈ C) ∧
      (∀ i ∈ C, ∃ x ∈ σ₀, c x.1 = i) ∧
      -- Coordinate compatibility of the orders
      (∀ i : Fin (n + 1), ∀ x y : DiscreteSimplex n l,
        (x.1 : Fin (n + 1) → ℝ) i < (y.1 : Fin (n + 1) → ℝ) i → (ords i).lt x y) ∧
      -- Order-dominance
      (∀ y : DiscreteSimplex n l, ∃ i ∈ C, ∀ x ∈ σ₀, ¬ (ords i).lt x y) := by
  have : Finite (DiscreteSimplex n l) := discreteSimplex_finite n l hl
  have : Nonempty (DiscreteSimplex n l) := discreteSimplex_nonempty n l hl
  have : Fintype (DiscreteSimplex n l) := Fintype.ofFinite _
  obtain ⟨ords, hcompat⟩ := build_coord_compatible_orders n l
  obtain ⟨σ₀, C, hσne, hCne, hcard, hcol, hsurj, hdom⟩ :=
    scarf_on_finite_type n l ords c
  exact ⟨σ₀, C, ords, hσne, hCne, hcard, hcol, hsurj, hcompat, hdom⟩

lemma scarf_colorful_room (n : ℕ) (l : ℕ) (hl : 0 < l)
    (c : ↑(stdSimplex ℝ (Fin (n + 1))) → Fin (n + 1)) :
    ∃ (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1)))) (C : Finset (Fin (n + 1))),
      σ.Nonempty ∧ C.Nonempty ∧
      σ.card = C.card ∧
      (∀ x ∈ σ, c x ∈ C) ∧
      (∀ i ∈ C, ∃ x ∈ σ, c x = i) ∧
      (∀ x ∈ σ, ∀ i : Fin (n + 1), ∃ k : ℕ, (x : Fin (n + 1) → ℝ) i = ↑k / ↑l) ∧
      (¬ ∃ y : ↑(stdSimplex ℝ (Fin (n + 1))),
        (∀ i : Fin (n + 1), ∃ k : ℕ, (y : Fin (n + 1) → ℝ) i = ↑k / ↑l) ∧
        ∀ i ∈ C, ∃ x ∈ σ, (x : Fin (n + 1) → ℝ) i < (y : Fin (n + 1) → ℝ) i) := by
  -- Get σ₀ ⊆ DiscreteSimplex and C with order-dominance
  obtain ⟨σ₀, C, ords, hne, hCne, hcard, hcol, hsurj, hcompat, hdom⟩ :=
    discrete_simplex_scarf n l hl c
  -- Lift σ₀ to stdSimplex via the subtype embedding
  let emb : DiscreteSimplex n l → ↑(stdSimplex ℝ (Fin (n + 1))) := Subtype.val
  have emb_inj : Function.Injective emb := Subtype.val_injective
  let σ : Finset ↑(stdSimplex ℝ (Fin (n + 1))) := σ₀.map ⟨emb, emb_inj⟩
  refine ⟨σ, C, ?_, hCne, ?_, ?_, ?_, ?_, ?_⟩
  · -- σ.Nonempty
    exact Finset.Nonempty.map hne
  · -- σ.card = C.card
    rw [Finset.card_map]; exact hcard
  · -- ∀ x ∈ σ, c x ∈ C
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hcol a ha
  · -- ∀ i ∈ C, ∃ x ∈ σ, c x = i
    intro i hi
    obtain ⟨x, hx, hcx⟩ := hsurj i hi
    exact ⟨emb x, Finset.mem_map.mpr ⟨x, hx, rfl⟩, hcx⟩
  · -- ∀ x ∈ σ, ∀ i, ∃ k, x_i = k/l (coordinate-divisibility from DiscreteSimplex)
    intro x hx i
    rw [Finset.mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact a.2 i
  · -- Translate order-dominance to coordinate-dominance
    -- Contrapositive: if ∃ y ∈ T_l, ∀ i ∈ C, ∃ x ∈ σ, x_i < y_i,
    -- then by coord-compat, ∀ i ∈ C, ∃ x ∈ σ₀, x <_i y₀,
    -- contradicting order-dominance (∃ i ∈ C, ∀ x ∈ σ₀, ¬(x <_i y₀))
    intro ⟨y, hy_disc, hy_dom⟩
    let y₀ : DiscreteSimplex n l := ⟨y, hy_disc⟩
    obtain ⟨i, hi, hblock⟩ := hdom y₀
    obtain ⟨x, hx, hlt⟩ := hy_dom i hi
    rw [Finset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hblock a ha (hcompat i a y₀ hlt)

/-- **Helper: the remaining mass 1 - ∑_{k∈C} v_k is a natural number divided by l.**

    If each v_k for k ∈ C is of the form m_k/l for some ℕ m_k, and ∑_{k∈C} v_k ≤ 1,
    then 1 - ∑_{k∈C} v_k = r/l for some r : ℕ.

    No direct Mathlib equivalent. Uses `Finset.sum_div` and `Nat.cast_sum`. -/
lemma remaining_mass_discrete (n : ℕ) (l : ℕ) (hl : 0 < l)
    (C : Finset (Fin (n + 1)))
    (v : Fin (n + 1) → ℝ)
    (hv_discrete : ∀ k ∈ C, ∃ m : ℕ, v k = ↑m / ↑l)
    (hv_sum : C.sum v ≤ 1) :
    ∃ r : ℕ, 1 - C.sum v = ↑r / ↑l := by
  -- Extend to a total function by defaulting to 0 outside C
  set g : Fin (n + 1) → ℕ := fun k ↦ if hk : k ∈ C then (hv_discrete k hk).choose else 0
  have hg : ∀ k ∈ C, v k = ↑(g k) / ↑l := by
    intro k hk; simp only [g, hk, dite_true]; exact (hv_discrete k hk).choose_spec
  -- ∑v = ∑(g k)/l = (∑ g k)/l
  have hl_pos : (0 : ℝ) < ↑l := Nat.cast_pos.mpr hl
  have hsum_eq : C.sum v = (↑(C.sum g) : ℝ) / ↑l := by
    rw [Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_congr rfl (fun k hk ↦ hg k hk)
  -- 1 = l/l
  have h1_eq : (1 : ℝ) = ↑l / ↑l := by field_simp
  -- We need ∑g k ≤ l (as ℕ)
  have hle : C.sum g ≤ l := by
    rw [← Nat.cast_le (α := ℝ)]
    have : (↑(C.sum g) : ℝ) / ↑l ≤ 1 := by rw [← hsum_eq]; exact hv_sum
    calc (↑(C.sum g) : ℝ) = ↑(C.sum g) / ↑l * ↑l := by field_simp
      _ ≤ 1 * ↑l := by apply mul_le_mul_of_nonneg_right this (le_of_lt hl_pos)
      _ = ↑l := one_mul _
  exact ⟨l - C.sum g, by rw [hsum_eq, h1_eq, Nat.cast_sub hle]; ring⟩

/-- **Helper: construct a simplex point from values on C plus remaining mass on coordinate 0.**

    Given nonneg values v on C with C.sum v ≤ 1, define M by setting M_k = v_k for k ∈ C,
    M_0 += (1 - C.sum v) (remaining mass), and M_i = 0 for i ∉ C ∪ {0}.
    Then M ∈ stdSimplex ℝ (Fin (n+1)).

    No direct Mathlib equivalent. This constructs the concrete simplex point. -/
lemma construct_simplex_point (n : ℕ)
    (C : Finset (Fin (n + 1)))
    (v : Fin (n + 1) → ℝ)
    (hv_nonneg : ∀ k ∈ C, 0 ≤ v k)
    (hv_sum : C.sum v ≤ 1) :
    let M : Fin (n + 1) → ℝ := fun i ↦
      (if i ∈ C then v i else 0) + (if i = (0 : Fin (n + 1)) then 1 - C.sum v else 0)
    M ∈ stdSimplex ℝ (Fin (n + 1)) := by
  show (fun i ↦ (if i ∈ C then v i else 0) + (if i = 0 then 1 - C.sum v else 0)) ∈ stdSimplex ℝ _
  refine ⟨fun i ↦ ?_, ?_⟩
  · -- Nonneg
    grind
  · -- Sum = 1
    rw [Finset.sum_add_distrib]
    have h1 : ∑ i : Fin (n + 1), (if i ∈ C then v i else 0) = C.sum v := by
      rw [← Finset.sum_filter]
      congr 1
      ext i; simp
    have h2 : ∑ i : Fin (n + 1), (if i = 0 then 1 - C.sum v else 0) = 1 - C.sum v := by
      rw [Finset.sum_ite_eq']
      simp [Finset.mem_univ]
    linarith

/-- **Construct a point in the discrete simplex dominating given values on C.**

    Given values `v : Fin (n+1) → ℝ` with each `v k` a nonneg multiple of `1/l` for `k ∈ C`,
    and `∑_{k∈C} v k ≤ 1`, construct a point `M` in `stdSimplex ℝ (Fin (n+1))` such that:
    - `M k ≥ v k` for all `k ∈ C`
    - Each `M i` is of the form `↑k / ↑l` for some `k : ℕ`

    **Construction:** For `k ∈ C`, set `M k = v k`. For `k ∉ C`, set `M k = 0`, except
    for one chosen coordinate `0` where we put the remaining mass `1 - ∑_{k∈C} v k`.
    Since all values are multiples of `1/l` and the total is ≤ 1, the remaining mass
    is also a nonneg multiple of `1/l`.

    Uses `remaining_mass_discrete` and `construct_simplex_point` as sub-helpers.
    No direct Mathlib equivalent. -/
lemma construct_dominating_point (n : ℕ) (l : ℕ) (hl : 0 < l)
    (C : Finset (Fin (n + 1)))
    (v : Fin (n + 1) → ℝ)
    (hv_nonneg : ∀ k ∈ C, 0 ≤ v k)
    (hv_discrete : ∀ k ∈ C, ∃ m : ℕ, v k = ↑m / ↑l)
    (hv_sum : C.sum v ≤ 1) :
    ∃ y : ↑(stdSimplex ℝ (Fin (n + 1))),
      (∀ i : Fin (n + 1), ∃ k : ℕ, (y : Fin (n + 1) → ℝ) i = ↑k / ↑l) ∧
      ∀ k ∈ C, (y : Fin (n + 1) → ℝ) k ≥ v k := by
  -- Define M
  set M : Fin (n + 1) → ℝ := fun i ↦
    (if i ∈ C then v i else 0) + (if i = (0 : Fin (n + 1)) then 1 - C.sum v else 0) with hM_def
  -- M is in the simplex
  have hM_mem : M ∈ stdSimplex ℝ (Fin (n + 1)) := construct_simplex_point n C v hv_nonneg hv_sum
  -- Package M as a subtype
  refine ⟨⟨M, hM_mem⟩, ?_, ?_⟩
  · -- Discreteness: each M i = k / l for some k : ℕ
    intro i
    show ∃ k : ℕ, M i = ↑k / ↑l
    simp only [hM_def]
    by_cases hiC : i ∈ C <;> by_cases hi0 : i = (0 : Fin (n + 1))
    · -- i ∈ C, i = 0
      subst hi0; simp only [hiC, ite_true]
      obtain ⟨m_i, hm_i⟩ := hv_discrete _ hiC
      obtain ⟨r, hr⟩ := remaining_mass_discrete n l hl C v hv_discrete hv_sum
      exact ⟨m_i + r, by rw [hm_i, hr]; push_cast; ring⟩
    · -- i ∈ C, i ≠ 0
      simp only [hiC, ite_true, hi0, ite_false, add_zero]
      exact hv_discrete i hiC
    · -- i ∉ C, i = 0
      subst hi0; simp only [hiC, ite_false, ite_true, zero_add]
      exact remaining_mass_discrete n l hl C v hv_discrete hv_sum
    · -- i ∉ C, i ≠ 0
      simp only [hiC, ite_false, hi0, add_zero]
      exact ⟨0, by simp⟩
  · -- Domination: M k ≥ v k for k ∈ C
    intro k hk
    show v k ≤ M k
    simp only [hM_def, hk, ite_true]
    by_cases hk0 : k = (0 : Fin (n + 1))
    · simp [hk0]; linarith [hv_sum]
    · simp [hk0]

/-- **Infimum of discrete values is attained and is discrete.**

    For a nonempty finite set `σ` of points in the standard simplex where each coordinate
    is a multiple of `1/l`, the infimum `σ.inf' hσ (fun z ↦ z i)` is attained at some
    element of `σ` and is itself a multiple of `1/l`.

    **Proof:** By `Finset.exists_mem_eq_inf'` (which requires `LinearOrder`, but ℝ has one),
    there exists `x ∈ σ` with `σ.inf' hσ f = f x`. Since `x ∈ σ`, by `hdiscrete` its
    `i`-th coordinate is a multiple of `1/l`.

    Uses: `Finset.exists_mem_eq_inf' : ∀ {α : Type} {ι : Type} [LinearOrder α]
      {s : Finset ι} (H : s.Nonempty) (f : ι → α), ∃ i ∈ s, s.inf' H f = f i` -/
lemma inf'_discrete (n : ℕ) (l : ℕ)
    (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1))))
    (hσ : σ.Nonempty)
    (hdiscrete : ∀ x ∈ σ, ∀ i : Fin (n + 1), ∃ k : ℕ, (x : Fin (n + 1) → ℝ) i = ↑k / ↑l)
    (i : Fin (n + 1)) :
    ∃ k : ℕ, σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) i) = ↑k / ↑l := by
  obtain ⟨x, hx, hmin⟩ := Finset.exists_mem_eq_inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) i)
  rw [hmin]
  exact hdiscrete x hx i

/-- **Infimum is attained: there exists x ∈ σ achieving the minimum coordinate.**

    For each coordinate `i`, there exists `x ∈ σ` such that
    `(x : Fin (n+1) → ℝ) i = σ.inf' hσ (fun z ↦ z i)`.

    **Proof:** Direct from `Finset.exists_mem_eq_inf'` applied to the linear order on ℝ.

    Uses: `Finset.exists_mem_eq_inf' : ∀ {α : Type} {ι : Type} [LinearOrder α]
      {s : Finset ι} (H : s.Nonempty) (f : ι → α), ∃ i ∈ s, s.inf' H f = f i` -/
lemma inf'_attained (n : ℕ)
    (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1))))
    (hσ : σ.Nonempty)
    (i : Fin (n + 1)) :
    ∃ x ∈ σ, σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) i) = (x : Fin (n + 1) → ℝ) i := by
  obtain ⟨x, hx, hmin⟩ := Finset.exists_mem_eq_inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) i)
  exact ⟨x, hx, hmin⟩

/-- **Sum rearrangement: from ¬(a < b) to ∑(m_k + 1/l) ≤ 1.**

    If `¬ (1 - ∑_{k∈C} m_k < C.card / l)` (equivalently `C.card / l ≤ 1 - ∑ m_k`),
    then `C.sum (fun k ↦ m k + 1/l) ≤ 1`.

    **Proof:** From `C.card / l ≤ 1 - ∑ m_k`, we get `∑ m_k + C.card / l ≤ 1`.
    Rewriting `C.card / l` as `∑_{k∈C} (1/l)` and combining with `∑ m_k` gives the result.

    Uses: `Finset.sum_add_distrib` and basic real arithmetic. -/
lemma sum_shifted_le_one (n : ℕ) (l : ℕ)
    (C : Finset (Fin (n + 1)))
    (m : Fin (n + 1) → ℝ)
    (h : ¬ (1 - C.sum m < (↑C.card : ℝ) / (↑l : ℝ))) :
    C.sum (fun k ↦ m k + 1 / (↑l : ℝ)) ≤ 1 := by
  rw [not_lt] at h
  have : C.sum (fun k ↦ m k + 1 / (↑l : ℝ)) = C.sum m + C.sum (fun _ ↦ 1 / (↑l : ℝ)) := by
    rw [← Finset.sum_add_distrib]
  rw [this]
  have : C.sum (fun _ : Fin (n + 1) ↦ 1 / (↑l : ℝ)) = ↑C.card / ↑l := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  linarith

lemma key_ineq (n : ℕ) (l : ℕ) (hl : 0 < l)
    (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1)))) (C : Finset (Fin (n + 1))) (hσ : σ.Nonempty)
    (hdiscrete : ∀ x ∈ σ, ∀ i : Fin (n + 1), ∃ k : ℕ, (x : Fin (n + 1) → ℝ) i = ↑k / ↑l)
    (hdom : ¬ ∃ y : ↑(stdSimplex ℝ (Fin (n + 1))),
        (∀ i : Fin (n + 1), ∃ k : ℕ, (y : Fin (n + 1) → ℝ) i = ↑k / ↑l) ∧
        ∀ i ∈ C, ∃ x ∈ σ, (x : Fin (n + 1) → ℝ) i < (y : Fin (n + 1) → ℝ) i) :
    1 - C.sum (fun k ↦ σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) k)) <
      (↑C.card : ℝ) / (↑l : ℝ) := by
  -- Proof by contradiction
  by_contra h_not_lt
  -- Let m be the function k ↦ σ.inf' hσ (fun z ↦ z k)
  set m : Fin (n + 1) → ℝ := fun k ↦ σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) k) with hm_def
  -- From h_not_lt, deduce ∑_{k∈C}(m k + 1/l) ≤ 1
  have hsum : C.sum (fun k ↦ m k + 1 / (↑l : ℝ)) ≤ 1 :=
    sum_shifted_le_one n l C m h_not_lt
  -- Each m k for k ∈ C is discrete (multiple of 1/l)
  have hm_discrete : ∀ k ∈ C, ∃ j : ℕ, m k = ↑j / ↑l := fun k _ ↦
    inf'_discrete n l σ hσ hdiscrete k
  -- Each m k + 1/l is nonneg and discrete
  have hv_nonneg : ∀ k ∈ C, 0 ≤ m k + 1 / (↑l : ℝ) := by
    intro k _
    have : 0 ≤ m k := by
      simp only [hm_def]
      obtain ⟨x, _, hmin⟩ := inf'_attained n σ hσ k
      rw [hmin]
      exact (x.2.1 k)
    linarith [show (0 : ℝ) < 1 / ↑l from by positivity]
  have hv_discrete : ∀ k ∈ C, ∃ j : ℕ, m k + 1 / (↑l : ℝ) = ↑j / ↑l := by
    intro k hk
    obtain ⟨j, hj⟩ := hm_discrete k hk
    exact ⟨j + 1, by rw [hj]; push_cast; ring⟩
  -- Construct the dominating point M
  obtain ⟨M, hM_discrete, hM_ge⟩ := construct_dominating_point n l hl C
    (fun k ↦ m k + 1 / (↑l : ℝ)) hv_nonneg hv_discrete hsum
  -- Apply hdom to get contradiction
  apply hdom
  refine ⟨M, hM_discrete, ?_⟩
  intro i hi
  -- Find the minimizer for coordinate i
  obtain ⟨x, hx, hmin⟩ := inf'_attained n σ hσ i
  refine ⟨x, hx, ?_⟩
  rw [hmin.symm]
  calc (m i : ℝ) < m i + 1 / (↑l : ℝ) := by linarith [show (0 : ℝ) < 1 / ↑l from by positivity]
    _ ≤ (M : Fin (n + 1) → ℝ) i := hM_ge i hi

lemma deviation_nonneg (n : ℕ)
    (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1))))
    (hσ : σ.Nonempty)
    (x : ↑(stdSimplex ℝ (Fin (n + 1)))) (hx : x ∈ σ) (k : Fin (n + 1)) :
    0 ≤ (x : Fin (n + 1) → ℝ) k - σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) k) :=
  sub_nonneg.mpr (Finset.inf'_le _ hx)

lemma sum_subset_le_one (n : ℕ) (C : Finset (Fin (n + 1)))
    (x : ↑(stdSimplex ℝ (Fin (n + 1)))) :
    C.sum (fun k ↦ (x : Fin (n + 1) → ℝ) k) ≤ 1 := by
  have h1 := Finset.sum_le_univ_sum_of_nonneg (f := fun k ↦ (x : Fin (n + 1) → ℝ) k)
    (s := C) (fun k ↦ (mem_Icc_of_mem_stdSimplex x.2 k).1)
  rw [stdSimplex.sum_eq_one] at h1
  exact h1

lemma deviation_in_C (n : ℕ)
    (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1)))) (C : Finset (Fin (n + 1)))
    (hσ : σ.Nonempty)
    (x : ↑(stdSimplex ℝ (Fin (n + 1)))) (hx : x ∈ σ) (i : Fin (n + 1)) (hi : i ∈ C) :
    (x : Fin (n + 1) → ℝ) i - σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) i) ≤
      1 - C.sum (fun k ↦ σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) k)) := by
  calc (x : Fin (n + 1) → ℝ) i - σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) i)
      ≤ C.sum (fun k ↦ (x : Fin (n + 1) → ℝ) k - σ.inf' hσ (fun z ↦ z k)) := by
        exact Finset.single_le_sum (fun k hk ↦ deviation_nonneg n σ hσ x hx k) hi
    _ = C.sum (fun k ↦ (x : Fin (n + 1) → ℝ) k) -
        C.sum (fun k ↦ σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) k)) := by
        exact Finset.sum_sub_distrib _ _
    _ ≤ 1 - C.sum (fun k ↦ σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) k)) := by
        linarith [sum_subset_le_one n C x]

lemma xi_le_one_sub_sum_C (n : ℕ)
    (x : ↑(stdSimplex ℝ (Fin (n + 1)))) (C : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∉ C) :
    (x : Fin (n + 1) → ℝ) i ≤ 1 - C.sum (fun k ↦ (x : Fin (n + 1) → ℝ) k) := by
  have hnn : ∀ j ∈ Cᶜ, 0 ≤ (x : Fin (n + 1) → ℝ) j :=
    fun j _ ↦ stdSimplex.zero_le x j
  have hmem : i ∈ Cᶜ := Finset.mem_compl.mpr hi
  have h1 : (x : Fin (n + 1) → ℝ) i ≤ ∑ k ∈ Cᶜ, (x : Fin (n + 1) → ℝ) k :=
    Finset.single_le_sum hnn hmem
  have h2 : ∑ k ∈ C, (x : Fin (n + 1) → ℝ) k + ∑ k ∈ Cᶜ, (x : Fin (n + 1) → ℝ) k =
    ∑ k, (x : Fin (n + 1) → ℝ) k := Finset.sum_add_sum_compl C _
  have h3 : ∑ k, (x : Fin (n + 1) → ℝ) k = 1 := stdSimplex.sum_eq_one x
  linarith

lemma sum_inf_le_sum_x (n : ℕ)
    (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1)))) (C : Finset (Fin (n + 1)))
    (hσ : σ.Nonempty)
    (x : ↑(stdSimplex ℝ (Fin (n + 1)))) (hx : x ∈ σ) :
    C.sum (fun k ↦ σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) k)) ≤
      C.sum (fun k ↦ (x : Fin (n + 1) → ℝ) k) := by
  apply Finset.sum_le_sum
  intro k _
  exact Finset.inf'_le (fun (z : ↑(stdSimplex ℝ (Fin (n + 1)))) ↦ (z : Fin (n + 1) → ℝ) k) hx

lemma deviation_not_in_C (n : ℕ)
    (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1)))) (C : Finset (Fin (n + 1)))
    (hσ : σ.Nonempty)
    (x : ↑(stdSimplex ℝ (Fin (n + 1)))) (hx : x ∈ σ) (i : Fin (n + 1)) (hi : i ∉ C) :
    (x : Fin (n + 1) → ℝ) i ≤
      1 - C.sum (fun k ↦ σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) k)) := by
  calc (x : Fin (n + 1) → ℝ) i
      ≤ 1 - C.sum (fun k ↦ (x : Fin (n + 1) → ℝ) k) := xi_le_one_sub_sum_C n x C i hi
    _ ≤ 1 - C.sum (fun k ↦ σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) k)) := by
        linarith [sum_inf_le_sum_x n σ C hσ x hx]

lemma coord_deviation_bound (n : ℕ) (l : ℕ) (hl : 0 < l)
    (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1)))) (C : Finset (Fin (n + 1))) (hσ : σ.Nonempty)
    (hdiscrete : ∀ x ∈ σ, ∀ i : Fin (n + 1), ∃ k : ℕ, (x : Fin (n + 1) → ℝ) i = ↑k / ↑l)
    (hdom : ¬ ∃ y : ↑(stdSimplex ℝ (Fin (n + 1))),
        (∀ i : Fin (n + 1), ∃ k : ℕ, (y : Fin (n + 1) → ℝ) i = ↑k / ↑l) ∧
        ∀ i ∈ C, ∃ x ∈ σ, (x : Fin (n + 1) → ℝ) i < (y : Fin (n + 1) → ℝ) i) :
    ∀ x ∈ σ, ∀ i : Fin (n + 1),
      (x : Fin (n + 1) → ℝ) i -
        (if i ∈ C then σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) i) else 0) <
        (↑(n + 1) : ℝ) / (↑l : ℝ) := by
  have hkey := key_ineq n l hl σ C hσ hdiscrete hdom
  have hcard : (↑C.card : ℝ) ≤ (↑(n + 1) : ℝ) := by
    have h1 : C.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ C)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    exact Nat.cast_le.mpr h1
  have hl_pos : (0 : ℝ) < ↑l := Nat.cast_pos.mpr hl
  intro x hx i
  by_cases hi : i ∈ C
  · simp only [hi, ite_true]
    calc (x : Fin (n + 1) → ℝ) i - σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) i)
        ≤ 1 - C.sum (fun k ↦ σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) k)) :=
          deviation_in_C n σ C hσ x hx i hi
      _ < (↑C.card : ℝ) / (↑l : ℝ) := hkey
      _ ≤ (↑(n + 1) : ℝ) / (↑l : ℝ) := div_le_div_of_nonneg_right hcard hl_pos.le
  · simp only [hi, ite_false, sub_zero]
    calc (x : Fin (n + 1) → ℝ) i
        ≤ 1 - C.sum (fun k ↦ σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) k)) :=
          deviation_not_in_C n σ C hσ x hx i hi
      _ < (↑C.card : ℝ) / (↑l : ℝ) := hkey
      _ ≤ (↑(n + 1) : ℝ) / (↑l : ℝ) := div_le_div_of_nonneg_right hcard hl_pos.le

lemma scarf_bounds (n : ℕ) (l : ℕ) (hl : 0 < l)
    (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1)))) (C : Finset (Fin (n + 1))) (hσ : σ.Nonempty)
    (hdiscrete : ∀ x ∈ σ, ∀ i : Fin (n + 1), ∃ k : ℕ, (x : Fin (n + 1) → ℝ) i = ↑k / ↑l)
    (hdom : ¬ ∃ y : ↑(stdSimplex ℝ (Fin (n + 1))),
        (∀ i : Fin (n + 1), ∃ k : ℕ, (y : Fin (n + 1) → ℝ) i = ↑k / ↑l) ∧
        ∀ i ∈ C, ∃ x ∈ σ, (x : Fin (n + 1) → ℝ) i < (y : Fin (n + 1) → ℝ) i) :
    (∀ x ∈ σ, ∀ y ∈ σ, ∀ i,
      |(x : Fin (n + 1) → ℝ) i - (y : Fin (n + 1) → ℝ) i| <
        2 * (↑(n + 1) : ℝ) / (↑l : ℝ)) ∧
    (∀ x ∈ σ, ∀ i, i ∉ C →
      (x : Fin (n + 1) → ℝ) i < (↑(n + 1) : ℝ) / (↑l : ℝ)) := by
  have hdev := coord_deviation_bound n l hl σ C hσ hdiscrete hdom
  refine ⟨fun x hx y hy i ↦ ?_, fun x hx i hi ↦ ?_⟩
  · -- Diameter bound: |x_i - y_i| < 2*(n+1)/l
    have hx_dev := hdev x hx i
    have hy_dev := hdev y hy i
    set mi := if i ∈ C then σ.inf' hσ (fun z ↦ (z : Fin (n + 1) → ℝ) i) else 0 with hmi_def
    have hx_ge : mi ≤ (x : Fin (n + 1) → ℝ) i := by
      simp only [hmi_def]; split
      · exact Finset.inf'_le _ hx
      · exact x.2.1 i
    have hy_ge : mi ≤ (y : Fin (n + 1) → ℝ) i := by
      simp only [hmi_def]; split
      · exact Finset.inf'_le _ hy
      · exact y.2.1 i
    have hbound : (↑(n + 1) : ℝ) / ↑l + ↑(n + 1) / ↑l = 2 * ↑(n + 1) / ↑l := by ring
    rw [abs_sub_lt_iff]
    exact ⟨by linarith, by linarith⟩
  · -- Small outside C
    have hx_dev := hdev x hx i
    simpa [hi, ↓reduceIte, sub_zero] using hx_dev

lemma exists_colorful_room_with_bounds (n : ℕ) (l : ℕ) (hl : 0 < l)
    (c : ↑(stdSimplex ℝ (Fin (n + 1))) → Fin (n + 1)) :
    ∃ (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1)))) (C : Finset (Fin (n + 1))),
      σ.Nonempty ∧ C.Nonempty ∧
      σ.card = C.card ∧
      (∀ x ∈ σ, c x ∈ C) ∧
      (∀ i ∈ C, ∃ x ∈ σ, c x = i) ∧
      (∀ x ∈ σ, ∀ y ∈ σ, ∀ i,
        |(x : Fin (n + 1) → ℝ) i - (y : Fin (n + 1) → ℝ) i| <
          2 * (↑(n + 1) : ℝ) / (↑l : ℝ)) ∧
      (∀ x ∈ σ, ∀ i, i ∉ C →
        (x : Fin (n + 1) → ℝ) i < (↑(n + 1) : ℝ) / (↑l : ℝ)) := by
  obtain ⟨σ, C, hσ, hC, hcard, hcov, hsurj, hdiscrete, hdom⟩ :=
    scarf_colorful_room n l hl c
  obtain ⟨hbound, hsmall⟩ := scarf_bounds n l hl σ C hσ hdiscrete hdom
  exact ⟨σ, C, hσ, hC, hcard, hcov, hsurj, hbound, hsmall⟩

lemma exists_ge_coord_of_simplex_map (n : ℕ)
    (x : ↑(stdSimplex ℝ (Fin (n + 1))))
    (f : ↑(stdSimplex ℝ (Fin (n + 1))) → ↑(stdSimplex ℝ (Fin (n + 1)))) :
    ∃ i : Fin (n + 1), ((f x) : Fin (n + 1) → ℝ) i ≥ (x : Fin (n + 1) → ℝ) i := by
  by_contra! h₂
  -- Extract the coordinates of x and f(x)
  have h₃ : ∑ i : Fin (n + 1), (x : Fin (n + 1) → ℝ) i = 1 := x.2.2
  have h₄ : ∑ i : Fin (n + 1), ((f x) : Fin (n + 1) → ℝ) i = 1 := (f x).2.2
  -- Use the fact that each f(x)_i < x_i to show that the sum of f(x)_i is less than the sum of x_i
  suffices ∑ i : Fin (n + 1), f x i < ∑ i : Fin (n + 1), x i by linarith
  -- Use the fact that each f(x)_i < x_i to show that the sum of f(x)_i is less than the sum of x_i
  calc
    ∑ i : Fin (n + 1), f x i < ∑ i : Fin (n + 1), x i := by
      -- Use the sum_lt_sum_of_nonempty lemma to compare the sums
      have h₅₂ : ∑ i : Fin (n + 1), f x i < ∑ i : Fin (n + 1), x i := by
        -- Use that each f(x)_i < x_i to show that the sum of f(x)_i is less than the sum of x_i
        apply Finset.sum_lt_sum_of_nonempty
        · -- Show that the set of indices is nonempty
          exact Finset.nonempty_of_ne_empty (by grind)
        · -- Show that each term in the sum is less than the corresponding term in the other sum
          grind
      exact h₅₂
    _ = ∑ i : Fin (n + 1), (x : Fin (n + 1) → ℝ) i := by rfl

lemma exists_colorful_room (n : ℕ) (l : ℕ) (hl : 0 < l)
    (f : ↑(stdSimplex ℝ (Fin (n + 1))) → ↑(stdSimplex ℝ (Fin (n + 1)))) :
    ∃ (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1)))) (C : Finset (Fin (n + 1))),
      σ.Nonempty ∧ C.Nonempty ∧
      σ.card = C.card ∧
      (∀ i ∈ C, ∃ z ∈ σ, ((f z) : Fin (n + 1) → ℝ) i ≥ (z : Fin (n + 1) → ℝ) i) ∧
      (∀ x ∈ σ, ∀ y ∈ σ, ∀ i,
        |(x : Fin (n + 1) → ℝ) i - (y : Fin (n + 1) → ℝ) i| <
          2 * (↑(n + 1) : ℝ) / (↑l : ℝ)) ∧
      (∀ x ∈ σ, ∀ i, i ∉ C →
        (x : Fin (n + 1) → ℝ) i < (↑(n + 1) : ℝ) / (↑l : ℝ)) := by
  -- Define the coloring: c(x) = some i with f(x)_i ≥ x_i
  let c : ↑(stdSimplex ℝ (Fin (n + 1))) → Fin (n + 1) :=
    fun x ↦ (exists_ge_coord_of_simplex_map n x f).choose
  -- Apply Scarf's theorem with this coloring
  obtain ⟨σ, C, hσne, hCne, hcard, hcσ, hcover, hdiam, hsmall⟩ :=
    exists_colorful_room_with_bounds n l hl c
  refine ⟨σ, C, hσne, hCne, hcard, ?_, hdiam, hsmall⟩
  -- For each i ∈ C, find witness z ∈ σ with f(z)_i ≥ z_i
  intro i hi
  obtain ⟨x, hx, hcx⟩ := hcover i hi
  refine ⟨x, hx, ?_⟩
  -- c(x) = i means (exists_ge_coord_of_simplex_map n x f).choose = i
  -- and choose_spec gives f(x) at that coordinate ≥ x at that coordinate
  have h1 := (exists_ge_coord_of_simplex_map n x f).choose_spec
  have h2 : (exists_ge_coord_of_simplex_map n x f).choose = i := hcx
  rw [h2] at h1
  exact h1

lemma exists_convergent_subseq (n : ℕ)
    (x : ℕ → ↑(stdSimplex ℝ (Fin (n + 1)))) :
    ∃ (z : ↑(stdSimplex ℝ (Fin (n + 1))))
      (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto (fun l ↦ (x (φ l) : Fin (n + 1) → ℝ)) Filter.atTop
        (nhds (z : Fin (n + 1) → ℝ)) := by
  have hcomp : IsCompact (stdSimplex ℝ (Fin (n + 1))) := isCompact_stdSimplex ℝ _
  have hmem : ∀ m, (x m : Fin (n + 1) → ℝ) ∈ stdSimplex ℝ (Fin (n + 1)) := fun m ↦ (x m).2
  obtain ⟨a, ha, φ, hφ, htend⟩ := hcomp.tendsto_subseq hmem
  exact ⟨⟨a, ha⟩, φ, hφ, htend⟩

lemma exists_const_finset_subseq (n : ℕ) (C : ℕ → Finset (Fin (n + 1))) :
    ∃ (C₀ : Finset (Fin (n + 1))) (φ : ℕ → ℕ),
      StrictMono φ ∧ ∀ l, C (φ l) = C₀ := by
  obtain ⟨C₀, hC₀⟩ := Finite.exists_infinite_fiber C
  -- The preimage {k : ℕ | C k = C₀} is infinite
  let p : ℕ → Prop := fun k ↦ C k = C₀
  have hp : (Set.ofPred p).Infinite := Set.infinite_coe_iff.mp hC₀
  -- Use Nat.nth to enumerate it strictly monotonically
  refine ⟨C₀, Nat.nth p, Nat.nth_strictMono hp, fun l ↦ ?_⟩
  exact Nat.nth_mem_of_infinite hp l

lemma close_seqs_same_limit (n : ℕ)
    (u v : ℕ → Fin (n + 1) → ℝ) (z : Fin (n + 1) → ℝ)
    (hv : Filter.Tendsto v Filter.atTop (nhds z))
    (bound : ℕ → ℝ) (hbound : Filter.Tendsto bound Filter.atTop (nhds 0))
    (hclose : ∀ l, ∀ i, |u l i - v l i| < bound l) :
    Filter.Tendsto u Filter.atTop (nhds z) := by
  rw [tendsto_pi_nhds] at hv ⊢
  intro i
  have hvi := hv i
  rw [Metric.tendsto_atTop] at hvi ⊢
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := hvi (ε / 2) hε2
  have hbound_metric : Filter.Tendsto bound Filter.atTop (nhds 0) := hbound
  rw [Metric.tendsto_atTop] at hbound_metric
  obtain ⟨N₂, hN₂⟩ := hbound_metric (ε / 2) hε2
  refine ⟨max N₁ N₂, fun l hl ↦ ?_⟩
  have hl₁ : l ≥ N₁ := le_of_max_le_left hl
  have hl₂ : l ≥ N₂ := le_of_max_le_right hl
  simp only [Real.dist_eq]
  have hN₁' : |v l i - z i| < ε / 2 := by
    have := hN₁ l hl₁; simp only [Real.dist_eq] at this; exact this
  have hN₂' : |bound l| < ε / 2 := by
    have := hN₂ l hl₂; simp only [Real.dist_eq, sub_zero] at this; exact this
  calc |u l i - z i| = |(u l i - v l i) + (v l i - z i)| := by ring_nf
    _ ≤ |u l i - v l i| + |v l i - z i| := abs_add_le _ _
    _ < bound l + |v l i - z i| := by linarith [hclose l i]
    _ ≤ |bound l| + |v l i - z i| := by linarith [le_abs_self (bound l)]
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

lemma ge_coord_of_tendsto (n : ℕ) (i : Fin (n + 1))
    (x : ℕ → Fin (n + 1) → ℝ) (z : Fin (n + 1) → ℝ)
    (y : ℕ → Fin (n + 1) → ℝ) (w : Fin (n + 1) → ℝ)
    (hx : Filter.Tendsto x Filter.atTop (nhds z))
    (hy : Filter.Tendsto y Filter.atTop (nhds w))
    (hge : ∀ l, (y l) i ≥ (x l) i) :
    w i ≥ z i := by
  have h₁ : Filter.Tendsto (fun l ↦ (x l) i) Filter.atTop (nhds (z i)) := by
    have h₂ : Continuous (fun p : Fin (n + 1) → ℝ ↦ p i) := by continuity
    have h₄ : Filter.Tendsto (fun l ↦ (x l) i) Filter.atTop (nhds (z i)) :=
      h₂.continuousAt.tendsto.comp hx
    exact h₄
  have h₂ : Filter.Tendsto (fun l ↦ (y l) i) Filter.atTop (nhds (w i)) := by
    have h₃ : Continuous (fun p : Fin (n + 1) → ℝ ↦ p i) := by continuity
    have h₄ : Filter.Tendsto y Filter.atTop (nhds w) := hy
    have h₅ : Filter.Tendsto (fun l ↦ (y l) i) Filter.atTop (nhds (w i)) :=
      h₃.continuousAt.tendsto.comp h₄
    exact h₅
  -- Use the fact that the limit of the difference is non-negative.
  have h₉ : Filter.Tendsto (fun l ↦ (y l) i - (x l) i) Filter.atTop (nhds (w i - z i)) := by
    exact h₂.sub h₁
  have h₁₀ : ∀ l, (y l) i - (x l) i ≥ 0 := by
    intro l
    have h₁₁ : (y l) i ≥ (x l) i := hge l
    linarith
  suffices (w i - z i) ≥ 0 by linarith
  by_contra h
  have h₁₆ : ∃ (l : ℕ), (y l) i - (x l) i < 0 := by
    -- Use the fact that the sequence is eventually in the neighborhood of the limit.
    have h₂₀ : ∃ (l : ℕ), ∀ k ≥ l, |(y k) i - (x k) i - (w i - z i)| < - (w i - z i) := by
      -- Find an l such that for all k ≥ l, the sequence is in the neighborhood of the limit.
      have h₂₂ : ∀ ε > 0, ∃ (l : ℕ), ∀ k ≥ l, |(y k) i - (x k) i - (w i - z i)| < ε :=
        Metric.tendsto_atTop.mp (h₂.sub h₁)
      exact h₂₂ (- (w i - z i)) (by linarith)
    obtain ⟨l, hl⟩ := h₂₀
    use l
    have h₂₁ := hl l (by linarith)
    linarith [abs_lt.mp h₂₁]
  obtain ⟨l, hl⟩ := h₁₆
  have h₁₉ : (y l) i - (x l) i ≥ 0 := h₁₀ l
  linarith

/-- The bound sequence (n+1)/(φ(l)+1) tends to 0 when φ is strictly monotone.
    Since φ is strictly monotone on ℕ, `StrictMono.tendsto_atTop` gives φ(l) → ∞,
    hence φ(l)+1 → ∞, so (φ(l)+1)⁻¹ → 0, and multiplying by the constant (n+1) gives
    (n+1)/(φ(l)+1) → 0. -/
lemma tendsto_bound_zero (n : ℕ) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Filter.Tendsto (fun l ↦ (↑(n + 1) : ℝ) / (↑(φ l + 1) : ℝ)) Filter.atTop (nhds 0) := by
  have hφ1 : StrictMono (fun l ↦ φ l + 1) := fun a b hab ↦ Nat.add_lt_add_right (hφ hab) 1
  have h1 : Filter.Tendsto (fun l ↦ (↑(φ l + 1) : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ1.tendsto_atTop
  simp_rw [div_eq_mul_inv]
  have h2 : (0 : ℝ) = (↑(n + 1) : ℝ) * 0 := by ring
  rw [h2]
  exact Filter.Tendsto.const_mul _ h1

lemma coord_zero_of_tendsto_bound (n : ℕ) (i : Fin (n + 1))
    (x_seq : ℕ → Fin (n + 1) → ℝ)
    (z : Fin (n + 1) → ℝ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : Filter.Tendsto (x_seq ∘ φ) Filter.atTop (nhds z))
    (hbound : ∀ l, x_seq (φ l) i < (↑(n + 1) : ℝ) / (↑(φ l + 1) : ℝ))
    (hnn : ∀ l, 0 ≤ x_seq (φ l) i) :
    z i = 0 := by
  -- Step 1: The i-th coordinate of the subsequence converges to z i
  have hconv_i : Filter.Tendsto (fun l ↦ x_seq (φ l) i) Filter.atTop (nhds (z i)) :=
    tendsto_pi_nhds.mp hconv i
  -- Step 2: The bound sequence tends to 0
  have hbound_tendsto : Filter.Tendsto (fun l ↦ (↑(n + 1) : ℝ) / ↑(φ l + 1)) .atTop (nhds 0) :=
    tendsto_bound_zero n φ hφ
  -- Step 3: By squeeze theorem, the i-th coordinate tends to 0
  have htendsto_zero : Filter.Tendsto (fun l ↦ x_seq (φ l) i) Filter.atTop (nhds 0) :=
    squeeze_zero hnn (fun l ↦ le_of_lt (hbound l)) hbound_tendsto
  -- Step 4: By uniqueness of limits, z i = 0
  exact tendsto_nhds_unique hconv_i htendsto_zero

lemma sum_eq_one_of_zero_outside (n : ℕ)
    (z : Fin (n + 1) → ℝ) (hz : z ∈ stdSimplex ℝ (Fin (n + 1)))
    (C : Finset (Fin (n + 1)))
    (hzero : ∀ i, i ∉ C → z i = 0) :
    ∑ i ∈ C, z i = 1 := by
  have h₃ : ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))) \ C, z i = 0 := by
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))) \ C, z i
      _ = ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))) \ C, 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        have h₄ : i ∉ C := by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
          exact hi
        have h₅ : z i = 0 := hzero i h₄
        rw [h₅]
      _ = 0 := by simp
  have h₄ : ∑ i ∈ Finset.univ, z i = ∑ i ∈ C, z i + ∑ i ∈ Finset.univ \ C, z i := by
    have h₅ : ∑ i ∈ Finset.univ, z i = ∑ i ∈ C ∪ (Finset.univ \ C), z i := by
      congr 1
      simp [Finset.ext_iff]
    rw [h₅]
    have h₇ : Disjoint C (Finset.univ \ C) := by
      simp [Finset.disjoint_left]
    rw [Finset.sum_union h₇]
  have h₅ : ∑ i ∈ C, z i = 1 := by
    linarith [hz.2]
  exact h₅

lemma sum_compl_eq_zero (n : ℕ)
    (w : Fin (n + 1) → ℝ)
    (hw : w ∈ stdSimplex ℝ (Fin (n + 1)))
    (C : Finset (Fin (n + 1)))
    (hge_sum : ∑ i ∈ C, w i ≥ 1) :
    ∑ i ∈ Cᶜ, w i = 0 := by
  have h1 : ∑ i ∈ Cᶜ, w i + ∑ i ∈ C, w i = ∑ i, w i := Finset.sum_compl_add_sum C w
  have h5 : 0 ≤ ∑ i ∈ Cᶜ, w i := Finset.sum_nonneg (fun i _ ↦ hw.1 i)
  linarith [hw.2]

lemma eq_of_ge_sum_one (n : ℕ)
    (z w : Fin (n + 1) → ℝ)
    (hw : w ∈ stdSimplex ℝ (Fin (n + 1)))
    (C : Finset (Fin (n + 1)))
    (hge : ∀ i ∈ C, w i ≥ z i)
    (hzero_z : ∀ i, i ∉ C → z i = 0)
    (hsum_z : ∑ i ∈ C, z i = 1) :
    ∀ i, w i = z i := by
  -- Step 1: ∑_{i∈C} w_i ≥ 1
  have hge_sum : ∑ i ∈ C, w i ≥ 1 := by
    calc ∑ i ∈ C, w i ≥ ∑ i ∈ C, z i := Finset.sum_le_sum (fun i hi ↦ hge i hi)
    _ = 1 := hsum_z
  -- Step 2: ∑_{i∈Cᶜ} w_i = 0
  have hsc := sum_compl_eq_zero n w hw C hge_sum
  -- Step 3: w_i = 0 for i ∉ C (from sum of nonneg = 0)
  have hwz : ∀ i, i ∉ C → w i = 0 := by
    intro i hi
    have hmem : i ∈ Cᶜ := Finset.mem_compl.mpr hi
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hw.1 j)).mp hsc i hmem
    exact this
  -- Step 4: ∑_{i∈C} w_i = 1
  have hsumC : ∑ i ∈ C, w i = 1 := by
    have h1 : ∑ i ∈ Cᶜ, w i + ∑ i ∈ C, w i = 1 := by
      rw [Finset.sum_compl_add_sum]; exact hw.2
    linarith
  -- Step 5: w_i = z_i for i ∈ C (equal sums + pointwise ≥)
  have hweq : ∀ i ∈ C, w i = z i := by
    have heq : ∑ i ∈ C, z i = ∑ i ∈ C, w i := by linarith
    have := (Finset.sum_eq_sum_iff_of_le (fun i hi ↦ hge i hi)).mp heq
    intro i hi; exact (this i hi).symm
  -- Step 6: Combine
  intro i
  by_cases hi : i ∈ C
  · exact hweq i hi
  · simp [hwz i hi, hzero_z i hi]

/-- Lifting ambient-space convergence through a continuous subtype self-map.
    Given that x_l → z in the ambient space (Fin (n+1) → ℝ) and f is continuous
    on the simplex subtype, we get f(x_l) → f(z) in the ambient space.

    The proof chains three steps:
    1. Ambient convergence ↑(x l) → ↑z lifts to subtype convergence x l → z
       via the induced topology (nhds z = comap Subtype.val (nhds ↑z)),
       using `Filter.tendsto_comap_iff`.
    2. Continuity of f gives f(x l) → f(z) in the subtype via `Continuous.tendsto`.
    3. Continuity of Subtype.val pushes back to ambient: ↑(f(x l)) → ↑(f(z))
       via `continuous_subtype_val.tendsto`.

    Mathlib has:
    - `Filter.tendsto_comap_iff : Tendsto f a (comap g c) ↔ Tendsto (g ∘ f) a c`
    - `Continuous.tendsto : Continuous f → ∀ x, Tendsto f (nhds x) (nhds (f x))`
    - `Filter.Tendsto.comp : Tendsto g y z → Tendsto f x y → Tendsto (g ∘ f) x z`
    - `continuous_subtype_val : Continuous Subtype.val` -/
lemma tendsto_apply_of_subtype_tendsto (n : ℕ)
    (f : ↑(stdSimplex ℝ (Fin (n + 1))) → ↑(stdSimplex ℝ (Fin (n + 1))))
    (hf : Continuous f)
    (x : ℕ → ↑(stdSimplex ℝ (Fin (n + 1))))
    (z : ↑(stdSimplex ℝ (Fin (n + 1))))
    (hconv : Filter.Tendsto (fun l ↦ (x l : Fin (n + 1) → ℝ))
      Filter.atTop (nhds (z : Fin (n + 1) → ℝ))) :
    Filter.Tendsto (fun l ↦ ((f (x l)) : Fin (n + 1) → ℝ))
      Filter.atTop (nhds ((f z) : Fin (n + 1) → ℝ)) := by
  -- Step 1: Lift ambient convergence to subtype convergence
  have hx_sub : Filter.Tendsto x Filter.atTop (nhds z) := by
    rw [nhds_induced]
    exact Filter.tendsto_comap_iff.mpr hconv
  -- Step 2+3: Apply f then push to ambient
  exact (continuous_subtype_val.tendsto _).comp ((hf.tendsto z).comp hx_sub)

lemma tendsto_bound_to_zero (n : ℕ) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Filter.Tendsto (fun l ↦ 2 * (↑(n + 1) : ℝ) / (↑(φ l + 1) : ℝ))
      Filter.atTop (nhds 0) := by
  apply Filter.Tendsto.const_div_atTop _ (2 * (↑(n + 1) : ℝ))
  have h2 : Filter.Tendsto (fun l ↦ φ l + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun l ↦ Nat.le_add_right (φ l) 1) hφ.tendsto_atTop
  have h3 : Filter.Tendsto (fun l ↦ (↑(φ l + 1) : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp h2
  exact h3

theorem brouwer_fixed_point (n : ℕ)
    (f : ↑(stdSimplex ℝ (Fin (n + 1))) → ↑(stdSimplex ℝ (Fin (n + 1))))
    (hf : Continuous f) :
    ∃ z : ↑(stdSimplex ℝ (Fin (n + 1))), f z = z := by
  -- Step 1: For each l ≥ 1, get a colorful room from Scarf's theorem
  have hrooms : ∀ l : ℕ,
      ∃ (σ : Finset ↑(stdSimplex ℝ (Fin (n + 1)))) (C : Finset (Fin (n + 1))),
        σ.Nonempty ∧ C.Nonempty ∧
        σ.card = C.card ∧
        (∀ i ∈ C, ∃ z ∈ σ, ((f z) : Fin (n + 1) → ℝ) i ≥ (z : Fin (n + 1) → ℝ) i) ∧
        (∀ x ∈ σ, ∀ y ∈ σ, ∀ i,
          |(x : Fin (n + 1) → ℝ) i - (y : Fin (n + 1) → ℝ) i| <
            2 * (↑(n + 1) : ℝ) / (↑(l + 1) : ℝ)) ∧
        (∀ x ∈ σ, ∀ i, i ∉ C →
          (x : Fin (n + 1) → ℝ) i < (↑(n + 1) : ℝ) / (↑(l + 1) : ℝ)) := by
    intro l; exact exists_colorful_room n (l + 1) (Nat.succ_pos l) f
  -- Choose σ_l, C_l for each l
  choose σ C hσne hCne hcard hcolor hdiam hsmall using hrooms
  -- Step 2: Pick a representative x_l from each σ_l
  choose x_rep hx_rep_mem using hσne
  -- Step 3: Extract convergent subsequence by compactness
  obtain ⟨z, φ₁, hφ₁, hconv₁⟩ := exists_convergent_subseq n x_rep
  -- Step 4: Extract further subsequence with constant C
  obtain ⟨C₀, φ₂, hφ₂, hC_eq⟩ := exists_const_finset_subseq n (C ∘ φ₁)
  -- Compose subsequences
  set φ := φ₁ ∘ φ₂ with hφ_def
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  -- The convergence still holds along the further subsequence
  have hconv : Filter.Tendsto (fun l ↦ (x_rep (φ l) : Fin (n + 1) → ℝ))
      Filter.atTop (nhds (z : Fin (n + 1) → ℝ)) :=
    hconv₁.comp hφ₂.tendsto_atTop
  -- C(φ(l)) = C₀ for all l
  have hC : ∀ l, C (φ l) = C₀ := hC_eq
  -- Step 5: For each i ∈ C₀, get coordinate inequality at limit
  have hge_limit : ∀ i ∈ C₀, ((f z) : Fin (n + 1) → ℝ) i ≥ (z : Fin (n + 1) → ℝ) i := by
    intro i hi
    -- For each l, get witness
    have hw : ∀ l, ∃ w ∈ σ (φ l),
        ((f w) : Fin (n + 1) → ℝ) i ≥ (w : Fin (n + 1) → ℝ) i := by
      intro l; exact hcolor (φ l) i ((hC l).symm ▸ hi)
    choose w hw_mem hw_ge using hw
    -- w_l and x_rep(φ l) are close (both in σ(φ l), diameter → 0)
    -- So w_l → z as well
    have hw_conv : Filter.Tendsto (fun l ↦ (w l : Fin (n + 1) → ℝ))
        Filter.atTop (nhds (z : Fin (n + 1) → ℝ)) := by
      apply close_seqs_same_limit n
        (fun l ↦ (w l : Fin (n + 1) → ℝ))
        (fun l ↦ (x_rep (φ l) : Fin (n + 1) → ℝ))
        (z : Fin (n + 1) → ℝ)
        hconv
        (fun l ↦ 2 * (↑(n + 1) : ℝ) / (↑(φ l + 1) : ℝ))
      · exact tendsto_bound_to_zero n φ hφ
      · intro l j
        exact hdiam (φ l) (w l) (hw_mem l) (x_rep (φ l)) (hx_rep_mem (φ l)) j
    -- f(w_l) → f(z) by continuity
    have hfw_conv : Filter.Tendsto (fun l ↦ ((f (w l)) : Fin (n + 1) → ℝ))
        Filter.atTop (nhds ((f z) : Fin (n + 1) → ℝ)) :=
      tendsto_apply_of_subtype_tendsto n f hf w z hw_conv
    -- Pass inequality to limit
    exact ge_coord_of_tendsto n i
      (fun l ↦ (w l : Fin (n + 1) → ℝ))
      (z : Fin (n + 1) → ℝ)
      (fun l ↦ ((f (w l)) : Fin (n + 1) → ℝ))
      ((f z) : Fin (n + 1) → ℝ)
      hw_conv hfw_conv hw_ge
  -- Step 6: For i ∉ C₀, z_i = 0
  have hzero : ∀ i, i ∉ C₀ → (z : Fin (n + 1) → ℝ) i = 0 := by
    intro i hi
    apply coord_zero_of_tendsto_bound n i
      (fun l ↦ (x_rep l : Fin (n + 1) → ℝ))
      (z : Fin (n + 1) → ℝ) φ hφ hconv
    · intro l
      exact hsmall (φ l) (x_rep (φ l)) (hx_rep_mem (φ l)) i ((hC l).symm ▸ hi)
    · intro l
      exact (x_rep (φ l)).property.1 i
  -- Step 7: Sum constraint
  have hsum : ∑ i ∈ C₀, (z : Fin (n + 1) → ℝ) i = 1 :=
    sum_eq_one_of_zero_outside n (z : Fin (n + 1) → ℝ) z.property C₀ hzero
  -- Step 8: Conclude f(z) = z
  have heq : ∀ i, ((f z) : Fin (n + 1) → ℝ) i = (z : Fin (n + 1) → ℝ) i :=
    eq_of_ge_sum_one n
      (z : Fin (n + 1) → ℝ) ((f z) : Fin (n + 1) → ℝ)
      (f z).property C₀ hge_limit hzero hsum
  exact ⟨z, Subtype.ext (funext heq)⟩

/-! ## Convex combinations and evaluation maps -/

/-- A convex combination of points in a convex set lies in that set. -/
lemma convex_combination_mem {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K : Set E} (hK_convex : Convex ℝ K)
    {N : ℕ} (pts : Fin N → E) (hpts : ∀ i, pts i ∈ K)
    (w : Fin N → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1) :
    ∑ i, w i • pts i ∈ K :=
  hK_convex.sum_mem (fun i _ ↦ hw_nonneg i) hw_sum (fun i _ ↦ hpts i)

/-- The evaluation map sending barycentric coordinates to the
corresponding convex combination of points is continuous. -/
lemma eval_map_continuous {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {N : ℕ} (pts : Fin N → E) :
    Continuous (fun w : (stdSimplex ℝ (Fin N)) ↦ ∑ i, (w : Fin N → ℝ) i • pts i) :=
  continuous_finsetSum _ fun i _ ↦
    ((continuous_apply i).comp continuous_subtype_val).smul continuous_const

/-! ## Finite covers and partitions of unity -/

/-- A compact set can be covered by finitely many translates of an open neighborhood of zero. -/
lemma finite_cover_of_compact
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    {K : Set E} (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty)
    {U : Set E} (hU_open : IsOpen U) (hU_zero : (0 : E) ∈ U) :
    ∃ (N : ℕ) (pts : Fin (N + 1) → E),
      (∀ i, pts i ∈ K) ∧
      K ⊆ ⋃ i : Fin (N + 1), (fun u ↦ pts i + u) '' U := by
  have h_open : ∀ x : E, IsOpen ((fun u ↦ x + u) '' U) := fun x ↦ by
    rw [Set.image_add_left]
    exact hU_open.preimage (continuous_const.add continuous_id)
  have h_mem : ∀ x : E, x ∈ (fun u ↦ x + u) '' U :=
    fun x ↦ ⟨0, hU_zero, by simp⟩
  obtain ⟨t, ht_mem, ht_cover⟩ := hK_compact.elim_nhds_subcover
    (fun x ↦ (fun u ↦ x + u) '' U)
    (fun x _ ↦ (h_open x).mem_nhds (h_mem x))
  have ht_ne : t.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := hK_nonempty
    have := ht_cover hx
    simp [h] at this
  have ht_pos : 0 < t.card := ht_ne.card_pos
  let e := t.equivFin
  refine ⟨t.card - 1, fun i ↦ (e.symm (i.cast (Nat.succ_pred_eq_of_pos ht_pos))).val, ?_, ?_⟩
  · intro i
    exact ht_mem _ (e.symm (i.cast (Nat.succ_pred_eq_of_pos ht_pos))).prop
  · intro x hx
    obtain ⟨y, hy_mem, hy_cover⟩ := Set.mem_iUnion₂.mp (ht_cover hx)
    rw [Set.mem_iUnion]
    let j := e ⟨y, hy_mem⟩
    refine ⟨j.cast (Nat.succ_pred_eq_of_pos ht_pos).symm, ?_⟩
    suffices h : (e.symm (Fin.cast (Nat.succ_pred_eq_of_pos ht_pos)
        (j.cast (Nat.succ_pred_eq_of_pos ht_pos).symm))).val = y by
      simp only [h]
      exact hy_cover
    have : Fin.cast (Nat.succ_pred_eq_of_pos ht_pos)
        (j.cast (Nat.succ_pred_eq_of_pos ht_pos).symm) = j := by ext; simp
    rw [this]
    exact congr_arg Subtype.val (e.symm_apply_apply ⟨y, hy_mem⟩)

/-- Evaluating a partition of unity at a point gives a point in the standard simplex. -/
lemma partition_of_unity_maps_to_simplex
    {X : Type*} [TopologicalSpace X] {N : ℕ}
    (ρ : PartitionOfUnity (Fin (N + 1)) X Set.univ)
    (x : X) :
    (fun i ↦ (ρ i) x) ∈ stdSimplex ℝ (Fin (N + 1)) := by
  rw [stdSimplex.eq_1]
  refine ⟨fun i ↦ ρ.nonneg i x, ?_⟩
  have := ρ.sum_eq_one (Set.mem_univ x)
  rwa [finsum_eq_sum_of_fintype] at this

/-- The map sending a point to its partition of unity coordinates in the simplex is continuous. -/
lemma partition_of_unity_phi_continuous
    {X : Type*} [TopologicalSpace X] {N : ℕ}
    (ρ : PartitionOfUnity (Fin (N + 1)) X Set.univ) :
    Continuous (fun x : X ↦ (⟨fun i ↦ (ρ i) x,
      partition_of_unity_maps_to_simplex ρ x⟩ : (stdSimplex ℝ (Fin (N + 1))))) :=
  Continuous.subtype_mk (continuous_pi (fun i ↦ (ρ i).continuous)) _

/-! ## Subordination and approximation -/

/-- If `(ρ i) x ≠ 0` and `ρ` is subordinate to translates of `U`, then `(x : E) - pts i ∈ U`. -/
lemma subordination_gives_mem_U
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {K : Set E} {U : Set E}
    {N : ℕ} (pts : Fin (N + 1) → E)
    (ρ : PartitionOfUnity (Fin (N + 1)) K Set.univ)
    (hρ_sub : ρ.IsSubordinate (fun i ↦ Subtype.val ⁻¹' ((fun u ↦ pts i + u) '' U)))
    (i : Fin (N + 1)) (x : K) (hne : (ρ i) x ≠ 0) :
    (x : E) - pts i ∈ U := by
  have hx_pre := hρ_sub i (subset_tsupport _ (Function.mem_support.mpr hne))
  rw [Set.mem_preimage] at hx_pre
  obtain ⟨u, hu, hxu⟩ := hx_pre
  rwa [show (x : E) - pts i = u from by
    have : pts i + u = (x : E) := by simpa using hxu
    rw [← this]
    abel]

/-- ∑ᶠ i, (ρ i) x • ((x : E) - pts i) = (x : E) - ∑ i, (ρ i) x • pts i. -/
lemma finsum_smul_sub_eq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {K : Set E}
    {N : ℕ} (pts : Fin (N + 1) → E)
    (ρ : PartitionOfUnity (Fin (N + 1)) K Set.univ)
    (x : K) :
    ∑ᶠ i, (ρ i) x • ((x : E) - pts i) = (x : E) - ∑ i, (ρ i) x • pts i := by
  rw [finsum_eq_sum_of_fintype]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul,
    show ∑ i : Fin (N + 1), (ρ i) x = 1 from by
      rw [← finsum_eq_sum_of_fintype]; exact ρ.sum_eq_one (Set.mem_univ x),
    one_smul]

/-- The convex combination from a subordinate partition of unity approximates each point. -/
lemma approximation_from_partition_of_unity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {K : Set E} {U : Set E} (hU_convex : Convex ℝ U)
    {N : ℕ} (pts : Fin (N + 1) → E)
    (ρ : PartitionOfUnity (Fin (N + 1)) K Set.univ)
    (hρ_sub : ρ.IsSubordinate (fun i ↦ Subtype.val ⁻¹' ((fun u ↦ pts i + u) '' U)))
    (x : K) :
    (x : E) - ∑ i, (ρ i) x • pts i ∈ U := by
  rw [← finsum_smul_sub_eq pts ρ x]
  exact ρ.finsum_smul_mem_convex (g := fun i _ ↦ (x : E) - pts i)
    (Set.mem_univ x)
    (fun i hne ↦ subordination_gives_mem_U pts ρ hρ_sub i x hne) hU_convex

/-! ## Schauder projection-evaluation pair -/

/-- For any open convex neighborhood `U` of zero, there exist continuous maps
`φ : K → Δ_N` and `ψ : Δ_N → K` such that `x - ψ(φ(x)) ∈ U` for all `x ∈ K`. -/
lemma schauder_projection_eval_pair
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {K : Set E} (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) (hK_nonempty : K.Nonempty)
    {U : Set E} (hU_open : IsOpen U) (hU_zero : (0 : E) ∈ U) (hU_convex : Convex ℝ U) :
    ∃ (N : ℕ) (φ : K → stdSimplex ℝ (Fin (N + 1)))
      (ψ : stdSimplex ℝ (Fin (N + 1)) → K),
      Continuous φ ∧ Continuous ψ ∧
      ∀ x : K, (x : E) - (ψ (φ x) : E) ∈ U := by
  obtain ⟨N, pts, hpts_mem, hK_cover⟩ :=
    finite_cover_of_compact hK_compact hK_nonempty hU_open hU_zero
  have hV_open : ∀ i : Fin (N + 1),
      IsOpen (Subtype.val ⁻¹' ((fun u ↦ pts i + u) '' U) : Set K) :=
    fun i ↦ ((isOpenMap_add_left (pts i)) U hU_open).preimage continuous_subtype_val
  have hV_cover : Set.univ ⊆
      ⋃ i : Fin (N + 1), (Subtype.val ⁻¹' ((fun u ↦ pts i + u) '' U) : Set K) := by
    intro ⟨x, hx⟩ _
    simp only [Set.mem_iUnion, Set.mem_preimage]
    exact Set.mem_iUnion.mp (hK_cover hx)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK_compact
  obtain ⟨ρ, hρ_sub⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i ↦ Subtype.val ⁻¹' ((fun u ↦ pts i + u) '' U)) hV_open hV_cover
  exact ⟨N,
    fun x ↦ ⟨fun i ↦ (ρ i) x, partition_of_unity_maps_to_simplex ρ x⟩,
    fun w ↦ ⟨∑ i, (w : Fin (N + 1) → ℝ) i • pts i,
      convex_combination_mem hK_convex pts hpts_mem _ (fun i ↦ w.2.1 i) w.2.2⟩,
    partition_of_unity_phi_continuous ρ,
    continuous_induced_rng.mpr (eval_map_continuous pts),
    fun x ↦ approximation_from_partition_of_unity hU_convex pts ρ hρ_sub x⟩

/-! ## Approximate and exact fixed points -/

/-- Using Brouwer on simplices, any continuous self-map of a compact convex set has
approximate fixed points in every open neighborhood of zero. -/
lemma approximate_fixed_point_of_brouwer
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {K : Set E} (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) (hK_nonempty : K.Nonempty)
    (f : K → K) (hf : Continuous f)
    {U : Set E} (hU_open : IsOpen U) (hU_zero : (0 : E) ∈ U) (hU_convex : Convex ℝ U) :
    ∃ z : K, (f z : E) - (z : E) ∈ U := by
  obtain ⟨N, φ, ψ, hφ_cont, hψ_cont, happrox⟩ :=
    schauder_projection_eval_pair hK_compact hK_convex hK_nonempty hU_open hU_zero hU_convex
  obtain ⟨y, hy⟩ := brouwer_fixed_point N (φ ∘ f ∘ ψ) (hφ_cont.comp (hf.comp hψ_cont))
  refine ⟨ψ y, ?_⟩
  have key := happrox (f (ψ y))
  rwa [show φ (f (ψ y)) = y from hy] at key

/-- If a continuous self-map of a compact set has approximate fixed points in every
neighborhood of zero, then it has an exact fixed point. -/
lemma fixed_point_of_approximate_fixed_points
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {K : Set E} (hK_compact : IsCompact K)
    (f : K → K) (hf : Continuous f)
    (happrox : ∀ U : Set E, IsOpen U → (0 : E) ∈ U →
      ∃ z : K, (f z : E) - (z : E) ∈ U) :
    ∃ x : K, f x = x := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK_compact
  have hclosed : IsClosed (Set.range (fun z : K ↦ (f z : E) - (z : E))) :=
    (isCompact_range (hf.subtype_val.sub continuous_subtype_val)).isClosed
  have h0 : (0 : E) ∈ closure (Set.range (fun z : K ↦ (f z : E) - (z : E))) := by
    rw [mem_closure_iff]
    intro U hU hU0
    obtain ⟨z, hz⟩ := happrox U hU hU0
    exact ⟨(f z : E) - (z : E), hz, z, rfl⟩
  rw [hclosed.closure_eq] at h0
  obtain ⟨z, hz⟩ := h0
  exact ⟨z, Subtype.val_injective (sub_eq_zero.mp hz)⟩

end

/-! ## Main theorems -/
@[expose] public section

/-! ## Finite-dimensional spaces are locally convex -/

/-- A finite-dimensional Hausdorff topological vector space over ℝ is locally convex. -/
instance FiniteDimensional.locallyConvexSpace
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [FiniteDimensional ℝ E] :
    LocallyConvexSpace ℝ E := by
  set n := Module.finrank ℝ E
  set φ := ContinuousLinearEquiv.ofFinrankEq
    (show Module.finrank ℝ E = Module.finrank ℝ (Fin n → ℝ) by rw [Module.finrank_fin_fun])
  apply LocallyConvexSpace.ofBasisZero ℝ E (fun (s : Set (Fin n → ℝ)) ↦ φ ⁻¹' s)
    (fun s ↦ s ∈ nhds (0 : Fin n → ℝ) ∧ Convex ℝ s)
  · rw [show nhds (0 : E) = Filter.comap φ (nhds (0 : Fin n → ℝ)) from by
      rw [φ.toHomeomorph.nhds_eq_comap]
      congr 1
      simp [ContinuousLinearEquiv.toHomeomorph, map_zero]]
    exact (LocallyConvexSpace.convex_basis_zero ℝ (Fin n → ℝ)).comap φ
  · intro s ⟨_, hs⟩
    exact hs.linear_preimage φ.toLinearMap

/-- **Schauder's Fixed Point Theorem.** Every continuous self-map of a nonempty compact convex
subset of a Hausdorff locally convex topological vector space has a fixed point. -/
theorem Continuous.exists_fixedPt_of_isConvex_isCompact
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E]
    {k : Set E} (hk : IsCompact k) (hk' : Convex ℝ k) (hk'' : k.Nonempty)
    {f : k → k} (hf : Continuous f) :
    ∃ x, f x = x := by
  apply fixed_point_of_approximate_fixed_points hk f hf
  intro U hU_open hU_zero
  obtain ⟨V, ⟨hV_zero, hV_open, hV_convex⟩, hVU⟩ :=
    (LocallyConvexSpace.convex_open_basis_zero ℝ E).mem_iff.mp (hU_open.mem_nhds hU_zero)
  obtain ⟨z, hz⟩ := approximate_fixed_point_of_brouwer hk hk'
    hk'' f hf hV_open hV_zero hV_convex
  exact ⟨z, hVU hz⟩

/-- **Schauder's Fixed Point Theorem.** Every continuous self-map of a nonempty compact convex
subset of a Hausdorff locally convex topological vector space has a fixed point. -/
theorem ContinuousOn.exists_fixedPt_of_isConvex_isCompact
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E]
    {k : Set E} (hk : IsCompact k) (hk' : Convex ℝ k) (hk'' : k.Nonempty)
    {f : E → E} (hf : ContinuousOn f k) (hf' : Set.MapsTo f k k) :
    ∃ x ∈ k, f x = x := by
  have ⟨⟨x, hx⟩, hx'⟩ := (hf.mapsToRestrict hf').exists_fixedPt_of_isConvex_isCompact hk hk' hk''
  exact ⟨x, hx, Subtype.ext_iff.1 hx'⟩

end
