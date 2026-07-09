module

public import Auctionlib.Auction.Affiliation.Basic
public import Mathlib

/-! # Lemma 7.3 — Monotone conditional expectations (finite case)

This file proves the finite/discrete case of **Lemma 7.3 (Monotone conditional
expectations)** from Section 7: if the joint density `f` is affiliated
(**Def 7.2**) and `g` is a nondecreasing function of the signal profile, then
the conditional expectation `E[g(X) | Xᵢ = t]` is nondecreasing in `t`.

We work over a finite support `S : Finset (Fin n → ℝ)` closed under the
pointwise lattice operations (`IsSublattice`), with a density `f` positive
on `S`. The discrete conditional expectation `condExpSlice` is the
`f`-weighted average of `g` over the slice `{x ∈ S | x i = t}`.

The proof runs through the **four functions theorem (Ahlswede–Daykin
inequality)** (`four_functions_theorem` in Mathlib), applied on the
distributive lattice `Fin n → ℝ` to the pair of slices at heights `t ≤ t'`:
affiliation of `f` and monotonicity of `g` combine into exactly the
four-functions hypothesis, and sublattice closure pushes the resulting
sup/inf slices back into the original ones. This avoids the Holley/FOSD
route entirely.

The continuous case (affiliation ⇒ monotone likelihood ratio ⇒ first-order
stochastic dominance ⇒ monotone conditional expectations) is future work;
**Prop 7.4** (winner's curse), **Thm 7.5**, and **Thm 7.7** (linkage
principle) build on this lemma.
-/

@[expose] public section

open Finset
open scoped FinsetFamily

namespace Auction.Affiliation

/-- The discrete conditional expectation `E[g(X) | Xᵢ = t]` of `g` under the
(unnormalized) density `f` supported on `S`: the `f`-weighted average of `g`
over the slice `{x ∈ S | x i = t}`. When the slice is empty (or its `f`-mass
vanishes) the convention `division by zero = 0` applies; Lemma 7.3 only ever
evaluates it at heights `t` realized in `S`, where the mass is positive. -/
noncomputable def condExpSlice {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (S : Finset (Fin n → ℝ)) (i : Fin n) (t : ℝ) : ℝ :=
  (∑ x ∈ S.filter (fun x => x i = t), g x * f x) /
    (∑ x ∈ S.filter (fun x => x i = t), f x)

/-- The Ahlswede–Daykin step of **Lemma 7.3**. For an affiliated density `f`
positive on the sublattice `S` and a nondecreasing nonnegative `g`, and any
`A, B ⊆ S` with `A ⊔ B ⊆ B` and `A ⊓ B ⊆ A` (elementwise — in Lemma 7.3 these
are the slices at heights `t ≤ t'`), the cross-multiplied comparison of
`f`-weighted averages of `g` holds:

`(∑ x ∈ A, g x * f x) * (∑ x ∈ B, f x) ≤ (∑ x ∈ B, g x * f x) * (∑ x ∈ A, f x)`.

The proof applies the **four functions theorem** (`four_functions_theorem`)
with `f₁ = f₄ = g·f` and `f₂ = f₃ = f` (extended by `0` off `S`): its
hypothesis `f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b)` is exactly affiliation of
`f` combined with `g a ≤ g (a ⊔ b)`, and the resulting sums over `A ⊼ B` and
`A ⊻ B` are then enlarged to `A` and `B` using the closure hypotheses. -/
theorem sum_mul_sum_le_of_affiliated {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {S A B : Finset (Fin n → ℝ)}
    (hf : Affiliated f) (hpos : ∀ x ∈ S, 0 < f x)
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    (hg : Monotone g) (hg0 : ∀ x ∈ S, 0 ≤ g x)
    (hAS : A ⊆ S) (hBS : B ⊆ S)
    (hsupAB : ∀ a ∈ A, ∀ b ∈ B, a ⊔ b ∈ B)
    (hinfAB : ∀ a ∈ A, ∀ b ∈ B, a ⊓ b ∈ A) :
    (∑ x ∈ A, g x * f x) * (∑ x ∈ B, f x) ≤
      (∑ x ∈ B, g x * f x) * (∑ x ∈ A, f x) := by
  classical
  -- Extend `f` and `g·f` by `0` off `S`, so that nonnegativity and the
  -- four-functions hypothesis hold globally.
  set F : (Fin n → ℝ) → ℝ := fun x => if x ∈ S then f x else 0 with hF
  set GF : (Fin n → ℝ) → ℝ := fun x => if x ∈ S then g x * f x else 0 with hGF
  have hF0 : ∀ x, 0 ≤ F x := by
    intro x
    simp only [hF]
    split_ifs with hx
    · exact (hpos x hx).le
    · exact le_rfl
  have hGF0 : ∀ x, 0 ≤ GF x := by
    intro x
    simp only [hGF]
    split_ifs with hx
    · exact mul_nonneg (hg0 x hx) (hpos x hx).le
    · exact le_rfl
  -- The four-functions hypothesis: affiliation of `f` plus monotonicity of `g`.
  have hAD : ∀ a b : Fin n → ℝ, GF a * F b ≤ F (a ⊓ b) * GF (a ⊔ b) := by
    intro a b
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · have hsupS : a ⊔ b ∈ S :=
          mem_coe.1 (hsub.supClosed (mem_coe.2 ha) (mem_coe.2 hb))
        have hinfS : a ⊓ b ∈ S :=
          mem_coe.1 (hsub.infClosed (mem_coe.2 ha) (mem_coe.2 hb))
        simp only [hF, hGF, if_pos ha, if_pos hb, if_pos hsupS, if_pos hinfS]
        have h1 : g a ≤ g (a ⊔ b) := hg le_sup_left
        have h2 : f a * f b ≤ f (a ⊔ b) * f (a ⊓ b) := hf a b
        calc g a * f a * f b = g a * (f a * f b) := by ring
          _ ≤ g (a ⊔ b) * (f (a ⊔ b) * f (a ⊓ b)) :=
              mul_le_mul h1 h2 (mul_nonneg (hpos a ha).le (hpos b hb).le)
                (hg0 _ hsupS)
          _ = f (a ⊓ b) * (g (a ⊔ b) * f (a ⊔ b)) := by ring
      · have hb0 : F b = 0 := by simp only [hF]; exact if_neg hb
        rw [hb0, mul_zero]
        exact mul_nonneg (hF0 _) (hGF0 _)
    · have ha0 : GF a = 0 := by simp only [hGF]; exact if_neg ha
      rw [ha0, zero_mul]
      exact mul_nonneg (hF0 _) (hGF0 _)
  -- Ahlswede–Daykin on the slices.
  have had := four_functions_theorem GF F F GF
    (Pi.le_def.mpr hGF0) (Pi.le_def.mpr hF0) (Pi.le_def.mpr hF0)
    (Pi.le_def.mpr hGF0) hAD A B
  -- Sublattice closure pushes the sup/inf slices back into `B` and `A`.
  have hABinf : A ⊼ B ⊆ A := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_infs.1 hz
    exact hinfAB a ha b hb
  have hABsup : A ⊻ B ⊆ B := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sups.1 hz
    exact hsupAB a ha b hb
  have h5 : ∑ x ∈ A ⊼ B, F x ≤ ∑ x ∈ A, F x :=
    sum_le_sum_of_subset_of_nonneg hABinf fun x _ _ => hF0 x
  have h6 : ∑ x ∈ A ⊻ B, GF x ≤ ∑ x ∈ B, GF x :=
    sum_le_sum_of_subset_of_nonneg hABsup fun x _ _ => hGF0 x
  -- On subsets of `S` the extensions agree with the originals.
  have eAGF : ∑ x ∈ A, GF x = ∑ x ∈ A, g x * f x :=
    sum_congr rfl fun x hx => by simp only [hGF]; exact if_pos (hAS hx)
  have eBF : ∑ x ∈ B, F x = ∑ x ∈ B, f x :=
    sum_congr rfl fun x hx => by simp only [hF]; exact if_pos (hBS hx)
  have eAF : ∑ x ∈ A, F x = ∑ x ∈ A, f x :=
    sum_congr rfl fun x hx => by simp only [hF]; exact if_pos (hAS hx)
  have eBGF : ∑ x ∈ B, GF x = ∑ x ∈ B, g x * f x :=
    sum_congr rfl fun x hx => by simp only [hGF]; exact if_pos (hBS hx)
  calc (∑ x ∈ A, g x * f x) * ∑ x ∈ B, f x
      = (∑ x ∈ A, GF x) * ∑ x ∈ B, F x := by rw [eAGF, eBF]
    _ ≤ (∑ x ∈ A ⊼ B, F x) * ∑ x ∈ A ⊻ B, GF x := had
    _ ≤ (∑ x ∈ A, F x) * ∑ x ∈ B, GF x :=
        mul_le_mul h5 h6 (sum_nonneg fun x _ => hGF0 x)
          (sum_nonneg fun x _ => hF0 x)
    _ = (∑ x ∈ B, g x * f x) * ∑ x ∈ A, f x := by rw [eAF, eBGF, mul_comm]

/-- **Lemma 7.3, nonnegative case**. For an affiliated density `f` positive on
the sublattice `S` and a nondecreasing *nonnegative* `g`, the discrete
conditional expectation `t ↦ E[g(X) | Xᵢ = t]` is nondecreasing on the set of
realized heights `{x i | x ∈ S}`. The general case
(`monotoneOn_condExpSlice_of_affiliated`) reduces to this one by shifting `g`
by a constant. -/
theorem monotoneOn_condExpSlice_of_affiliated_of_nonneg {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {S : Finset (Fin n → ℝ)}
    (hf : Affiliated f) (hpos : ∀ x ∈ S, 0 < f x)
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    (hg : Monotone g) (hg0 : ∀ x ∈ S, 0 ≤ g x) (i : Fin n) :
    MonotoneOn (condExpSlice f g S i) ↑(S.image fun x => x i) := by
  intro t ht t' ht' htt'
  rw [mem_coe, mem_image] at ht ht'
  obtain ⟨a₀, ha₀S, ha₀⟩ := ht
  obtain ⟨b₀, hb₀S, hb₀⟩ := ht'
  have hApos : 0 < ∑ x ∈ S.filter (fun x => x i = t), f x :=
    sum_pos (fun x hx => hpos x (mem_filter.1 hx).1)
      ⟨a₀, mem_filter.2 ⟨ha₀S, ha₀⟩⟩
  have hBpos : 0 < ∑ x ∈ S.filter (fun x => x i = t'), f x :=
    sum_pos (fun x hx => hpos x (mem_filter.1 hx).1)
      ⟨b₀, mem_filter.2 ⟨hb₀S, hb₀⟩⟩
  -- The slice at height `t` sups into the slice at height `t'`, and infs back.
  have hsupAB : ∀ a ∈ S.filter (fun x => x i = t),
      ∀ b ∈ S.filter (fun x => x i = t'), a ⊔ b ∈ S.filter (fun x => x i = t') := by
    intro a ha b hb
    obtain ⟨haS, hai⟩ := mem_filter.1 ha
    obtain ⟨hbS, hbi⟩ := mem_filter.1 hb
    refine mem_filter.2 ⟨mem_coe.1 (hsub.supClosed (mem_coe.2 haS) (mem_coe.2 hbS)), ?_⟩
    rw [Pi.sup_apply, hai, hbi]
    exact sup_eq_right.2 htt'
  have hinfAB : ∀ a ∈ S.filter (fun x => x i = t),
      ∀ b ∈ S.filter (fun x => x i = t'), a ⊓ b ∈ S.filter (fun x => x i = t) := by
    intro a ha b hb
    obtain ⟨haS, hai⟩ := mem_filter.1 ha
    obtain ⟨hbS, hbi⟩ := mem_filter.1 hb
    refine mem_filter.2 ⟨mem_coe.1 (hsub.infClosed (mem_coe.2 haS) (mem_coe.2 hbS)), ?_⟩
    rw [Pi.inf_apply, hai, hbi]
    exact inf_eq_left.2 htt'
  simp only [condExpSlice]
  rw [div_le_div_iff₀ hApos hBpos]
  exact sum_mul_sum_le_of_affiliated hf hpos hsub hg hg0
    (filter_subset _ _) (filter_subset _ _) hsupAB hinfAB

/-- **Lemma 7.3 (Monotone conditional expectations), finite case**. Let the
joint density `f` be affiliated (**Def 7.2**) and positive on the finite
sublattice `S` of signal profiles, and let `g` be nondecreasing. Then the
discrete conditional expectation `t ↦ E[g(X) | Xᵢ = t]` (`condExpSlice`) is
nondecreasing on the set of realized heights `{x i | x ∈ S}`.

The proof reduces to the nonnegative case
(`monotoneOn_condExpSlice_of_affiliated_of_nonneg`, via Ahlswede–Daykin) by
shifting `g` by the constant `c = -g m`, where `m` attains the minimum of `g`
on `S`: the shift keeps `g` nondecreasing, makes it nonnegative on `S`, and
translates every conditional expectation by exactly `c`. -/
theorem monotoneOn_condExpSlice_of_affiliated {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {S : Finset (Fin n → ℝ)}
    (hf : Affiliated f) (hpos : ∀ x ∈ S, 0 < f x)
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    (hg : Monotone g) (i : Fin n) :
    MonotoneOn (condExpSlice f g S i) ↑(S.image fun x => x i) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · intro t ht
    simp at ht
  obtain ⟨m, hmS, hm⟩ := S.exists_min_image g hS
  set c : ℝ := -g m with hc
  have hg0' : ∀ x ∈ S, 0 ≤ g x + c := by
    intro x hx
    have := hm x hx
    simp only [hc]
    linarith
  have hmono' : Monotone fun x => g x + c := hg.add_const c
  -- Shifting `g` by a constant shifts every conditional expectation by it.
  have key : ∀ t ∈ S.image fun x => x i,
      condExpSlice f (fun x => g x + c) S i t = condExpSlice f g S i t + c := by
    intro t ht
    rw [mem_image] at ht
    obtain ⟨a₀, ha₀S, ha₀⟩ := ht
    have hD : 0 < ∑ x ∈ S.filter (fun x => x i = t), f x :=
      sum_pos (fun x hx => hpos x (mem_filter.1 hx).1)
        ⟨a₀, mem_filter.2 ⟨ha₀S, ha₀⟩⟩
    simp only [condExpSlice]
    rw [show (∑ x ∈ S.filter (fun x => x i = t), (g x + c) * f x)
          = (∑ x ∈ S.filter (fun x => x i = t), g x * f x)
            + c * ∑ x ∈ S.filter (fun x => x i = t), f x by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun x _ => by ring]
    rw [add_div, mul_div_assoc, div_self hD.ne', mul_one]
  intro t ht t' ht' htt'
  have h := monotoneOn_condExpSlice_of_affiliated_of_nonneg hf hpos hsub
    hmono' hg0' i ht ht' htt'
  rw [mem_coe] at ht ht'
  rw [key t ht, key t' ht'] at h
  linarith

end Auction.Affiliation
