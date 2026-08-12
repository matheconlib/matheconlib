module

public import Auctionlib.Auction.Affiliation.FiniteCondExp

/-! # Lemma 7.3 — Monotone conditional expectations (finite case)

This file proves the finite/discrete case of **Lemma 7.3 (Monotone conditional
expectations)** from Section 7: if the joint density `f` is affiliated
(**Def 7.2**) and `g` is a nondecreasing function of the signal profile, then
the conditional expectation `E[g(X) | Xᵢ = t]` is nondecreasing in `t`.

We work over a finite support `S : Finset (Fin n → ℝ)` closed under the
pointwise lattice operations (`IsSublattice`), with a density `f` positive
on `S`. The discrete conditional expectation `condExpSlice` is the
`f`-weighted average of `g` over the slice `{x ∈ S | x i = t}`.

The reusable conditional-expectation comparison is proved in
`FiniteCondExp.lean`.  Its proof uses the **four functions theorem
(Ahlswede–Daykin inequality)** on the distributive lattice `Fin n → ℝ`.
This file verifies that the slices at heights `t ≤ t'` satisfy the required
supremum and infimum conditions, then applies that comparison directly.
`WinnersCurse.lean` uses the same finite comparison for Proposition 7.4.
This approach avoids the Holley/FOSD route entirely.

The continuous case (affiliation ⇒ monotone likelihood ratio ⇒ first-order
stochastic dominance ⇒ monotone conditional expectations) is future work;
**Prop 7.4** (winner's curse), **Thm 7.5**, and **Thm 7.7** (linkage
principle) build on this lemma.
-/

@[expose] public section

open Finset

namespace Auction.Affiliation

/-- The discrete conditional expectation `E[g(X) | Xᵢ = t]` of `g` under the
(unnormalized) density `f` supported on `S`: the `f`-weighted average of `g`
over the slice `{x ∈ S | x i = t}`. When the slice is empty (or its `f`-mass
vanishes) the convention `division by zero = 0` applies; Lemma 7.3 only ever
evaluates it at heights `t` realized in `S`, where the mass is positive. -/
noncomputable def condExpSlice {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (S : Finset (Fin n → ℝ)) (i : Fin n) (t : ℝ) : ℝ :=
  condExpOn f g (S.filter fun x => x i = t)

/-- **Lemma 7.3 (Monotone conditional expectations), finite case**. Let the
joint density `f` be affiliated (**Def 7.2**) and positive on the finite
sublattice `S` of signal profiles, and let `g` be nondecreasing.  Then the
discrete conditional expectation `t ↦ E[g(X) | Xᵢ = t]` (`condExpSlice`) is
nondecreasing on the set of realized heights `{x i | x ∈ S}`.

For realized heights `t ≤ t'`, let `A` and `B` be the corresponding slices of
`S`.  Both slices are nonempty.  Moreover, the pointwise infimum of a profile
in `A` with a profile in `B` returns to `A`, while their pointwise supremum
returns to `B`.  The result is therefore a direct application of
`condExpOn_le_condExpOn_of_affiliated`. -/
theorem monotoneOn_condExpSlice_of_affiliated {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {S : Finset (Fin n → ℝ)}
    (hf : Affiliated f) (hpos : ∀ x ∈ S, 0 < f x)
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    (hg : Monotone g) (i : Fin n) :
    MonotoneOn (condExpSlice f g S i) ↑(S.image fun x => x i) := by
  intro t ht t' ht' htt'

  -- Since `t` and `t'` are realized heights, choose one profile from each
  -- corresponding slice.
  rw [mem_coe, mem_image] at ht
  rw [mem_coe, mem_image] at ht'
  obtain ⟨x, hxS, hxi⟩ := ht
  obtain ⟨y, hyS, hyi⟩ := ht'

  have hA_nonempty : (S.filter fun z => z i = t).Nonempty :=
    ⟨x, mem_filter.2 ⟨hxS, hxi⟩⟩
  have hB_nonempty : (S.filter fun z => z i = t').Nonempty :=
    ⟨y, mem_filter.2 ⟨hyS, hyi⟩⟩

  -- Each slice is a subset of the original finite support `S`.
  have hA_subset : S.filter (fun z => z i = t) ⊆ S :=
    filter_subset _ _
  have hB_subset : S.filter (fun z => z i = t') ⊆ S :=
    filter_subset _ _

  -- The supremum of a profile at height `t` and a profile at height `t'`
  -- has height `t'`, because `t ≤ t'`.
  have hsupAB : ∀ a ∈ S.filter (fun z => z i = t),
      ∀ b ∈ S.filter (fun z => z i = t'),
        a ⊔ b ∈ S.filter (fun z => z i = t') := by
    intro a ha b hb
    obtain ⟨haS, hai⟩ := mem_filter.1 ha
    obtain ⟨hbS, hbi⟩ := mem_filter.1 hb
    have hsupS : a ⊔ b ∈ S :=
      mem_coe.1 (hsub.supClosed (mem_coe.2 haS) (mem_coe.2 hbS))
    refine mem_filter.2 ⟨hsupS, ?_⟩
    rw [Pi.sup_apply, hai, hbi]
    exact sup_eq_right.2 htt'

  -- Dually, the infimum of the same two profiles has height `t`.
  have hinfAB : ∀ a ∈ S.filter (fun z => z i = t),
      ∀ b ∈ S.filter (fun z => z i = t'),
        a ⊓ b ∈ S.filter (fun z => z i = t) := by
    intro a ha b hb
    obtain ⟨haS, hai⟩ := mem_filter.1 ha
    obtain ⟨hbS, hbi⟩ := mem_filter.1 hb
    have hinfS : a ⊓ b ∈ S :=
      mem_coe.1 (hsub.infClosed (mem_coe.2 haS) (mem_coe.2 hbS))
    refine mem_filter.2 ⟨hinfS, ?_⟩
    rw [Pi.inf_apply, hai, hbi]
    exact inf_eq_left.2 htt'

  -- The generic finite comparison now applies to the two slices.
  change
    condExpOn f g (S.filter fun z => z i = t) ≤
      condExpOn f g (S.filter fun z => z i = t')
  exact condExpOn_le_condExpOn_of_affiliated
    hf hpos hsub hg
    hA_subset hB_subset hA_nonempty hB_nonempty hsupAB hinfAB

set_option linter.unusedVariables false in
/-- **Lemma 7.3, nonnegative case**.  This is the specialization of
`monotoneOn_condExpSlice_of_affiliated` to a function `g` known to be
nonnegative on `S`.

The stronger theorem does not require the nonnegativity assumption, so this
statement is now an immediate corollary.  Its existing public name and
signature are retained for callers that naturally carry the stronger
hypotheses. -/
theorem monotoneOn_condExpSlice_of_affiliated_of_nonneg {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {S : Finset (Fin n → ℝ)}
    (hf : Affiliated f) (hpos : ∀ x ∈ S, 0 < f x)
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    (hg : Monotone g) (hg0 : ∀ x ∈ S, 0 ≤ g x) (i : Fin n) :
    MonotoneOn (condExpSlice f g S i) ↑(S.image fun x => x i) := by
  exact monotoneOn_condExpSlice_of_affiliated hf hpos hsub hg i

end Auction.Affiliation
