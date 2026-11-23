/-
Copyright (c) 2026 Ayan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayan
-/
module

public import MathEconLib.Matching.Classical.Marriage.DeferredAcceptanceComputable

/-!
# The blocking lemma and weak Pareto optimality of the man-optimal stable matching

Let `ν` be a partial matching of a finite classical marriage market that is individually rational
for the women, and suppose some man strictly prefers `ν` to the man-optimal stable matching. The
blocking lemma says that `ν` is blocked by a pair `(m, w)` in which `m` does not strictly prefer
`ν` and `w` is the partner under `ν` of a man who does. In particular `ν` cannot make every man
strictly better off, which is weak Pareto optimality. The alternative `ν` need not be stable, so
optimality among stable matchings does not imply either result.

## Main statements

* `MarriageMarket.IsManOptimal.exists_isBlockingPair_of_ltM`: the blocking lemma for any
  man-optimal stable matching.
* `MarriageMarket.exists_isBlockingPair_of_ltM_galeShapley`: the blocking lemma for man-proposing
  deferred acceptance.
* `MarriageMarket.IsManOptimal.not_forall_ltM`: weak Pareto optimality for any man-optimal stable
  matching.
* `MarriageMarket.not_forall_ltM_galeShapley`: weak Pareto optimality for man-proposing deferred
  acceptance.
* `MarriageMarket.not_forall_ltM_galeShapleyComputable`: weak Pareto optimality for the executable
  algorithm.

## Hypotheses

Only the women's half of individual rationality is assumed. A man who strictly gains over a
stable matching is matched to a woman he finds acceptable, and the men who do not gain play no
role beyond supplying the blocking man, so the men's half is never needed. An individually
rational alternative `hν : mkt.IndividuallyRational ν` supplies the hypothesis as `hν.2`. The
women's half cannot be dropped from either result, weak Pareto optimality needs a nonempty set of
men, its conclusion cannot be strengthened to full Pareto efficiency, and it does not hold for an
arbitrary stable matching in place of the man-optimal one. These limits are checked in
`MathEconLibExamples.Matching.BlockingLemma`.

## Proof

The proof runs at the terminal round of deferred acceptance. Every man who gains is matched by
`ν` to a woman who has rejected him there, and because he is acceptable to her she holds a man
she strictly prefers. If one of these held men does not gain, he and the woman holding him block
`ν`. Otherwise the held men are exactly the gaining men. Consider the last round in which a
gaining man is rejected. He then proposes to the woman who finally holds him. She had already
rejected her partner under `ν`, so she was holding some other man, whom she rejects later. That
man is rejected after the last rejection of a gaining man, so he does not gain, and he blocks `ν`
with her.

## References

The formulation of the blocking lemma is credited to J. S. Hwang by David Gale and Marilda Sotomayor
(1985), *Some remarks on the stable matching problem*, *Discrete Applied Mathematics* **11**(3),
223–232, Section 6, Key Lemma, pp. 230–231; the algorithmic proof is in the appendix, pp. 231–232.
[DOI: 10.1016/0166-218X(85)90074-5](https://doi.org/10.1016/0166-218X(85)90074-5). It is
Lemma 3.5 in Alvin E. Roth and Marilda A. Oliveira Sotomayor (1990), *Two-Sided Matching: A Study
in Game-Theoretic Modeling and Analysis*, Cambridge University Press,
[Chapter 3](https://doi.org/10.1017/CCOL052139015X.003). Weak Pareto optimality is Theorem 3 of
Gale and Sotomayor (1985), p. 230, with an algorithmic proof on p. 231. This formalization uses
only women's individual rationality for the comparison matching, rather than two-sided
individual rationality, and makes nonemptiness of the men explicit for weak Pareto optimality.
This module covers the classical one-to-one case only.
-/

@[expose] public section

namespace MathEconLib.Matching

open Function

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v} [Fintype M] [Fintype W] (mkt : MarriageMarket M W)

omit [Fintype M] in
/-- A woman a man strictly prefers to his best unrejected option has already rejected him. -/
private theorem gs_rejected_of_lt_bestM {R : Set (M × W)} {m : M} {w : W}
    (h : mkt.ltM m (mkt.bestM m Rᶜ) (some w)) : (m, w) ∈ R := by
  by_contra hn
  have hle : mkt.leM m (some w) (mkt.bestM m Rᶜ) :=
    mkt.le_bestM_of_mem (mkt.some_mem_menuM.mpr hn)
  let := mkt.prefM m
  exact not_lt_of_ge hle h

/-- A pair rejected by the end of a round ranks strictly below what the woman held in it. -/
private theorem gs_lt_bestW_of_mem_gsStep (k : ℕ) {m : M} {w : W}
    (h : (m, w) ∈ mkt.gsStep (mkt.gsRejected k)) :
    mkt.ltW w (some m) (mkt.bestW w (mkt.gsProposals (mkt.gsRejected k))) := by
  let := mkt.prefW w
  rcases h with hR | ⟨hp, hnh⟩
  · exact mkt.gs_rejected_below_holding k hR
  · have hle : some m ≤ mkt.bestW w (mkt.gsProposals (mkt.gsRejected k)) :=
      mkt.le_bestW_of_mem (mkt.some_mem_menuW.mpr hp)
    exact lt_of_le_of_ne hle (fun heq => hnh ⟨hp, heq⟩)

private theorem gsRejected_mono : Monotone mkt.gsRejected :=
  monotone_nat_of_le_succ fun n => by
    rw [mkt.gsRejected_succ]
    exact mkt.gs_subset_step _

/-- A pair rejected by round `n` but not by round `i` was first rejected in a round between. -/
private theorem gs_exists_round_of_mem_of_not_mem {p : M × W} {i : ℕ} :
    ∀ n, p ∈ mkt.gsRejected n → p ∉ mkt.gsRejected i →
      ∃ j, i ≤ j ∧ j < n ∧ p ∈ mkt.gsRejected (j + 1) ∧ p ∉ mkt.gsRejected j
  | 0, hp, _ => False.elim hp
  | n + 1, hp, hi => by
      by_cases hn : p ∈ mkt.gsRejected n
      · obtain ⟨j, hij, hjn, hj⟩ := gs_exists_round_of_mem_of_not_mem n hn hi
        exact ⟨j, hij, Nat.lt_succ_of_lt hjn, hj⟩
      · refine ⟨n, ?_, Nat.lt_succ_self n, hp, hn⟩
        by_contra hlt
        exact hi (gsRejected_mono mkt (Nat.succ_le_of_lt (Nat.lt_of_not_le hlt)) hp)

/-- Rejections after a terminal round add nothing. -/
private theorem gsRejected_subset_of_terminal {n : ℕ}
    (hn : IsFixedPt mkt.gsStep (mkt.gsRejected n)) (k : ℕ) :
    mkt.gsRejected k ⊆ mkt.gsRejected n := by
  have hfix : ∀ i, mkt.gsRejected (n + i) = mkt.gsRejected n := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [← Nat.add_assoc, mkt.gsRejected_succ, ih]; exact hn
  rcases Nat.le_total k n with hle | hle
  · exact gsRejected_mono mkt hle
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact (hfix i).subset

/-- A man who strictly prefers `ν` to his best unrejected option is matched by `ν` to a woman who
has rejected him, who finds him acceptable, and who holds a man she strictly prefers. -/
private theorem gs_exists_bestW_eq_some_of_ltM (n : ℕ) {ν : M ≃. W}
    (hν : mkt.IndividuallyRationalW ν) {m : M}
    (hm : mkt.ltM m (mkt.bestM m (mkt.gsRejected n)ᶜ) (ν m)) :
    ∃ w h, ν m = some w ∧ (m, w) ∈ mkt.gsRejected n ∧ mkt.leW w none (some m) ∧
      mkt.bestW w (mkt.gsProposals (mkt.gsRejected n)) = some h ∧
      mkt.ltW w (some m) (some h) := by
  cases hνm : ν m with
  | none =>
      rw [hνm] at hm
      let := mkt.prefM m
      exact absurd hm (not_lt_of_ge (mkt.none_le_bestM m _))
  | some w =>
      have hrej : (m, w) ∈ mkt.gsRejected n := by
        apply gs_rejected_of_lt_bestM mkt
        rw [← hνm]
        exact hm
      have hacc : mkt.leW w none (some m) := by
        have h : mkt.IndividuallyRationalForW ν w := hν w
        rwa [MarriageMarket.IndividuallyRationalForW, ν.eq_some_iff.mpr hνm] at h
      have hlt := mkt.gs_rejected_below_holding n hrej
      cases hb : mkt.bestW w (mkt.gsProposals (mkt.gsRejected n)) with
      | none =>
          rw [hb] at hlt
          let := mkt.prefW w
          exact absurd hlt (not_lt_of_ge hacc)
      | some h =>
          rw [hb] at hlt
          exact ⟨w, h, rfl, hrej, hacc, hb, hlt⟩

/-- The blocking lemma at any reached terminal round. -/
private theorem gs_exists_isBlockingPair_of_terminal (n : ℕ)
    (hn : IsFixedPt mkt.gsStep (mkt.gsRejected n)) {ν : M ≃. W}
    (hν : mkt.IndividuallyRationalW ν) {m₀ : M}
    (h₀ : mkt.ltM m₀ (mkt.bestM m₀ (mkt.gsRejected n)ᶜ) (ν m₀)) :
    ∃ m w, ¬ mkt.ltM m (mkt.bestM m (mkt.gsRejected n)ᶜ) (ν m) ∧
      (∃ m', mkt.ltM m' (mkt.bestM m' (mkt.gsRejected n)ᶜ) (ν m') ∧ ν m' = some w) ∧
      mkt.IsBlockingPair ν m w := by
  classical
  -- The men who strictly gain. Each is matched by `ν` to a woman who rejected him and who holds
  -- a man she strictly prefers at the terminal round.
  let S : Set M := {m | mkt.ltM m (mkt.bestM m (mkt.gsRejected n)ᶜ) (ν m)}
  have key := fun m (hm : m ∈ S) => gs_exists_bestW_eq_some_of_ltM mkt n hν hm
  obtain ⟨w₀, -, hw₀, -⟩ := key m₀ h₀
  have : Nonempty W := ⟨w₀⟩
  have : Nonempty M := ⟨m₀⟩
  choose! g f hkey using key
  have hprop : ∀ m ∈ S, some (g m) = mkt.bestM (f m) (mkt.gsRejected n)ᶜ :=
    fun m hm => mkt.gs_bestW_mem (hkey m hm).2.2.2.1
  have hsymm : ∀ m ∈ S, ν.symm (g m) = some m := fun m hm => ν.eq_some_iff.mpr (hkey m hm).1
  by_cases hc : ∃ m ∈ S, f m ∉ S
  · -- Some woman matched by `ν` to a gaining man holds a man who does not gain.
    obtain ⟨m, hm, hfm⟩ := hc
    refine ⟨f m, g m, hfm, ⟨m, hm, (hkey m hm).1⟩, ?_, ?_⟩
    · let := mkt.prefM (f m)
      have hle : ν (f m) ≤ some (g m) := by
        rw [hprop m hm]
        exact not_lt.mp hfm
      refine lt_of_le_of_ne hle fun heq => ?_
      have hmm : m = f m := mkt.graphOf_leftUnique ν (mkt.mem_graphOf.mpr (hkey m hm).1)
        (mkt.mem_graphOf.mpr heq)
      have hlt := (hkey m hm).2.2.2.2
      rw [← hmm] at hlt
      let := mkt.prefW (g m)
      exact lt_irrefl _ hlt
    · change mkt.ltW (g m) (ν.symm (g m)) (some (f m))
      rw [hsymm m hm]
      exact (hkey m hm).2.2.2.2
  -- Otherwise the held men are exactly the gaining men.
  push Not at hc
  have hsurj : ∀ m' ∈ S, ∃ m ∈ S, f m = m' := by
    let f' : S → S := fun x => ⟨f x, hc x x.2⟩
    have hinj : Injective f' := by
      intro a b hab
      have hfab : f a = f b := congrArg Subtype.val hab
      have hgab : g a = g b :=
        Option.some.inj (by rw [hprop a a.2, hprop b b.2, hfab])
      have hνb : ν b = some (g a) := by rw [hgab]; exact (hkey b b.2).1
      exact Subtype.ext (mkt.graphOf_leftUnique ν (mkt.mem_graphOf.mpr (hkey a a.2).1)
        (mkt.mem_graphOf.mpr hνb))
    intro m' hm'
    obtain ⟨a, ha⟩ := Finite.injective_iff_surjective.mp hinj ⟨m', hm'⟩
    exact ⟨a, a.2, congrArg Subtype.val ha⟩
  -- The last round in which a gaining man is rejected.
  let P : ℕ → Prop := fun j =>
    ∃ p, p ∈ mkt.gsRejected (j + 1) ∧ p ∉ mkt.gsRejected j ∧ p.1 ∈ S
  obtain ⟨j₀, -, hj₀n, hj₀⟩ := gs_exists_round_of_mem_of_not_mem mkt (i := 0) n
    (hkey m₀ h₀).2.1 (fun h => h)
  have hPk : P (Nat.findGreatest P n) :=
    Nat.findGreatest_spec (P := P) hj₀n.le ⟨_, hj₀.1, hj₀.2, h₀⟩
  have hmax : ∀ j, Nat.findGreatest P n < j → j ≤ n → ¬ P j :=
    fun j hkj hjn => Nat.findGreatest_is_greatest hkj hjn
  generalize Nat.findGreatest P n = k at hPk hmax
  have hlate : ∀ m w, m ∈ S → (m, w) ∈ mkt.gsRejected n → (m, w) ∈ mkt.gsRejected (k + 1) := by
    intro m w hm hmw
    by_contra hnot
    obtain ⟨j, hkj, hjn, hj⟩ := gs_exists_round_of_mem_of_not_mem mkt n hmw hnot
    exact hmax j hkj hjn.le ⟨_, hj.1, hj.2, hm⟩
  obtain ⟨⟨ms, ws⟩, hmem, hnot, hms⟩ := hPk
  have hmsR : (ms, ws) ∈ mkt.gsRejected (k + 1) := hmem
  rw [mkt.gsRejected_succ] at hmem
  rcases hmem with hR | ⟨hp, -⟩
  · exact absurd hR hnot
  obtain ⟨m, hm, rfl⟩ := hsurj ms hms
  obtain ⟨hνm, hrej, hacc, hbest, -⟩ := hkey m hm
  have hsub : (mkt.gsRejected n)ᶜ ⊆ (mkt.gsRejected (k + 1))ᶜ :=
    Set.compl_subset_compl.mpr (gsRejected_subset_of_terminal mkt hn (k + 1))
  -- After his last rejection the man `f m` proposes to the woman `g m` who finally holds him.
  have hnext : (f m, g m) ∈ mkt.gsProposals (mkt.gsRejected (k + 1)) := by
    let := mkt.prefM (f m)
    change some (g m) = mkt.bestM (f m) (mkt.gsRejected (k + 1))ᶜ
    apply le_antisymm
    · rw [hprop m hm]
      exact mkt.bestM_mono hsub
    · rw [hprop m hm]
      cases hb : mkt.bestM (f m) (mkt.gsRejected (k + 1))ᶜ with
      | none => exact mkt.none_le_bestM (f m) _
      | some w'' =>
          have hmenu := mkt.bestM_mem_menuM (f m) (mkt.gsRejected (k + 1))ᶜ
          rw [hb] at hmenu
          have hnk : (f m, w'') ∉ mkt.gsRejected (k + 1) := mkt.some_mem_menuM.mp hmenu
          exact mkt.le_bestM_of_mem
            (mkt.some_mem_menuM.mpr fun hR => hnk (hlate (f m) w'' hms hR))
  have hne : g m ≠ ws := by
    intro heq
    rw [← heq] at hmsR
    exact mkt.gs_proposal_not_rejected hnext hmsR
  -- The woman `g m` rejected `m` by then, so she held a man `h` in round `k`.
  have hmk : (m, g m) ∈ mkt.gsStep (mkt.gsRejected k) := by
    rw [← mkt.gsRejected_succ]
    exact hlate m (g m) hm hrej
  have hlt := gs_lt_bestW_of_mem_gsStep mkt k hmk
  cases hb : mkt.bestW (g m) (mkt.gsProposals (mkt.gsRejected k)) with
  | none =>
      rw [hb] at hlt
      let := mkt.prefW (g m)
      exact absurd hlt (not_lt_of_ge hacc)
  | some h =>
      rw [hb] at hlt
      have hheld : (h, g m) ∈ mkt.gsHeld (mkt.gsRejected k) := ⟨mkt.gs_bestW_mem hb, hb.symm⟩
      have hhnext : (h, g m) ∈ mkt.gsProposals (mkt.gsRejected (k + 1)) := by
        rw [mkt.gsRejected_succ]
        exact mkt.gs_held_proposes_next hheld
      have hhne : h ≠ f m := by
        intro heq
        have h1 : some (g m) = mkt.bestM h (mkt.gsRejected k)ᶜ := hheld.1
        have h2 : some ws = mkt.bestM (f m) (mkt.gsRejected k)ᶜ := hp
        rw [heq] at h1
        exact hne (Option.some.inj (h1.trans h2.symm))
      have hhk : some (g m) = mkt.bestM h (mkt.gsRejected (k + 1))ᶜ := hhnext
      -- She finally holds `f m`, so she rejects `h` later, and `h` does not gain.
      have hhR : (h, g m) ∈ mkt.gsRejected n := by
        by_contra hnR
        let := mkt.prefM h
        have hle : some (g m) ≤ mkt.bestM h (mkt.gsRejected n)ᶜ :=
          mkt.le_bestM_of_mem (mkt.some_mem_menuM.mpr hnR)
        have hge : mkt.bestM h (mkt.gsRejected n)ᶜ ≤ some (g m) := by
          rw [hhk]
          exact mkt.bestM_mono hsub
        have hpn : (h, g m) ∈ mkt.gsProposals (mkt.gsRejected n) := le_antisymm hle hge
        have h1 : some h = mkt.bestW (g m) (mkt.gsProposals (mkt.gsRejected n)) :=
          (mkt.gs_held_of_terminal hn hpn).2
        exact hhne (Option.some.inj (h1.trans hbest))
      have hhS : h ∉ S := fun hS =>
        mkt.gs_proposal_not_rejected hhnext (hlate h (g m) hS hhR)
      refine ⟨h, g m, hhS, ⟨m, hm, hνm⟩, ?_, ?_⟩
      · let := mkt.prefM h
        have hle : ν h ≤ mkt.bestM h (mkt.gsRejected n)ᶜ := not_lt.mp hhS
        have hlt' : mkt.bestM h (mkt.gsRejected n)ᶜ < some (g m) := by
          refine lt_of_le_of_ne (by rw [hhk]; exact mkt.bestM_mono hsub) fun heq => ?_
          exact mkt.gs_proposal_not_rejected (R := mkt.gsRejected n) heq.symm hhR
        exact lt_of_le_of_lt hle hlt'
      · change mkt.ltW (g m) (ν.symm (g m)) (some h)
        rw [hsymm m hm]
        exact hlt

/-- **Blocking lemma.** If some man strictly prefers a matching `ν` that is individually rational
for the women to man-proposing deferred acceptance, then `ν` is blocked by a man who does not
strictly prefer it together with a woman whom `ν` matches to a man who does. -/
theorem exists_isBlockingPair_of_ltM_galeShapley {ν : M ≃. W}
    (hν : mkt.IndividuallyRationalW ν) {m₀ : M} (h₀ : mkt.ltM m₀ (mkt.galeShapley m₀) (ν m₀)) :
    ∃ m w, ¬ mkt.ltM m (mkt.galeShapley m) (ν m) ∧
      (∃ m', mkt.ltM m' (mkt.galeShapley m') (ν m') ∧ ν m' = some w) ∧
      mkt.IsBlockingPair ν m w :=
  gs_exists_isBlockingPair_of_terminal mkt mkt.galeShapleyRoundBound
    mkt.galeShapleyRoundBound_terminal hν h₀

omit [Fintype M] [Fintype W] in
/-- **Blocking lemma** for any man-optimal stable matching. -/
theorem IsManOptimal.exists_isBlockingPair_of_ltM [Finite M] [Finite W] {μ ν : M ≃. W}
    (hμ : mkt.IsManOptimal μ) (hν : mkt.IndividuallyRationalW ν) {m₀ : M}
    (h₀ : mkt.ltM m₀ (μ m₀) (ν m₀)) :
    ∃ m w, ¬ mkt.ltM m (μ m) (ν m) ∧ (∃ m', mkt.ltM m' (μ m') (ν m') ∧ ν m' = some w) ∧
      mkt.IsBlockingPair ν m w := by
  have := Fintype.ofFinite M
  have := Fintype.ofFinite W
  rw [IsManOptimal.unique mkt hμ mkt.isManOptimal_galeShapley] at h₀ ⊢
  exact mkt.exists_isBlockingPair_of_ltM_galeShapley hν h₀

/-- No partial matching that is individually rational for the women, stable or not, makes every
man strictly better off than man-proposing deferred acceptance. -/
theorem not_forall_ltM_galeShapley [Nonempty M] {ν : M ≃. W}
    (hν : mkt.IndividuallyRationalW ν) : ¬ ∀ m, mkt.ltM m (mkt.galeShapley m) (ν m) := by
  intro hgain
  obtain ⟨m₀⟩ := ‹Nonempty M›
  obtain ⟨m, -, hm, -⟩ := mkt.exists_isBlockingPair_of_ltM_galeShapley hν (hgain m₀)
  exact hm (hgain m)

omit [Fintype M] [Fintype W] in
/-- **Weak Pareto optimality.** No partial matching that is individually rational for the women,
stable or not, makes every man strictly better off than the man-optimal stable matching. -/
theorem IsManOptimal.not_forall_ltM [Finite M] [Finite W] [Nonempty M] {μ ν : M ≃. W}
    (hμ : mkt.IsManOptimal μ) (hν : mkt.IndividuallyRationalW ν) :
    ¬ ∀ m, mkt.ltM m (μ m) (ν m) := by
  have := Fintype.ofFinite M
  have := Fintype.ofFinite W
  rw [IsManOptimal.unique mkt hμ mkt.isManOptimal_galeShapley]
  exact mkt.not_forall_ltM_galeShapley hν

/-- Weak Pareto optimality for the executable algorithm. -/
theorem not_forall_ltM_galeShapleyComputable [DecidableEq M] [DecidableEq W] [Nonempty M]
    {ν : M ≃. W} (hν : mkt.IndividuallyRationalW ν) :
    ¬ ∀ m, mkt.ltM m (mkt.galeShapleyComputable m) (ν m) := by
  rw [mkt.galeShapleyComputable_eq_galeShapley]
  exact mkt.not_forall_ltM_galeShapley hν

end MarriageMarket

end MathEconLib.Matching
