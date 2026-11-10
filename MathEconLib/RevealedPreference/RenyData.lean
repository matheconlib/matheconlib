/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.GARP
public import Mathlib.Analysis.Convex.Quasiconvex

/-!
# Raw data and rationalization for the infinite-data Afriat problem

These definitions follow Reny's 2015 rationalization convention, including
strict utility comparisons for strictly cheaper bundles. The observation type
is arbitrary. Admissibility is stated separately from the raw observations:
zero-price goods and zero choices are allowed. No infinite-data sufficiency
theorem is asserted in this file.

Mathematical reference: Philip J. Reny, "A Characterization of Rationalizable
Consumer Behavior", Econometrica 83 (2015), 175–192, doi:10.3982/ECTA12345.

## References and Lean provenance

Ported from Victor H. Aguiar's Apache-2.0 Lean development
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), module `RenyData`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

variable {L : ℕ} {T S : Type*}

/-- Prices may have zero coordinates, but a price vector is not identically zero. -/
def RenyPriceAdmissible (p : T → Bundle L) : Prop :=
  ∀ t, Nonnegative (p t) ∧ p t ≠ 0

/-- Observed choices may lie anywhere in the nonnegative orthant, including zero. -/
def RenyChoiceAdmissible (q : T → Bundle L) : Prop :=
  ∀ t, Nonnegative (q t)

/-- Reny's rationalization convention distinguishes strict affordability from
weak affordability. It does not require a unique maximizer. -/
def rawRenyRationalizes (p q : T → Bundle L) (u : Utility L) : Prop :=
  ∀ t y, Nonnegative y →
    (dot (p t) y ≤ dot (p t) (q t) → u y ≤ u (q t)) ∧
    (dot (p t) y < dot (p t) (q t) → u y < u (q t))

/-- Utility increases strictly when every commodity coordinate increases.
This is weaker than the package's `StrictlyIncreasing` predicate. -/
def SemiStrictlyIncreasingOnNonnegative (u : Utility L) : Prop :=
  ∀ x y, Nonnegative x → Nonnegative y →
    (∀ i, x i < y i) → u x < u y

/-- A Reny rationalization propagates weak utility comparisons along revealed
preference paths, even when the observation type is infinite. -/
theorem revealedPreferred_monotone_of_rawRenyRationalizes
    (p q : T → Bundle L) (u : Utility L)
    (hchoice : RenyChoiceAdmissible q)
    (hrat : rawRenyRationalizes p q u)
    {s t : T} (hst : RevealedPreferred p q s t) :
    u (q t) ≤ u (q s) := by
  refine Relation.ReflTransGen.head_induction_on hst ?_ ?_
  · exact le_rfl
  · intro a b hab _hbc ih
    exact ih.trans ((hrat a (q b) (hchoice b)).1 hab)

/-- Necessity of GARP uses no finiteness or price-positivity assumption. -/
theorem graphGARP_of_rawRenyRationalizes
    (p q : T → Bundle L) (u : Utility L)
    (hchoice : RenyChoiceAdmissible q)
    (hrat : rawRenyRationalizes p q u) :
    GraphGARP p q := by
  intro s t hst hcheap
  have hweak := revealedPreferred_monotone_of_rawRenyRationalizes p q u hchoice hrat hst
  have hstrict : u (q s) < u (q t) := (hrat t (q s) (hchoice s)).2 hcheap
  exact (not_lt_of_ge hweak) hstrict

/-- A revealed-preference path maps to the original observations under any
reindexing, without injectivity or finiteness assumptions. -/
theorem revealedPreferred_reindex (p q : T → Bundle L) (f : S → T)
    {s t : S} (hst : RevealedPreferred (p ∘ f) (q ∘ f) s t) :
    RevealedPreferred p q (f s) (f t) := by
  refine Relation.ReflTransGen.head_induction_on hst ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro a b hab _hbc ih
    exact ih.head hab

/-- Every subfamily of GARP-consistent observations remains GARP-consistent. -/
theorem graphGARP_reindex (p q : T → Bundle L) (f : S → T)
    (hgarp : GraphGARP p q) : GraphGARP (p ∘ f) (q ∘ f) := by
  intro s t hst
  exact hgarp (f s) (f t) (revealedPreferred_reindex p q f hst)

/-- A revealed-preference path uses only finitely many observations. -/
theorem exists_finset_revealedPref (p q : T → Bundle L)
    {s t : T} (hst : RevealedPreferred p q s t) :
    ∃ (F : Finset T) (hs : s ∈ F) (ht : t ∈ F),
      RevealedPreferred (fun z : F => p z) (fun z : F => q z)
        ⟨s, hs⟩ ⟨t, ht⟩ := by
  classical
  refine Relation.ReflTransGen.head_induction_on hst ?_ ?_
  · exact ⟨{t}, Finset.mem_singleton_self t, Finset.mem_singleton_self t,
      Relation.ReflTransGen.refl⟩
  · intro a b hab _hbc ih
    obtain ⟨F, hb, ht, hF⟩ := ih
    let G := insert a F
    let embed : F → G := fun z => ⟨z, Finset.mem_insert_of_mem z.property⟩
    have haG : a ∈ G := Finset.mem_insert_self a F
    have hbG : b ∈ G := Finset.mem_insert_of_mem hb
    have htG : t ∈ G := Finset.mem_insert_of_mem ht
    have hG : RevealedPreferred (fun z : G => p z) (fun z : G => q z)
        ⟨b, hbG⟩ ⟨t, htG⟩ :=
      revealedPreferred_reindex (fun z : G => p z) (fun z : G => q z) embed hF
    have habG : DirectlyRevealedPreferred (fun z : G => p z) (fun z : G => q z)
        ⟨a, haG⟩ ⟨b, hbG⟩ := hab
    exact ⟨G, haG, htG, hG.head habG⟩

/-- GARP is a finite-character restriction even for arbitrary observation sets.
This is a graph statement, not an infinite-data utility sufficiency theorem. -/
theorem graphGARP_iff_all_finite_restrictions (p q : T → Bundle L) :
    GraphGARP p q ↔
      ∀ F : Finset T, GraphGARP (fun z : F => p z) (fun z : F => q z) := by
  constructor
  · intro hgarp F
    exact graphGARP_reindex p q Subtype.val hgarp
  · intro hfinite s t hst hcheap
    obtain ⟨F, hs, ht, hF⟩ := exists_finset_revealedPref p q hst
    exact hfinite F ⟨s, hs⟩ ⟨t, ht⟩ hF hcheap

end MathEconLib.RevealedPreference
