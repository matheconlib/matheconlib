/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLibExamples.RevealedPreference.RenyInfinite

/-!
# Concrete clients of the compactness review interfaces

These clients exercise the finite-valued extension and the explicit
prescribed-margin quantifier order requested in MathEconLib issue #202.
They exercise concrete feasibility and the shrinking-gap failure boundary.
The infinite-data Afriat client is in
`MathEconLibExamples.RevealedPreference.RenyInfinite`.
-/

set_option autoImplicit false

-- Compile-time regression clients are intentionally private to this test module.
set_option linter.privateModule false

namespace MathEconLibTest.RevealedPreference.InfiniteAfriat

open MathEconLib
open MathEconLib.RevealedPreference
open MathEconLibExamples.RevealedPreference
open scoped BigOperators

-- Empty observations are covered by the same infinite theorem.
example (p q : Empty → Bundle 1) : HasRegularRenyRationalization p q := by
  apply hasRegularRenyRationalization_of_graphGARP (by decide) p q
  · intro t; exact t.elim
  · intro t; exact t.elim
  · intro t; exact t.elim

-- This instance has infinitely many different choices, a free good, and zero income.
example : Set.Infinite (Set.range RenyInfinite.choice) :=
  RenyInfinite.infinitely_many_choices

example : RenyInfinite.price 0 1 = 0 := rfl

example : dot (RenyInfinite.price 0) (RenyInfinite.choice 0) = 0 := by
  rw [RenyInfinite.zero_observation_choice, dot_zero_right]

private def periodicColor (n : ℕ) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by decide)⟩

private def pairVars (n : ℕ) (k : Fin 2) : ℕ := n + k.val

private def pairRule (n : ℕ) (b : Fin 2 → Fin 3) : Prop :=
  b 0 = periodicColor n ∧ b 1 = periodicColor (n + 1)

/-- An infinite family of overlapping two-variable constraints has a
three-valued model. This uses the new finite-valued theorem, not its Bool
specialization. All finite-feasibility premises are proved concretely. -/
theorem infinite_three_value_model :
    ∃ a : ℕ → Fin 3,
      a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 2 ∧ ∀ n, a (n + 3) = a n := by
  have hf : ∀ s : Finset ℕ, ∃ a : ℕ → Fin 3,
      ∀ n ∈ s, pairRule n (fun k => a (pairVars n k)) := by
    intro s
    refine ⟨periodicColor, ?_⟩
    intro n _hn
    simp [pairRule, pairVars]
  obtain ⟨a, ha⟩ := LogicalCompactness.finite_local_compactness pairVars pairRule hf
  have heq (n : ℕ) : a n = periodicColor n := by
    simpa [pairRule, pairVars] using (ha n).1
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · rw [heq]; rfl
  · rw [heq]; rfl
  · rw [heq]; rfl
  · intro n
    rw [heq, heq]
    apply Fin.ext
    simp [periodicColor]

/-- In the genuinely infinite free-good dataset, one full-family positive
margin schedule works for every finite collection of utility constraints.
The existential `w` is outside the universal finite-subfamily quantifier. -/
theorem infinite_data_uniform_margin_client :
    ∃ w : RationalStrongPair 2 → ℝ,
      (∀ r, 0 < w r) ∧
      (∀ K : Finset (RationalStrongPair 2), ∑ r ∈ K, w r ≤ 1 / 2) ∧
      ∀ s : Finset (InfiniteAfriat.Constraint 2 ℕ),
        ∃ v : InfiniteAfriat.UtilityCube 2, ∀ c ∈ s,
          InfiniteAfriat.Satisfies RenyInfinite.price
            RenyInfinite.choice w c v := by
  obtain ⟨w, hw, hsum, hf⟩ :=
    InfiniteAfriat.exists_fixed_margins_and_finite_witnesses (by decide)
      RenyInfinite.price RenyInfinite.choice
      RenyInfinite.price_admissible RenyInfinite.choice_admissible
      RenyInfinite.graph_garp
  exact ⟨w, hw, hsum, hf⟩

/-- Regression boundary: allowing a positive gap to depend on a finite
subfamily is strictly weaker than prescribing one gap for the whole family.
Every finite set of upper bounds `x ≤ 1/(n+1)` admits a positive `x` in the
compact interval `[0,1]`. -/
theorem finite_subfamilies_allow_shrinking_positive_gaps (s : Finset ℕ) :
    ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < x ∧
      ∀ n ∈ s, x ≤ 1 / ((n : ℝ) + 1) := by
  let x : ℝ := 1 / (((s.sup id : ℕ) : ℝ) + 2)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxone : x ≤ 1 := by
    dsimp [x]
    have hden : (1 : ℝ) ≤ ((s.sup id : ℕ) : ℝ) + 2 := by
      have hn : (0 : ℝ) ≤ ((s.sup id : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
  refine ⟨x, ⟨hx.le, hxone⟩, hx, ?_⟩
  intro n hn
  have hnle : n ≤ s.sup id := Finset.le_sup (f := id) hn
  have hcast : (n : ℝ) ≤ ((s.sup id : ℕ) : ℝ) := by exact_mod_cast hnle
  have hden : (n : ℝ) + 1 ≤ ((s.sup id : ℕ) : ℝ) + 2 := by linarith
  exact one_div_le_one_div_of_le (by positivity) hden

/-- The full family above has no strictly positive feasible point, despite
the preceding finite-subfamily witnesses. This is why one cannot exchange
the fixed-margin and finite-subfamily quantifiers in the Reny proof. -/
theorem no_global_positive_gap_for_shrinking_bounds :
    ¬ ∃ x : ℝ, 0 < x ∧ ∀ n : ℕ, x ≤ 1 / ((n : ℝ) + 1) := by
  rintro ⟨x, hx, hbounds⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
  exact (not_lt_of_ge (hbounds n)) hn

#print axioms LogicalCompactness.finite_local_compactness
#print axioms LogicalCompactness.finite_local_compactness_iff
#print axioms InfiniteAfriat.exists_fixed_margins_and_finite_witnesses
#print axioms infinite_three_value_model
#print axioms infinite_data_uniform_margin_client
#print axioms finite_subfamilies_allow_shrinking_positive_gaps
#print axioms no_global_positive_gap_for_shrinking_bounds
#print axioms infinite_reny_characterization
#print axioms RenyInfinite.has_regular_rationalization

end MathEconLibTest.RevealedPreference.InfiniteAfriat
