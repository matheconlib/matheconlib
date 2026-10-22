/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.DeferredAcceptanceComputable
import MathEconLib.Matching.Classical.Marriage.RankPreferences
import MathEconLib.ForMathlib.Uniform
import Mathlib.Probability.Independence.Basic

/-!
# Finite random preference profiles for marriage markets

The deterministic `RankPreferences` layer encodes strict complete rankings of the other
population. Smaller ranks are preferred. The adapter to `MarriageMarket` reverses this order
and puts every partner above remaining unmatched. The two population sizes are separate parameters.

`uniformProfile` is Mathlib's uniform PMF on the full finite profile space.
`uniformProfile_apply_eq_prod` identifies its joint masses with the product of uniform
individual-ranking masses. `uniformProfile_map_agentRanks` gives the product measure,
`uniformProfile_map_ranking` gives each marginal, and `iIndepFun_uniformProfile` establishes
Mathlib's joint independence across both populations, including empty and unequal markets.
These specialize shared finite-uniform transport and product-law lemmas.
No executable random-number generator is asserted.

The short-side completeness results show that the existing executable proposer DA matches
everyone on a side no larger than the other. The balanced corollaries cover both sides.
`expectedAverageProposerRank_two` proves its expected average one-based proposer rank is `5/4`
in the two-by-two model.
The calculation is checked by Lean's kernel over all sixteen profiles.

The rank adapter specializes the existing optional-partner orders; it introduces no second
preference foundation. This is the overlap with the preference-port scoping work in issue #161.
The generic short-side completeness lemma is in `Marriage.Basic`, independent of rank
profiles and probability. Ranks remain ordinal positions; no utility representation is required.

This implements the first finite benchmark in issue #166. Proposal-count bounds, balanced-market
asymptotics, stable-matching counts, and the Ashlagi–Kanoria–Leshno imbalance results remain later
work. In particular, assigning an outside-option rank does not define the matched-agent averages
needed for those imbalance results.

## Provenance

The profile representation is adapted from `StableMarriage.Profile` in
`FormalConjecturesForMathlib/Combinatorics/StableMarriage.lean`, formal-conjectures PR #4955,
revision `db05d685417a9c711d7438ea966e42ff605f0413`:
https://github.com/google-deepmind/formal-conjectures/blob/db05d685417a9c711d7438ea966e42ff605f0413/FormalConjecturesForMathlib/Combinatorics/StableMarriage.lean
The original code is copyright 2026 The Formal Conjectures Authors and licensed under Apache 2.0.
Here its single population-size parameter is generalized to two. Stability and deferred acceptance
are supplied by the existing matching library; no conjecture or alternative stability predicate
is imported.

## References

* L. B. Wilson (1972), *An analysis of the stable marriage assignment algorithm*, BIT 12,
  569–575. https://doi.org/10.1007/BF01932966. The general proposal bound is not formalized here.
* Itai Ashlagi, Yash Kanoria, and Jacob D. Leshno (2017), *Unbalanced Random Matching Markets:
  The Stark Effect of Competition*, Journal of Political Economy 125(1), 69–98.
  https://doi.org/10.1086/689869. The independent uniform preference model agrees with Section II.A;
  the asymptotic theorems are outside this module's scope.

The `5/4` benchmark is a direct finite calculation, not an attribution of that statement to either
paper. Related tracking: https://github.com/matheconlib/matheconlib/issues/166 and
https://github.com/matheconlib/matheconlib/issues/161.
-/

namespace MathEconLib.Matching.MarriageMarket

open scoped BigOperators

namespace RankProfile

variable {m n : ℕ}

/-- Discrete measurable structure on the finite profile space. -/
instance : MeasurableSpace (RankProfile m n) := ⊤

/-- Individual finite rankings carry the discrete measurable structure. -/
instance (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

instance (a : Fin m ⊕ Fin n) : MeasurableSpace (Ranking m n a) := by
  cases a <;> dsimp [Ranking] <;> infer_instance

instance (a : Fin m ⊕ Fin n) : DiscreteMeasurableSpace (Ranking m n a) := by
  cases a <;> dsimp [Ranking] <;> infer_instance

/-- Independent uniform rankings for both populations, as the uniform law on all rank profiles.
This adapts `StableMarriage.uniformProfile` from the source cited above. -/
noncomputable def uniformProfile (m n : ℕ) : PMF (RankProfile m n) :=
  PMF.uniformOfFintype (RankProfile m n)

/-- Every full profile has equal mass. -/
theorem uniformProfile_apply (p : RankProfile m n) :
    uniformProfile m n p =
      (((Nat.factorial n) ^ m * (Nat.factorial m) ^ n : ℕ) : ENNReal)⁻¹ := by
  simp [uniformProfile, PMF.uniformOfFintype_apply, card]

/-- The full joint mass factors into the uniform masses of all individual rankings.
Because `equivRanks` is a bijection onto unrestricted ranking families, this characterizes
independent uniform preference lists, rather than only normalization of the joint law. -/
theorem uniformProfile_apply_eq_prod (p : RankProfile m n) :
    uniformProfile m n p =
      (∏ i : Fin m, PMF.uniformOfFintype (Equiv.Perm (Fin n)) (p.manRank i)) *
      (∏ j : Fin n, PMF.uniformOfFintype (Equiv.Perm (Fin m)) (p.womanRank j)) := by
  simp only [uniformProfile, PMF.uniformOfFintype_apply, card, Fintype.card_perm,
    Fintype.card_fin, Finset.prod_const, Finset.card_univ, Nat.cast_mul, Nat.cast_pow]
  rw [ENNReal.mul_inv (a := (n.factorial : ENNReal) ^ m)
    (b := (m.factorial : ENNReal) ^ n) (by simp) (by simp)]
  simp [ENNReal.inv_pow]

/-- The profile law is normalized, including empty populations. -/
theorem uniformProfile_univ (m n : ℕ) :
    (uniformProfile m n).toMeasure Set.univ = 1 := by simp

open MeasureTheory

/-- Viewing a uniform profile as its individual rankings gives their full product law. -/
theorem uniformProfile_map_agentRanks (m n : ℕ) :
    (uniformProfile m n).toMeasure.map (equivAgentRanks m n) =
      Measure.pi (fun a ↦ (PMF.uniformOfFintype (Ranking m n a)).toMeasure) := by
  rw [PMF.toMeasure_map _ _ Measurable.of_discrete]
  rw [uniformProfile, PMF.map_uniformOfFintype]
  exact PMF.toMeasure_uniformOfFintype_pi (α := Ranking m n)

/-- Every agent's ranking is uniform on all permutations of the other population. -/
theorem uniformProfile_map_ranking (m n : ℕ) (a : Fin m ⊕ Fin n) :
    (uniformProfile m n).toMeasure.map (fun p ↦ equivAgentRanks m n p a) =
      (PMF.uniformOfFintype (Ranking m n a)).toMeasure := by
  calc
    _ = ((uniformProfile m n).toMeasure.map (equivAgentRanks m n)).map
        (Function.eval a) := by
      exact (Measure.map_map (measurable_pi_apply a) Measurable.of_discrete).symm
    _ = _ := by
      rw [uniformProfile_map_agentRanks]
      exact (measurePreserving_eval _ a).map_eq

theorem uniformProfile_map_manRank (i : Fin m) :
    (uniformProfile m n).toMeasure.map (fun p ↦ p.manRank i) =
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure :=
  uniformProfile_map_ranking m n (Sum.inl i)

theorem uniformProfile_map_womanRank (j : Fin n) :
    (uniformProfile m n).toMeasure.map (fun p ↦ p.womanRank j) =
      (PMF.uniformOfFintype (Equiv.Perm (Fin m))).toMeasure :=
  uniformProfile_map_ranking m n (Sum.inr j)

/-- All individual rankings are jointly independent, across as well as within the two sides. -/
theorem iIndepFun_uniformProfile (m n : ℕ) :
    ProbabilityTheory.iIndepFun (fun a p ↦ equivAgentRanks m n p a)
      (uniformProfile m n).toMeasure := by
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun _ ↦ Measurable.of_discrete.aemeasurable)).mpr
  simp only [uniformProfile_map_ranking]
  exact uniformProfile_map_agentRanks m n

/-- Every proposer is matched when the proposer population is no larger. -/
theorem isSome_galeShapleyComputable_of_le (p : RankProfile m n) (h : m ≤ n) (i : Fin m) :
    (p.toMarriageMarket.galeShapleyComputable i).isSome :=
  Unblocked.isSome_of_card_le p.toMarriageMarket
    p.toMarriageMarket.stable_galeShapleyComputable.2 (by simpa using h)
    p.toMarriageMarket_acceptableM p.toMarriageMarket_acceptableW i

/-- Every receiver is matched when the receiver population is no larger. -/
theorem isSome_symm_galeShapleyComputable_of_le (p : RankProfile m n) (h : n ≤ m)
    (j : Fin n) : (p.toMarriageMarket.galeShapleyComputable.symm j).isSome := by
  have hs := p.toMarriageMarket.stable_galeShapleyComputable
  exact Unblocked.isSome_of_card_le p.toMarriageMarket.symm
    ((p.toMarriageMarket.isStableMatching_symm _).mpr hs).2 (by simpa using h)
    p.toMarriageMarket_acceptableW p.toMarriageMarket_acceptableM j

/-- Balanced rank profiles give complete outcomes under the existing executable proposer DA. -/
theorem isSome_galeShapleyComputable (p : RankProfile n n) (i : Fin n) :
    (p.toMarriageMarket.galeShapleyComputable i).isSome :=
  isSome_galeShapleyComputable_of_le p le_rfl i

/-- The same balanced DA outcome matches every receiver. -/
theorem isSome_symm_galeShapleyComputable (p : RankProfile n n) (j : Fin n) :
    (p.toMarriageMarket.galeShapleyComputable.symm j).isSome :=
  isSome_symm_galeShapleyComputable_of_le p le_rfl j

/-- The existing proposer-optimality result gives weakly lower average rank than any stable
outcome, including in unequal markets. This compares ordinal positions, not cardinal utilities. -/
theorem averageProposerRank_galeShapleyComputable_le (p : RankProfile m n)
    {ν : Fin m ≃. Fin n} (hν : p.toMarriageMarket.IsStableMatching ν) :
    p.averageProposerRank p.toMarriageMarket.galeShapleyComputable ≤ p.averageProposerRank ν :=
  p.averageProposerRank_le (p.toMarriageMarket.galeShapleyComputable_manOptimal hν)

/-- Expected average rank of the existing executable proposer DA under independent uniform
preferences. Randomness is in the profile, not selection among stable outcomes. -/
noncomputable def expectedAverageProposerRank (n : ℕ) : ℝ :=
  ∫ p, p.averageProposerRank p.toMarriageMarket.galeShapleyComputable
    ∂(uniformProfile n n).toMeasure

/-- The expectation is the ordinary average over all finite profiles. -/
theorem expectedAverageProposerRank_eq_sum (n : ℕ) :
    expectedAverageProposerRank n =
      (∑ p : RankProfile n n,
        (p.totalProposerRank p.toMarriageMarket.galeShapleyComputable : ℝ)) /
        ((Fintype.card (RankProfile n n) : ℝ) * n) := by
  rw [expectedAverageProposerRank, uniformProfile, PMF.integral_uniformOfFintype,
    Fintype.expect_eq_sum_div_card]
  simp_rw [averageProposerRank_eq_total_div]
  rw [← Finset.sum_div, div_div, mul_comm (n : ℝ)]

/-- The empty-population average is zero under the documented division convention. -/
@[simp] theorem expectedAverageProposerRank_zero : expectedAverageProposerRank 0 = 0 := by
  rw [expectedAverageProposerRank_eq_sum]
  simp

set_option maxRecDepth 4096 in
/-- Exact finite evaluation of the existing executable DA on all sixteen two-by-two profiles.
Eight profiles have total proposer rank two and eight have total proposer rank three.
The kernel checks this finite calculation; no external computation supplies the proof. -/
theorem sum_totalProposerRank_two :
    (∑ p : RankProfile 2 2,
      p.totalProposerRank p.toMarriageMarket.galeShapleyComputable) = 40 := by
  decide +kernel

/-- Under independent uniform complete strict rankings in the two-by-two marriage market,
the existing executable proposer DA has expected average one-based proposer rank `5/4`.
This is a finite ordinal-rank benchmark, not a cardinal welfare or asymptotic claim. -/
theorem expectedAverageProposerRank_two : expectedAverageProposerRank 2 = 5 / 4 := by
  rw [expectedAverageProposerRank_eq_sum, ← Nat.cast_sum, sum_totalProposerRank_two, card]
  norm_num

end RankProfile
end MathEconLib.Matching.MarriageMarket
