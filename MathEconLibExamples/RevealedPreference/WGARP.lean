/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference
public import MathEconLibExamples.RevealedPreference

/-!
# WGARP rationalization beyond ordinary utility

The canonical three-observation example satisfies WGARP but violates GARP. Applying
both characterization theorems to those same data supplies a finite coherent CMU
rationalization and excludes a regular ordinary utility rationalization. The underlying
prices, choices, and exact arithmetic are defined once in
`MathEconLibExamples.RevealedPreference`.

An explicit three-agent majority witness also proves regularity and rationalization
on three observed budgets, then applies the supplied-witness converse. Its scores
exhibit a strict cycle on the separate menu of unit bundles.

A single two-member coalition with positive linear utilities gives scores of minus one
in both directions between two unit bundles. Its regular, sign-asymmetric preference
is incomplete, is not numerically skew symmetric, and chooses neither bundle on that menu.

A separate tie example distinguishes WGARP from the single-valued WARP condition:
two distinct choices on the same budget are permitted by weak rationalization.
These are exact mathematical examples, not empirical estimates. No demand existence
on unobserved budgets, numerical skew symmetry, or matrix/simplex representation is claimed.

## References

The three-observation data are attributed in the canonical example to Hans Keiding
and Mich Tvede (2013), *Revealed smooth nontransitive preferences*, Economic Theory
**54**(3), 463–484, Example 1, p. 467.
[DOI: 10.1007/s00199-013-0765-z](https://doi.org/10.1007/s00199-013-0765-z).
-/

@[expose] public section

namespace MathEconLibExamples.RevealedPreference

open MathEconLib.RevealedPreference

/-- The existing pairwise checks are exactly WGARP. -/
theorem three_wgarp : WGARP threeDataset := by
  intro s t hts
  apply le_of_not_gt
  intro hst
  exact three_no_pairwise_reversal t s
    ((directlyRevealedPreferred_iff_expenditureGap_nonneg threeDataset t s).mpr hts)
    ((strictlyCheaperAt_iff_expenditureGap_pos threeDataset s t).mpr hst)

/-- The named WGARP characterization supplies a coherent CMU, while finite Afriat
rules out every regular ordinary utility for the same observations. -/
theorem three_cmu_but_not_regular_utility :
    HasFiniteCoherentCMURationalization threeDataset ∧
      ¬ HasRegularUtilityRationalization threeDataset := by
  refine ⟨(wgarp_iff_hasFiniteCoherentCMURationalization threeDataset).mp three_wgarp, ?_⟩
  intro h
  exact three_not_garp ((garp_iff_hasRegularUtilityRationalization threeDataset).mpr h)

/-- The preference-function characterization also applies to the three-cycle. -/
theorem three_has_regular_preference : HasRegularPreferenceRationalization threeDataset :=
  (wgarp_iff_hasRegularPreferenceRationalization threeDataset).mp three_wgarp

/-- The same rationalizer supplies a choice correspondence containing each observed
choice on its budget, without asserting nonempty demand on other menus. -/
theorem three_has_regular_preferenceChoice :
    ∃ r : PreferenceFunction 3,
      ContinuousPreference r ∧ StrictlyIncreasingFirst r ∧ SignAsymmetric r ∧
        ∀ t, threeDataset.choice t ∈ preferenceChoice r (budgetSet threeDataset t) :=
  (wgarp_iff_exists_regular_preferenceChoice threeDataset).mp three_wgarp

/-- Three two-agent majorities, supplied independently of the observation construction. -/
def majorityCoalitions : FiniteCoalitionSystem (Fin 3) (Fin 3) where
  members := ![{0, 1}, {1, 2}, {2, 0}]
  members_nonempty := by intro c; fin_cases c <;> simp

/-- Any two majorities share an agent. -/
theorem majorityCoalitions_isCoherent : majorityCoalitions.IsCoherent := by
  intro c d
  fin_cases c <;> fin_cases d <;> norm_num [majorityCoalitions, Fin.exists_fin_succ]

/-- Positive linear utility coefficients with cyclic rankings of the unit bundles. -/
def majorityWeights : Fin 3 → Bundle 3 := ![![3, 2, 1], ![1, 3, 2], ![2, 1, 3]]

/-- The three supplied utilities are ordinary linear utilities. -/
noncomputable def majorityAgents (i : Fin 3) : Utility 3 := dot (majorityWeights i)

/-- Every supplied component is continuous, strictly increasing, and concave globally. -/
theorem majorityAgents_regular (i : Fin 3) :
    Continuous (majorityAgents i) ∧ StrictlyIncreasing (majorityAgents i) ∧
      ConcaveOn ℝ Set.univ (majorityAgents i) := by
  refine ⟨continuous_dot _, ?_, convex_univ, ?_⟩
  · apply strictlyIncreasing_iff_strictMono.mpr
    intro z x hzx
    apply dot_strictlyIncreasing_of_pos (p := majorityWeights i) _
      (strictDominates_iff_lt.mpr hzx)
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [majorityWeights]
  · intro x _ y _ a b _ _ _
    exact le_of_eq (dot_add_smul (majorityWeights i) x y a b).symm

/-- Three unit purchases, each facing prices that support a majority of the utilities. -/
def majorityDataset : Dataset 3 (Fin 3) where
  price := ![![1, 2, 2], ![2, 1, 2], ![2, 2, 1]]
  choice := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]
  price_pos := by intro t i; fin_cases t <;> fin_cases i <;> norm_num
  choice_nonneg := by intro t i; fin_cases t <;> fin_cases i <;> norm_num

/-- A supporting majority maximizes the observed purchase over its whole budget. -/
theorem majority_rationalizes :
    PreferenceRationalizes majorityDataset (finiteCMU majorityCoalitions majorityAgents) := by
  apply finiteCMU_rationalizes_of_coalitions
  intro t
  refine ⟨(![2, 0, 1] : Fin 3 → Fin 3) t, ?_⟩
  intro i hi y hy
  have h0 : (0 : ℝ) ≤ y 0 := hy.1 0
  have h1 : (0 : ℝ) ≤ y 1 := hy.1 1
  have h2 : (0 : ℝ) ≤ y 2 := hy.1 2
  have hb := hy.2
  fin_cases t <;> fin_cases i <;>
    norm_num [majorityCoalitions] at hi <;>
    norm_num [majorityAgents, majorityWeights, majorityDataset, expenditure,
      dot, dotProduct, Fin.sum_univ_succ] at hb ⊢ <;> linarith

/-- All assumptions of the supplied-witness converse are proved for the explicit model. -/
theorem majority_cmu_rationalizes :
    FiniteCoherentCMURationalizes majorityDataset majorityCoalitions majorityAgents :=
  ⟨majorityCoalitions_isCoherent, fun i => (majorityAgents_regular i).1,
    fun i => (majorityAgents_regular i).2.1, fun i => (majorityAgents_regular i).2.2,
    majority_rationalizes⟩

/-- The named supplied-witness converse establishes WGARP without constructing row coalitions. -/
theorem majority_wgarp : WGARP majorityDataset :=
  majority_cmu_rationalizes.wgarp majorityDataset majorityCoalitions majorityAgents

/-- The supplied CMU has a strict three-cycle on the separate menu of unit bundles.
Every forward score is exactly one and every reverse score is minus one. -/
theorem majority_scores :
    finiteCMU majorityCoalitions majorityAgents ![1, 0, 0] ![0, 1, 0] = 1 ∧
    finiteCMU majorityCoalitions majorityAgents ![0, 1, 0] ![0, 0, 1] = 1 ∧
    finiteCMU majorityCoalitions majorityAgents ![0, 0, 1] ![1, 0, 0] = 1 ∧
    finiteCMU majorityCoalitions majorityAgents ![0, 1, 0] ![1, 0, 0] = -1 ∧
    finiteCMU majorityCoalitions majorityAgents ![0, 0, 1] ![0, 1, 0] = -1 ∧
    finiteCMU majorityCoalitions majorityAgents ![1, 0, 0] ![0, 0, 1] = -1 := by
  norm_num [finiteCMU, coalitionScore, majorityCoalitions, majorityAgents, majorityWeights,
    Fin.univ_succ, dot, dotProduct, Fin.sum_univ_succ]

/-- One coalition containing both agents: every comparison requires their unanimity. -/
def disagreementCoalitions : FiniteCoalitionSystem (Fin 1) (Fin 2) where
  members := fun _ => {0, 1}
  members_nonempty := by intro c; simp

/-- The single two-member coalition is coherent. -/
theorem disagreementCoalitions_isCoherent : disagreementCoalitions.IsCoherent := by
  intro c d
  exact ⟨0, by simp [disagreementCoalitions], by simp [disagreementCoalitions]⟩

/-- The agents weight the two goods differently, with strictly positive coefficients. -/
def disagreementWeights : Fin 2 → Bundle 2 := ![![2, 1], ![1, 2]]

/-- The two utilities are `2 * x 0 + x 1` and `x 0 + 2 * x 1`. -/
noncomputable def disagreementAgents (i : Fin 2) : Utility 2 := dot (disagreementWeights i)

/-- Both components are continuous, strictly increasing, and concave on all bundles. -/
theorem disagreementAgents_regular (i : Fin 2) :
    Continuous (disagreementAgents i) ∧ StrictlyIncreasing (disagreementAgents i) ∧
      ConcaveOn ℝ Set.univ (disagreementAgents i) := by
  refine ⟨continuous_dot _, ?_, convex_univ, ?_⟩
  · apply strictlyIncreasing_iff_strictMono.mpr
    intro z x hzx
    apply dot_strictlyIncreasing_of_pos (p := disagreementWeights i) _
      (strictDominates_iff_lt.mpr hzx)
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [disagreementWeights]
  · intro x _ y _ a b _ _ _
    exact le_of_eq (dot_add_smul (disagreementWeights i) x y a b).symm

/-- The CMU has the regularity and sign asymmetry used in preference rationalization. -/
theorem disagreement_preference_regular :
    ContinuousPreference (finiteCMU disagreementCoalitions disagreementAgents) ∧
      StrictlyIncreasingFirst (finiteCMU disagreementCoalitions disagreementAgents) ∧
      SignAsymmetric (finiteCMU disagreementCoalitions disagreementAgents) := by
  refine ⟨finiteCMU_continuous _ _ (fun _ i _ => (disagreementAgents_regular i).1),
    finiteCMU_strictlyIncreasingFirst _ _
      (fun _ i _ => (disagreementAgents_regular i).2.1), ?_, ?_⟩
  · intro x y h
    exact finiteCMU_weakSignAsymmetry _ _ disagreementCoalitions_isCoherent h
  · intro x y h
    exact finiteCMU_signAsymmetry _ _ disagreementCoalitions_isCoherent h

/-- Disagreement makes both directional scores minus one on the binary unit-bundle menu. -/
theorem disagreement_scores :
    finiteCMU disagreementCoalitions disagreementAgents ![1, 0] ![0, 1] = -1 ∧
      finiteCMU disagreementCoalitions disagreementAgents ![0, 1] ![1, 0] = -1 := by
  norm_num [finiteCMU, coalitionScore, disagreementCoalitions, disagreementAgents,
    disagreementWeights, Fin.univ_succ, dot, dotProduct, Fin.sum_univ_succ]

/-- Neither weak comparison holds, so the induced relation is incomplete. -/
theorem disagreement_incomparable :
    ¬ (0 ≤ finiteCMU disagreementCoalitions disagreementAgents ![1, 0] ![0, 1] ∨
      0 ≤ finiteCMU disagreementCoalitions disagreementAgents ![0, 1] ![1, 0]) := by
  rw [disagreement_scores.1, disagreement_scores.2]
  norm_num

/-- Coherence and sign asymmetry do not force numerical skew symmetry. -/
theorem disagreement_not_skew :
    finiteCMU disagreementCoalitions disagreementAgents ![0, 1] ![1, 0] ≠
      -finiteCMU disagreementCoalitions disagreementAgents ![1, 0] ![0, 1] := by
  rw [disagreement_scores.1, disagreement_scores.2]
  norm_num

/-- The actual induced choice is empty on a nonempty two-alternative menu. -/
theorem disagreement_preferenceChoice_empty :
    preferenceChoice (finiteCMU disagreementCoalitions disagreementAgents)
      {![1, 0], ![0, 1]} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx, hcomp⟩ := (mem_preferenceChoice _ _ _).mp hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · have h := hcomp ![0, 1] (by simp)
    rw [disagreement_scores.1] at h
    norm_num at h
  · have hx := Set.mem_singleton_iff.mp hx
    subst x
    have h := hcomp ![1, 0] (by simp)
    rw [disagreement_scores.2] at h
    norm_num at h

/-- Two distinct bundles chosen at identical prices and identical expenditure. -/
def tieDataset : Dataset 2 (Fin 2) where
  price := fun _ => ![1, 1]
  choice := fun t => if t = 0 then ![1, 0] else ![0, 1]
  price_pos := by intro t i; fin_cases i <;> norm_num
  choice_nonneg := by intro t i; fin_cases t <;> fin_cases i <;> norm_num

/-- Every cross-budget comparison in the tie example is an equality. -/
theorem tie_expenditureGap (s t : Fin 2) : expenditureGap tieDataset s t = 0 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [expenditureGap, tieDataset, dot, dotProduct, Fin.sum_univ_succ]

/-- WGARP permits distinct choices tied on the same budget. -/
theorem tie_wgarp : WGARP tieDataset := by
  intro s t _
  exact le_of_eq (tie_expenditureGap s t)

/-- The strict reverse-affordability condition for single-valued WARP fails.
The condition is written explicitly to avoid confusing it with WGARP. -/
theorem tie_not_unique_choice_warp :
    ¬ (∀ s t, tieDataset.choice s ≠ tieDataset.choice t →
      DirectlyRevealedPreferred tieDataset.price tieDataset.choice s t →
        expenditure tieDataset t (tieDataset.choice t) <
          expenditure tieDataset t (tieDataset.choice s)) := by
  intro h
  have hne : tieDataset.choice 0 ≠ tieDataset.choice 1 := by
    intro heq
    have hcoord := congrFun heq 0
    norm_num [tieDataset] at hcoord
  have hdirect : DirectlyRevealedPreferred tieDataset.price tieDataset.choice 0 1 :=
    (directlyRevealedPreferred_iff_expenditureGap_nonneg tieDataset 0 1).mpr
      (le_of_eq (tie_expenditureGap 0 1).symm)
  have hbad := h 0 1 hne hdirect
  norm_num [expenditure, tieDataset, dot, dotProduct, Fin.sum_univ_succ] at hbad

/-- Regular preference rationalization retains these budget ties. -/
theorem tie_has_regular_preference : HasRegularPreferenceRationalization tieDataset :=
  (wgarp_iff_hasRegularPreferenceRationalization tieDataset).mp tie_wgarp

/-- A weak comparison followed by a strict reverse comparison violates WGARP. -/
theorem cycle_not_wgarp : ¬ WGARP cycleDataset := by
  intro h
  have hbad := h (0 : Fin 2) (1 : Fin 2)
  norm_num [expenditureGap, cycleDataset, cyclePrices, cycleChoices,
    dot, dotProduct, Fin.sum_univ_succ] at hbad

/-- The converse characterization excludes regular preference rationalization
for the mixed weak/strict binary cycle. -/
theorem cycle_no_regular_preference : ¬ HasRegularPreferenceRationalization cycleDataset := by
  intro h
  exact cycle_not_wgarp ((wgarp_iff_hasRegularPreferenceRationalization cycleDataset).mpr h)

end MathEconLibExamples.RevealedPreference
