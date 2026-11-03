/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.Probability.FinDist.Basic
public import Mathlib.Algebra.BigOperators.Field

/-!
# Conditioning finite distributions on events

Finite distributions assign probabilities to events and admit conditional distributions on events
with positive probability. Pointwise conditional masses are zero on null conditioning events; a
separate totalized conditional distribution returns the original distribution on those events.

## Main definitions

* `FinDist.probEvent`: Probability mass of an event `e : Set α`.
* `FinDist.condProb`: Conditional probability mass, equal to `d.pmf x / d.probEvent e` when
  `x ∈ e ∧ 0 < d.probEvent e`, else `0`.
* `FinDist.conditionalOnOrSelf`: Totalized distribution-valued conditional. Falls back to `d`
  itself when `d.probEvent e = 0`.
* `FinDist.conditionalOn`: Conditional distribution on an event with positive probability.

## Main statements

* `FinDist.condProb_sum_one_of_pos`: Conditional masses sum to one on positive-mass events.
* `FinDist.conditionalOn_apply`: The conditional distribution evaluates to `condProb`.
* `FinDist.conditionalOnOrSelf_eq_self_of_zero`: On zero event mass the totalized conditional
  equals the prior.

## Tags

probability, finite distributions, conditional distribution, conditioning
-/

@[expose] public section

open BigOperators

namespace MathEconLib.Probability
namespace FinDist

variable {α : Type*} [Fintype α]

/-- Probability mass of an event `e : Set α` under a finite distribution. -/
noncomputable def probEvent (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : α => x ∈ e), d x

/-- Event mass is nonnegative. -/
lemma probEvent_nonneg (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] :
    0 ≤ d.probEvent e :=
  Finset.sum_nonneg (fun x _ => d.nonneg x)

/-- Event probability is the sum of the masses of its points. -/
lemma probEvent_eq_sum_filter (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] :
    d.probEvent e = ∑ x ∈ Finset.univ.filter (fun x : α => x ∈ e), d x := rfl

/-- Event probability is the sum of probability masses multiplied by the event indicator. -/
lemma probEvent_eq_sum_ite (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] :
    d.probEvent e = ∑ x, if x ∈ e then d x else 0 := by
  rw [probEvent_eq_sum_filter, Finset.sum_filter]

/-- The conditional mass of `x` given `e`, equal to `d x / d.probEvent e` when `x ∈ e` and `e` has
positive probability, and zero otherwise. -/
noncomputable def condProb (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    (x : α) : ℝ :=
  if x ∈ e ∧ 0 < d.probEvent e then d x / d.probEvent e else 0

/-- Conditional mass is the probability ratio on a positive-mass conditioning event and zero
otherwise. -/
lemma condProb_eq_ite (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] (x : α) :
    d.condProb e x = if x ∈ e ∧ 0 < d.probEvent e then d x / d.probEvent e else 0 := rfl

/-- The pointwise conditional mass is nonnegative. -/
lemma condProb_nonneg (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] (x : α) :
    0 ≤ d.condProb e x := by
  unfold condProb
  split_ifs with h
  · exact div_nonneg (d.nonneg x) (le_of_lt h.2)
  · exact le_refl _

/-- The conditional mass vanishes off the conditioning event. -/
lemma condProb_eq_zero_of_notMem (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    {x : α} (hx : x ∉ e) : d.condProb e x = 0 :=
  ite_eq_right fun h => hx h.1

/-- On positive event mass, the conditional mass at a point of `e` is `d x / d.probEvent e`. -/
lemma condProb_eq_of_pos (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    {x : α} (hx : x ∈ e) (hpos : 0 < d.probEvent e) :
    d.condProb e x = d x / d.probEvent e := by
  unfold condProb
  rw [ite_eq_left ⟨hx, hpos⟩]

/-- On positive event mass, the conditional mass sums to one. -/
lemma condProb_sum_one_of_pos (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    (hpos : 0 < d.probEvent e) :
    ∑ x : α, d.condProb e x = 1 := by
  -- The summand is nonzero only on `x ∈ e`; on that set it equals `d x / d.probEvent e`.
  have hrestrict : ∑ x : α, d.condProb e x =
      ∑ x ∈ Finset.univ.filter (fun x : α => x ∈ e), d x / d.probEvent e := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [condProb, hpos]
  rw [hrestrict, ← Finset.sum_div]
  simpa [probEvent_eq_sum_filter] using div_self (ne_of_gt hpos)

/-- On zero event mass, the conditional mass is identically zero, so its sum is zero. -/
lemma condProb_sum_zero_of_not_pos (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    (hnot : ¬ 0 < d.probEvent e) :
    ∑ x : α, d.condProb e x = 0 := by
  exact Finset.sum_eq_zero fun x _ => ite_eq_right fun h => hnot h.2

/-- The conditional distribution on `e` when `e` has positive probability, and the original
distribution when `e` has zero probability. -/
noncomputable def conditionalOnOrSelf (d : FinDist α) (e : Set α)
    [DecidablePred (· ∈ e)] : FinDist α :=
  if h : 0 < d.probEvent e then
    ⟨d.condProb e, d.condProb_nonneg e, d.condProb_sum_one_of_pos e h⟩
  else d

/-- The conditional distribution on an event of positive probability, supported on that event. -/
noncomputable def conditionalOn (d : FinDist α) (e : Set α)
    [DecidablePred (· ∈ e)]
    -- Positive event mass ensures that the result is a conditional distribution supported on `e`.
    (_h_pos : 0 < d.probEvent e) : FinDist α :=
  d.conditionalOnOrSelf e

/-- On a positive-mass event, the conditional distribution agrees with the totalized conditional. -/
lemma conditionalOn_eq_conditionalOnOrSelf (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    (h_pos : 0 < d.probEvent e) :
    d.conditionalOn e h_pos = d.conditionalOnOrSelf e := rfl

/-- The conditional distribution's masses agree with the conditional probability ratios. -/
lemma conditionalOn_apply (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    (hpos : 0 < d.probEvent e) (x : α) :
    (d.conditionalOn e hpos) x = d.condProb e x := by
  unfold conditionalOn conditionalOnOrSelf
  rw [dite_eq_left hpos]
  rfl

/-- When the conditioning event has positive prior mass, the conditional distribution agrees with
the pointwise conditional mass at `x`. -/
lemma conditionalOn_prob_eq (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    {x : α} (hpos : 0 < d.probEvent e) :
    (d.conditionalOn e hpos) x = d.condProb e x :=
  d.conditionalOn_apply e hpos x

/-- On a zero-mass event, `conditionalOnOrSelf` returns the original distribution. -/
lemma conditionalOnOrSelf_eq_self_of_zero (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    (hzero : d.probEvent e = 0) :
    d.conditionalOnOrSelf e = d := by
  unfold conditionalOnOrSelf
  exact dite_eq_right (hzero ▸ lt_irrefl _)

/-- **Conditional event probability as a ratio.** On a positive-mass conditioning event `A`, the
mass that the conditional distribution `d.conditionalOn A` assigns to an event `B` is
`d.probEvent (A ∩ B) / d.probEvent A` — the elementary definition of `Pr(B ∣ A)`. -/
lemma probEvent_conditionalOn (d : FinDist α) (A B : Set α)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] [DecidablePred (· ∈ A ∩ B)]
    (hpos : 0 < d.probEvent A) :
    (d.conditionalOn A hpos).probEvent B = d.probEvent (A ∩ B) / d.probEvent A := by
  -- On positive prior mass, the conditional mass is `if x ∈ A then d x / d.probEvent A else 0`.
  have hconditional_apply : ∀ x : α, (d.conditionalOn A hpos) x =
      if x ∈ A then d x / d.probEvent A else 0 := by
    intro x
    rw [conditionalOn_apply d A hpos x]
    unfold condProb
    simp [hpos]
  rw [probEvent_eq_sum_filter]
  simp_rw [hconditional_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_div,
    Finset.filter_filter]
  rw [probEvent_eq_sum_filter (e := A ∩ B)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro x _
  simp [Set.mem_inter_iff, and_comm]

end FinDist

end MathEconLib.Probability
