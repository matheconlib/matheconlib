/-
Copyright (c) 2026 Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen
-/
module

import MathEconLib.Epistemic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Checked applications of the agreement theorems

Four equally likely states `0, 1, 2, 3` (counting measure; posteriors do not depend on the
normalization). Agent 1 learns whether the state is below `2`, so its information partition is
`{{0, 1}, {2, 3}}`; agent 2 learns the parity of the state, so its partition is
`{{0, 2}, {1, 3}}`. Take the event `E = {0, 1, 3}`.

At the state `0`, agent 1 is certain of `E` and agent 2 gives it probability `1/2`. Aumann's
theorem then shows that this disagreement is not common knowledge, and the approximate agreement
theorem shows that it is not even common `9/10`-belief. Each application discharges every
hypothesis of the theorem for this model. The examples use only the public umbrella import.
-/

-- This module only contains test declarations, which are not part of the library's public API.
set_option linter.privateModule false

open MeasureTheory Setoid MathEconLib.Epistemic
open scoped ENNReal

namespace MathEconLibTest.Epistemic.Examples

/-- Every partition of the four-state space is measurable. -/
theorem measurable (P : Partitions (Fin 4)) : P.Measurable := fun _ _ ↦ .of_discrete

/-- Every part of a partition of the four-state space has positive counting measure. -/
theorem count_pos (P : Partitions (Fin 4)) : ∀ s ∈ P, 0 < (Measure.count : Measure (Fin 4)) s :=
  fun _ hs ↦ pos_iff_ne_zero.2 <|
    Measure.count_ne_zero_iff.2 (nonempty_of_mem_partition P.isPartition hs)

/-- Agent 1 learns whether the state is below `2`. -/
noncomputable abbrev P₁ : Partitions (Fin 4) := Partition.orderIso _ (ker fun i : Fin 4 ↦ i.val / 2)

/-- Agent 2 learns the parity of the state. -/
noncomputable abbrev P₂ : Partitions (Fin 4) := Partition.orderIso _ (ker fun i : Fin 4 ↦ i.val % 2)

/-- The event `{0, 1, 3}`. -/
abbrev E : Set (Fin 4) := ((({0, 1, 3} : Finset (Fin 4))) : Set (Fin 4))

/-- Agent 1's part at the state `0`. -/
theorem part₁_zero : P₁.partOf 0 = ((({0, 1} : Finset (Fin 4))) : Set (Fin 4)) := by
  rw [Partitions.partOf_orderIso]
  ext b
  fin_cases b <;> simp [ker_def]

/-- Agent 2's part at the state `0`. -/
theorem part₂_zero : P₂.partOf 0 = ((({0, 2} : Finset (Fin 4))) : Set (Fin 4)) := by
  rw [Partitions.partOf_orderIso]
  ext b
  fin_cases b <;> simp [ker_def]

/-- At the state `0`, agent 1 is certain of `E`. -/
theorem posterior₁_zero : posterior P₁ Measure.count E 0 = 1 := by
  rw [posterior, part₁_zero, ← Finset.coe_inter, Measure.count_apply_finset,
    Measure.count_apply_finset, show ({0, 1, 3} ∩ {0, 1} : Finset (Fin 4)) = {0, 1} by decide]
  exact ENNReal.div_self (by simp) (by simp)

/-- At the state `0`, agent 2 gives `E` probability `1/2`. -/
theorem posterior₂_zero : posterior P₂ Measure.count E 0 = 1 / 2 := by
  rw [posterior, part₂_zero, ← Finset.coe_inter, Measure.count_apply_finset,
    Measure.count_apply_finset, show ({0, 1, 3} ∩ {0, 2} : Finset (Fin 4)) = {0} by decide,
    show ({0, 2} : Finset (Fin 4)).card = 2 from rfl]
  simp

/-- **Application of Aumann's theorem.** The agents disagree about `E` at the state `0`, and
this disagreement is not common knowledge there. -/
theorem disagreement_not_commonKnowledge :
    posterior P₁ Measure.count E 0 ≠ posterior P₂ Measure.count E 0 ∧
      ¬(P₁ ⊔ P₂).partOf 0 ⊆
        {ω | posterior P₁ Measure.count E ω = 1 ∧ posterior P₂ Measure.count E ω = 1 / 2} := by
  have hne : (1 : ℝ≥0∞) ≠ 1 / 2 := (ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top).ne'
  refine ⟨by rw [posterior₁_zero, posterior₂_zero]; exact hne, fun h ↦ hne ?_⟩
  exact aumann_agreement_of_commonPrior (measurable P₁) (measurable P₂) (count_pos P₁)
    (count_pos P₂) .of_discrete 0 h

/-- **Application of approximate agreement.** The two posteriors at the state `0` differ by
`1/2 > 2 * (1 - 9/10)`, so they are not common `9/10`-belief there. -/
theorem disagreement_not_commonBelief :
    ¬IsCommonBeliefAt ![P₁, P₂] Measure.count (9 / 10)
      {ω | ∀ i, posterior (![P₁, P₂] i) Measure.count E ω = ![1, 1 / 2] i} 0 := by
  intro h
  have := abs_toReal_sub_le_of_isCommonBeliefAt (fun i ↦ measurable _) (fun i ↦ count_pos _)
    .of_discrete 0 (by norm_num) h 0 1
  norm_num [ENNReal.toReal_div] at this

#print axioms disagreement_not_commonKnowledge
#print axioms disagreement_not_commonBelief

end MathEconLibTest.Epistemic.Examples
