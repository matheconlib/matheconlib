/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Maximizers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Substitution across a retailer's checkout systems

A retailer can buy at most one of two checkout systems and can also buy an inventory app.
Singleton purchases and refusals bound standalone values between `9.90` and `10.10`. With
either checkout system priced at `1`, purchases and refusals bracket the marginal value of
the app between `7.90` and `8.10` with the first system and between `4.90` and `5.10` with
the second. An observed purchase need only maximize surplus, so ties are allowed.

These observations imply disjoint bounds on the substitution penalties between each checkout
system and the app. The gross-substitutes triangle condition forces the penalty between the two
checkout systems to equal the smaller of those penalties. On a menu offering just the two systems
at `7` each, relaxing the constraint makes the pair uniquely optimal under every valuation
satisfying the hypotheses. The observations are exact illustrative data.

We use the triangle condition at the empty bundle as a hypothesis. For its role in the
local characterization of gross substitutes, see Eric Balkanski and Renato Paes Leme (2020),
*On the Construction of Substitutes*, §2.1, [DOI](https://doi.org/10.1287/moor.2019.0991).
-/

@[expose] public section

namespace MathEconLib.Examples.Choice.RetailerSubstitution

open BigOperators

/-- Two checkout systems in one category and an inventory app in the other. -/
inductive Product
  | checkoutA
  | checkoutB
  | inventory
  deriving DecidableEq

open Product

abbrev Bundle := Finset Product

/-- The retailer's value for a bundle less its total posted price. -/
def surplus (v : Bundle → ℝ) (prices : Product → ℝ) (bundle : Bundle) : ℝ :=
  v bundle - ∑ item ∈ bundle, prices item

/-- Every surplus-maximizing subset of the offered menu. -/
def demand (v : Bundle → ℝ) (prices : Product → ℝ) (menu : Bundle) : Set Bundle :=
  Choice.maximizers (Preferences.Preference.ofUtility (surplus v prices))
    {bundle | bundle ⊆ menu}

private theorem mem_demand {v : Bundle → ℝ} {prices : Product → ℝ} {menu bundle : Bundle} :
    bundle ∈ demand v prices menu ↔
      bundle ⊆ menu ∧ ∀ other ⊆ menu, surplus v prices other ≤ surplus v prices bundle :=
  Choice.mem_maximizers_ofUtility _

/-- A quote for one product, with all other offered products priced at one. -/
def probePrices (item : Product) (quote : ℝ) (other : Product) : ℝ :=
  if other = item then quote else 1

/-- Buy the base and the tested product at the low quote, and only the base at the high quote. -/
def BracketObservation (v : Bundle → ℝ) (base : Bundle) (item : Product) (low high : ℝ) : Prop :=
  insert item base ∈ demand v (probePrices item low) (insert item base) ∧
    base ∈ demand v (probePrices item high) (insert item base)

/-- The singleton and checkout–inventory observations in the example. -/
structure FitsObservations (v : Bundle → ℝ) : Prop where
  standalone (item : Product) : BracketObservation v ∅ item (99 / 10) (101 / 10)
  withCheckoutA : BracketObservation v {checkoutA} inventory (79 / 10) (81 / 10)
  withCheckoutB : BracketObservation v {checkoutB} inventory (49 / 10) (51 / 10)

/-- The reduction in marginal value from having the other product. -/
def pairPenalty (v : Bundle → ℝ) (i j : Product) : ℝ :=
  v {i} + v {j} - v {i, j} - v ∅

/-- The three pair penalties obey the gross-substitutes triangle inequalities. -/
def HasSubstitutesTriangle (v : Bundle → ℝ) : Prop :=
  let x := pairPenalty v checkoutA checkoutB
  let y := pairPenalty v checkoutA inventory
  let z := pairPenalty v checkoutB inventory
  min y z ≤ x ∧ min x z ≤ y ∧ min x y ≤ z

private theorem marginal_bounds {v : Bundle → ℝ} {base : Bundle} {item : Product}
    {low high : ℝ} (hitem : item ∉ base) (h : BracketObservation v base item low high) :
    low ≤ v (insert item base) - v base ∧ v (insert item base) - v base ≤ high := by
  have bought := (mem_demand.mp h.1).2 base (Finset.subset_insert item base)
  have passed := (mem_demand.mp h.2).2 _ (Finset.Subset.refl _)
  simp [surplus, Finset.sum_insert hitem, probePrices] at bought passed
  constructor <;> linarith

private theorem singleton_bounds {v : Bundle → ℝ} (h : FitsObservations v) (i : Product) :
    (99 : ℝ) / 10 ≤ v {i} - v ∅ ∧ v {i} - v ∅ ≤ 101 / 10 := by
  simpa using marginal_bounds (Finset.notMem_empty i) (h.standalone i)

/-- The app observations give disjoint bounds for its penalties with the two systems. -/
theorem inventory_penalty_bounds {v : Bundle → ℝ} (h : FitsObservations v) :
    (9 : ℝ) / 5 ≤ pairPenalty v checkoutA inventory ∧
    pairPenalty v checkoutA inventory ≤ 11 / 5 ∧
    (24 : ℝ) / 5 ≤ pairPenalty v checkoutB inventory ∧
    pairPenalty v checkoutB inventory ≤ 26 / 5 := by
  obtain ⟨hInventoryLow, hInventoryHigh⟩ := singleton_bounds h inventory
  have hA : (79 : ℝ) / 10 ≤ v {checkoutA, inventory} - v {checkoutA} ∧
      v {checkoutA, inventory} - v {checkoutA} ≤ 81 / 10 := by
    simpa [Finset.pair_comm inventory checkoutA] using
      marginal_bounds (by simp : inventory ∉ ({checkoutA} : Bundle)) h.withCheckoutA
  have hB : (49 : ℝ) / 10 ≤ v {checkoutB, inventory} - v {checkoutB} ∧
      v {checkoutB, inventory} - v {checkoutB} ≤ 51 / 10 := by
    simpa [Finset.pair_comm inventory checkoutB] using
      marginal_bounds (by simp : inventory ∉ ({checkoutB} : Bundle)) h.withCheckoutB
  obtain ⟨hALow, hAHigh⟩ := hA
  obtain ⟨hBLow, hBHigh⟩ := hB
  unfold pairPenalty
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The smaller app penalty determines the penalty between the checkout systems. -/
theorem checkout_penalty_eq {v : Bundle → ℝ} (h : FitsObservations v)
    (htriangle : HasSubstitutesTriangle v) :
    pairPenalty v checkoutA checkoutB = pairPenalty v checkoutA inventory := by
  obtain ⟨_, hAUpper, hBLower, _⟩ := inventory_penalty_bounds h
  have hAB : pairPenalty v checkoutA inventory < pairPenalty v checkoutB inventory :=
    hAUpper.trans_lt ((by norm_num : (11 : ℝ) / 5 < 24 / 5).trans_le hBLower)
  obtain ⟨hleft, hright, _⟩ := htriangle
  rw [min_eq_left hAB.le] at hleft
  refine le_antisymm ?_ hleft
  by_contra! hgreater
  exact (not_lt_of_ge hright) (lt_min hgreater hAB)

private theorem subset_pair_iff {bundle : Bundle} {i j : Product} :
    bundle ⊆ {i, j} ↔ bundle = ∅ ∨ bundle = {i} ∨ bundle = {j} ∨ bundle = {i, j} := by
  rw [← Finset.mem_powerset]
  change bundle ∈ (insert i (insert j (∅ : Bundle))).powerset ↔ _
  simp [Finset.powerset_insert, eq_comm, or_assoc, or_left_comm]

/-- At seven per system, the relaxed menu has a unique optimal purchase. -/
theorem relaxedDemand_eq {v : Bundle → ℝ} (h : FitsObservations v)
    (htriangle : HasSubstitutesTriangle v) :
    demand v (fun _ ↦ 7) {checkoutA, checkoutB} = {{checkoutA, checkoutB}} := by
  have hA := (singleton_bounds h checkoutA).1
  have hB := (singleton_bounds h checkoutB).1
  have hpenalty := (inventory_penalty_bounds h).2.1
  rw [← checkout_penalty_eq h htriangle] at hpenalty
  unfold pairPenalty at hpenalty
  have pair_strictly_better (bundle : Bundle) (hsub : bundle ⊆ {checkoutA, checkoutB})
      (hne : bundle ≠ {checkoutA, checkoutB}) :
      surplus v (fun _ ↦ 7) bundle < surplus v (fun _ ↦ 7) {checkoutA, checkoutB} := by
    rcases subset_pair_iff.mp hsub with rfl | rfl | rfl | rfl
    · norm_num [surplus, Finset.sum_insert]
      linarith
    · norm_num [surplus, Finset.sum_insert]
      linarith
    · norm_num [surplus, Finset.sum_insert]
      linarith
    · exact (hne rfl).elim
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_demand.mpr ⟨Finset.Subset.refl _, ?_⟩, ?_⟩
  · intro bundle hsub
    by_cases heq : bundle = {checkoutA, checkoutB}
    · rw [heq]
    · exact (pair_strictly_better bundle hsub heq).le
  · intro bundle hmem
    obtain ⟨hsub, hmax⟩ := mem_demand.mp hmem
    by_contra hne
    exact (not_lt_of_ge (hmax _ (Finset.Subset.refl _))) (pair_strictly_better bundle hsub hne)

/-- A valuation with the stated checkout–inventory marginal values. -/
def exampleValue (bundle : Bundle) : ℝ :=
  10 * (bundle.card : ℝ) -
    (if checkoutA ∈ bundle ∧ inventory ∈ bundle then 2 else 0) -
    (if checkoutB ∈ bundle ∧ inventory ∈ bundle then 5 else 0) -
    (if checkoutA ∈ bundle ∧ checkoutB ∈ bundle then 2 else 0)

/-- The observation and triangle hypotheses are jointly satisfiable. -/
theorem exampleValue_valid :
    FitsObservations exampleValue ∧ HasSubstitutesTriangle exampleValue := by
  constructor
  · constructor
    · intro item
      cases item <;>
        norm_num [BracketObservation, mem_demand, Finset.subset_singleton_iff, surplus,
          probePrices, exampleValue, or_imp, forall_and]
    · norm_num [BracketObservation, mem_demand, subset_pair_iff, surplus, probePrices,
        exampleValue, Finset.sum_insert, Finset.card_insert_of_notMem, or_imp, forall_and]
    · norm_num [BracketObservation, mem_demand, subset_pair_iff, surplus, probePrices,
        exampleValue, Finset.sum_insert, Finset.card_insert_of_notMem, or_imp, forall_and]
  · norm_num [HasSubstitutesTriangle, pairPenalty, exampleValue, Finset.card_insert_of_notMem]

/-- Applying the inference to the concrete valuation recovers the joint purchase. -/
theorem exampleValue_relaxedDemand :
    demand exampleValue (fun _ ↦ 7) {checkoutA, checkoutB} = {{checkoutA, checkoutB}} :=
  relaxedDemand_eq exampleValue_valid.1 exampleValue_valid.2

end MathEconLib.Examples.Choice.RetailerSubstitution
