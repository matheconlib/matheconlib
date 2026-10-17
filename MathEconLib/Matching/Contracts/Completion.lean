/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import MathEconLib.Matching.Contracts.ManyToOne
import MathEconLib.Matching.Contracts.WeakSubstitutes
import MathEconLib.Matching.Contracts.StableFixedPoints

/-!
# Stable outcomes from substitutable completions

Replace buyer choices by one jointly substitutable and IRC completion per
buyer, leaving seller choices and contract assignments unchanged. Support of
the completed choices follows from the existing choice-level support theorem.
Completions may choose several contracts with one seller off equilibrium.
Seller unit demand nevertheless makes every individually rational outcome
feasible, so original and completed choices agree at that outcome.

For nonblocking, use the menu of all contracts sellers would accept alongside
the outcome. Completed buyers choose exactly their outcome contracts from
this menu. Their choices are therefore feasible, so the original buyers agree
there too. Original IRC then rules out every original blocking set. This
argument does not assume pointwise enlargement of choices or equality of the
two stable sets.

The transfer and completion-based existence results allow arbitrary contract
and agent types under explicit set-form IRC. The unilateral-substitutability
corollary uses finite-valued buyer choices; a finite-contract version follows.
No law of aggregate demand is required. Outcome independence and comparison
with cumulative offers remain separate results in issues #138–139.

## References

John William Hatfield and Scott Duke Kominers (2025), *The theory of matching
with contracts*, Handbook of the Economics of Matching 2, 409–487,
§6.1, Theorems 6.1–6.2, pp. 471–472.
https://doi.org/10.1016/bs.hesmat.2025.10.005.
The source assumes IRC throughout. Here original IRC and IRC of the same
completion that satisfies substitutability are explicit hypotheses.
-/

namespace MathEconLib.Matching

open MathEconLib.Choice

namespace Market

variable {B S X : Type*} (M : Market B S X)

/-- Replace buyer choices by specified substitutable completions. Seller
choices and both contract-assignment maps are preserved. -/
def withBuyerCompletions (D : B → ChoiceFunction X)
    (hcomp : ∀ b, (M.choiceB b).IsCompletionOf M.seller (D b))
    (hsub : ∀ b, (D b).Substitutable) : Market B S X where
  buyer := M.buyer
  seller := M.seller
  choiceB := D
  choiceS := M.choiceS
  buyer_eq_of_mem := fun {b _ _} hx =>
    M.buyer_eq_of_mem_completion (hcomp b) (hsub b) hx
  seller_eq_of_mem := M.seller_eq_of_mem

variable (D : B → ChoiceFunction X)
    (hcomp : ∀ b, (M.choiceB b).IsCompletionOf M.seller (D b))
    (hsub : ∀ b, (D b).Substitutable)

/-- Original and completed individual rationality coincide on feasible outcomes.
No IRC or substitutability of original choices is used. -/
theorem indRational_withBuyerCompletions_iff {A : Set X}
    (hA : M.ManyToOneFeasible A) :
    (M.withBuyerCompletions D hcomp hsub).IndRational A ↔ M.IndRational A := by
  have heq : ∀ b, D b A = M.choiceB b A :=
    fun b => (hcomp b).eq_of_injOn_menu hA
  change ((∀ b, D b A = M.buyerSide b A) ∧
    ∀ s, M.choiceS s A = M.sellerSide s A) ↔ _
  simp only [heq, IndRational]

/-- Every stable completed outcome is stable in the original market.
The original buyers need IRC, but need not be substitutable. -/
theorem stable_of_withBuyerCompletions
    (hunit : M.SellersUnitDemand) (hcons : M.Consistent)
    (hDcons : ∀ b, (D b).Consistent) {A : Set X}
    (hA : (M.withBuyerCompletions D hcomp hsub).Stable A) : M.Stable A := by
  let N := M.withBuyerCompletions D hcomp hsub
  have hNsub : N.Substitutable :=
    ⟨hsub, hunit.substitutable M hcons.2⟩
  have hNcons : N.Consistent := ⟨hDcons, hcons.2⟩
  have hfeas : M.ManyToOneFeasible A :=
    hA.manyToOneFeasible N hunit
  have hIR : M.IndRational A :=
    (M.indRational_withBuyerCompletions_iff D hcomp hsub hfeas).mp hA.1
  have hAV : A ⊆ N.toBuyers A := N.subset_toBuyers_of_indRational hA.1
  have hDV : ∀ b, D b (N.toBuyers A) = M.buyerSide b A := by
    intro b
    exact (N.choiceB_eq_of_stable hNsub hNcons hA b
      (Set.Subset.refl A) hAV (fun _ hy _ => hy)).trans (hA.1.1 b)
  have hCV : ∀ b, M.choiceB b (N.toBuyers A) = M.buyerSide b A := by
    intro b
    have hfeasD : Set.InjOn M.seller (D b (N.toBuyers A)) := by
      rw [hDV b]
      intro x hx y hy hxy
      exact hfeas hx.1 hy.1 hxy
    rw [← (hcomp b).eq_of_injOn hfeasD, hDV b]
  refine ⟨hIR, ?_⟩
  intro Z hZ
  obtain ⟨hne, hdisj, hB, hS⟩ := hZ
  have hZV : Z ⊆ N.toBuyers A := by
    intro z hz
    have hzS := hS (M.seller z) (show z ∈ M.sellerSide (M.seller z) Z from ⟨hz, rfl⟩)
    exact (hNsub.2 (M.seller z)).mem_of_subset
      (Set.insert_subset_iff.mpr ⟨Or.inr hz, Set.subset_union_left⟩)
      hzS (Set.mem_insert _ _)
  have hC : ∀ b, M.choiceB b (A ∪ Z) = M.buyerSide b A := by
    intro b
    have hchosen : M.choiceB b (N.toBuyers A) ⊆ A ∪ Z := by
      rw [hCV b]
      exact fun _ hx => Or.inl hx.1
    exact (hcons.1 b hchosen (Set.union_subset hAV hZV)).trans (hCV b)
  obtain ⟨z, hz⟩ := hne
  have hzC := hB (M.buyer z) (show z ∈ M.buyerSide (M.buyer z) Z from ⟨hz, rfl⟩)
  rw [hC] at hzC
  exact Set.disjoint_left.mp hdisj hz hzC.1

omit D hcomp hsub in
/-- Consistent choices with unit-demand sellers admit a feasible stable outcome
whenever each buyer has one substitutable completion satisfying IRC. -/
theorem exists_stable_of_buyerCompletions
    (hunit : M.SellersUnitDemand) (hcons : M.Consistent)
    (hcomp : M.BuyersHaveConsistentSubstitutableCompletions) :
    ∃ A : Set X, M.Stable A ∧ M.ManyToOneFeasible A := by
  classical
  choose D hDcomp hDsub hDcons using hcomp
  let N := M.withBuyerCompletions D hDcomp hDsub
  obtain ⟨A, hA⟩ := N.exists_stable
    ⟨hDsub, hunit.substitutable M hcons.2⟩ ⟨hDcons, hcons.2⟩
  exact ⟨A, M.stable_of_withBuyerCompletions D hDcomp hDsub hunit hcons hDcons hA,
    hA.manyToOneFeasible N hunit⟩

omit D hcomp hsub in
/-- Finite-valued unilateral substitutes on the accepting side give stable
existence. Agent and contract types may be infinite. -/
theorem exists_stable_of_buyersUnilaterallySubstitutable_of_finiteValued
    (hunit : M.SellersUnitDemand) (hcons : M.Consistent)
    (hfeas : M.BuyersCounterpartyFeasible)
    (hUS : M.BuyersUnilaterallySubstitutable)
    (hfinite : ∀ b, (M.choiceB b).FiniteValued) :
    ∃ A : Set X, M.Stable A ∧ M.ManyToOneFeasible A :=
  M.exists_stable_of_buyerCompletions hunit hcons
    (M.buyersHaveConsistentSubstitutableCompletions_of_unilaterallySubstitutable_of_finiteValued
      hUS hcons.1 hfeas hfinite)

omit D hcomp hsub in
/-- Finite-contract specialization of stable existence under unilateral
substitutability and IRC. No law of aggregate demand is assumed. -/
theorem exists_stable_of_buyersUnilaterallySubstitutable [Finite X]
    (hunit : M.SellersUnitDemand) (hcons : M.Consistent)
    (hfeas : M.BuyersCounterpartyFeasible)
    (hUS : M.BuyersUnilaterallySubstitutable) :
    ∃ A : Set X, M.Stable A ∧ M.ManyToOneFeasible A :=
  M.exists_stable_of_buyersUnilaterallySubstitutable_of_finiteValued
    hunit hcons hfeas hUS (fun _ _ => Set.toFinite _)

end Market

end MathEconLib.Matching
