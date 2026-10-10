import MathEconLib.Matching.Contracts.Order
import MathEconLib.ForMathlib.Data.SetFiber

/-!
# Rural hospitals

Substitutability and finite-menu size monotonicity imply that every agent
signs the same number of contracts at all stable outcomes in a finite contract
market. These assumptions supply IRC. The agent types need not be finite.

The counting core applies to finite, individually rational outcomes in an
arbitrary contract type, when the two sides' choice comparisons have opposite
orientations. The full rural-hospitals theorem retains a finite contract type
so that the extremal outcome used for comparison is also finite.

## References

HKContractDesign2017: John William Hatfield and Scott Duke Kominers,
*Contract design and stability in many-to-many matching*, Games and Economic
Behavior **101** (2017), 78–97. Theorem 4, Appendix B (p. 95), gives
contract-count invariance under substitutability and aggregate demand;
§4.2 (p. 88) discusses the result and defines aggregate demand.
https://doi.org/10.1016/j.geb.2016.01.002

The article uses preference-induced choices. Here the public theorem assumes
a finite contract type and derives IRC from substitutability and finite-menu
size monotonicity. The conclusion concerns contract counts, not equality of
partner sets or total quantities represented by those contracts.
-/

namespace MathEconLib.Matching

open Function OrderDual
open scoped BigOperators

universe u v w

variable {B : Type u} {S : Type v} {X : Type w}

namespace Market

variable (M : Market B S X)

/-! ### Finite-menu counting -/

/-- Count contracts by their buyers, without requiring a finite contract type. -/
theorem ncard_eq_sum_buyerSide {A : Set X} (hA : A.Finite) (T : Finset B)
    (hT : ∀ x ∈ A, M.buyer x ∈ T) :
    A.ncard = ∑ b ∈ T, (M.buyerSide b A).ncard :=
  hA.ncard_eq_sum_ncard_fiber M.buyer T hT

/-- Count contracts by their sellers, without requiring a finite contract type. -/
theorem ncard_eq_sum_sellerSide {A : Set X} (hA : A.Finite) (T : Finset S)
    (hT : ∀ x ∈ A, M.seller x ∈ T) :
    A.ncard = ∑ s ∈ T, (M.sellerSide s A).ncard :=
  hA.ncard_eq_sum_ncard_fiber M.seller T hT

/-- The counting core: `|A| = Σ_b |A_b| = Σ_s |A_s|` squeezes the two
one-sided law-of-aggregate-demand inequalities into equalities. -/
theorem ncard_sides_eq_of_chosen (hload : M.SizeMonotone) {A A₀ : Set X}
    (hAfin : A.Finite) (hA₀fin : A₀.Finite)
    (hA : M.IndRational A) (hA₀ : M.IndRational A₀)
    (hbc : M.BuyerChosen A A₀) (hsc : M.SellerChosen A₀ A) :
    (∀ b, (M.buyerSide b A).ncard = (M.buyerSide b A₀).ncard) ∧
    (∀ s, (M.sellerSide s A).ncard = (M.sellerSide s A₀).ncard) := by
  classical
  have hb : ∀ b, (M.buyerSide b A₀).ncard ≤ (M.buyerSide b A).ncard := by
    intro b
    have hsub' : A₀ ⊆ A ∪ A₀ := fun x hx => Or.inr hx
    have h : (M.choiceB b A₀).ncard ≤ (M.choiceB b (A ∪ A₀)).ncard :=
      (hload.1 b).ncard_le_of_finite (hAfin.union hA₀fin) hsub'
    rwa [hA₀.1 b, hbc b] at h
  have hs : ∀ s, (M.sellerSide s A).ncard ≤ (M.sellerSide s A₀).ncard := by
    intro s
    have hsub' : A ⊆ A₀ ∪ A := fun x hx => Or.inr hx
    have h : (M.choiceS s A).ncard ≤ (M.choiceS s (A₀ ∪ A)).ncard :=
      (hload.2 s).ncard_le_of_finite (hA₀fin.union hAfin) hsub'
    rwa [hA.2 s, hsc s] at h
  have hfin : (A ∪ A₀).Finite := hAfin.union hA₀fin
  have hmemB : ∀ x ∈ A ∪ A₀, M.buyer x ∈ hfin.toFinset.image M.buyer :=
    fun x hx => Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hx)
  have hmemS : ∀ x ∈ A ∪ A₀, M.seller x ∈ hfin.toFinset.image M.seller :=
    fun x hx => Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hx)
  have eA1 := M.ncard_eq_sum_buyerSide hAfin _ fun x hx => hmemB x (Or.inl hx)
  have eA2 := M.ncard_eq_sum_sellerSide hAfin _ fun x hx => hmemS x (Or.inl hx)
  have eB1 := M.ncard_eq_sum_buyerSide hA₀fin _ fun x hx => hmemB x (Or.inr hx)
  have eB2 := M.ncard_eq_sum_sellerSide hA₀fin _ fun x hx => hmemS x (Or.inr hx)
  have hcard : A.ncard = A₀.ncard := by
    refine le_antisymm ?_ ?_
    · rw [eA2, eB2]; exact Finset.sum_le_sum fun s _ => hs s
    · rw [eB1, eA1]; exact Finset.sum_le_sum fun b _ => hb b
  have hsumB : ∑ b ∈ hfin.toFinset.image M.buyer, (M.buyerSide b A₀).ncard
      = ∑ b ∈ hfin.toFinset.image M.buyer, (M.buyerSide b A).ncard := by
    rw [← eB1, ← eA1, hcard]
  have hsumS : ∑ s ∈ hfin.toFinset.image M.seller, (M.sellerSide s A).ncard
      = ∑ s ∈ hfin.toFinset.image M.seller, (M.sellerSide s A₀).ncard := by
    rw [← eA2, ← eB2, hcard]
  refine ⟨fun b => ?_, fun s => ?_⟩
  · by_cases hbT : b ∈ hfin.toFinset.image M.buyer
    · exact ((Finset.sum_eq_sum_iff_of_le (fun b _ => hb b)).mp hsumB b hbT).symm
    · have e1 : M.buyerSide b A = ∅ :=
        Set.fiber_eq_empty_of_not_mem M.buyer
          (T := ↑(hfin.toFinset.image M.buyer))
          (fun x hx => hmemB x (Or.inl hx)) hbT
      have e2 : M.buyerSide b A₀ = ∅ :=
        Set.fiber_eq_empty_of_not_mem M.buyer
          (T := ↑(hfin.toFinset.image M.buyer))
          (fun x hx => hmemB x (Or.inr hx)) hbT
      rw [e1, e2]
  · by_cases hsT : s ∈ hfin.toFinset.image M.seller
    · exact (Finset.sum_eq_sum_iff_of_le (fun s _ => hs s)).mp hsumS s hsT
    · have e1 : M.sellerSide s A = ∅ :=
        Set.fiber_eq_empty_of_not_mem M.seller
          (T := ↑(hfin.toFinset.image M.seller))
          (fun x hx => hmemS x (Or.inl hx)) hsT
      have e2 : M.sellerSide s A₀ = ∅ :=
        Set.fiber_eq_empty_of_not_mem M.seller
          (T := ↑(hfin.toFinset.image M.seller))
          (fun x hx => hmemS x (Or.inr hx)) hsT
      rw [e1, e2]

section Counting

variable [Finite X]

/-- Rural-hospitals count invariance, with explicit IRC for callers that already
have it. The buyer and seller conclusions share the same two comparisons. -/
theorem ncard_sides_eq_of_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) (hload : M.SizeMonotone) {A A' : Set X}
    (hA : M.Stable A) (hA' : M.Stable A') :
    (∀ b, (M.buyerSide b A).ncard = (M.buyerSide b A').ncard) ∧
    (∀ s, (M.sellerSide s A).ncard = (M.sellerSide s A').ncard) := by
  have hopt := M.stable_sellerOptimal hsub hcons
  have h1 := M.ncard_sides_eq_of_chosen hload (Set.toFinite A) (Set.toFinite _)
    hA.1 hopt.1 (M.buyerChosen_sellerOptimal hsub hcons hA)
    (M.sellerChosen_sellerOptimal hsub hcons hA)
  have h2 := M.ncard_sides_eq_of_chosen hload (Set.toFinite A') (Set.toFinite _)
    hA'.1 hopt.1 (M.buyerChosen_sellerOptimal hsub hcons hA')
    (M.sellerChosen_sellerOptimal hsub hcons hA')
  exact ⟨fun b => (h1.1 b).trans (h2.1 b).symm,
    fun s => (h1.2 s).trans (h2.2 s).symm⟩

theorem ncard_buyerSide_eq_of_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) (hload : M.SizeMonotone) {A A' : Set X}
    (hA : M.Stable A) (hA' : M.Stable A') (b : B) :
    (M.buyerSide b A).ncard = (M.buyerSide b A').ncard :=
  (M.ncard_sides_eq_of_stable hsub hcons hload hA hA').1 b

theorem ncard_sellerSide_eq_of_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) (hload : M.SizeMonotone) {A A' : Set X}
    (hA : M.Stable A) (hA' : M.Stable A') (s : S) :
    (M.sellerSide s A).ncard = (M.sellerSide s A').ncard :=
  (M.ncard_sides_eq_of_stable hsub hcons hload hA hA').2 s

/-- Rural hospitals with no redundant IRC hypothesis. On a finite contract
domain, substitutability and the law of aggregate demand imply consistency.
The count-invariance conclusion is HKContractDesign2017, Theorem 4,
Appendix B (p. 95). -/
theorem ruralHospitals (hsub : M.Substitutable) (hload : M.SizeMonotone)
    {A A' : Set X} (hA : M.Stable A) (hA' : M.Stable A') :
    (∀ b, (M.buyerSide b A).ncard = (M.buyerSide b A').ncard) ∧
    (∀ s, (M.sellerSide s A).ncard = (M.sellerSide s A').ncard) := by
  have hcons := M.consistent_of_substitutable_sizeMonotone hsub hload
  exact M.ncard_sides_eq_of_stable hsub hcons hload hA hA'

end Counting

end Market

end MathEconLib.Matching
