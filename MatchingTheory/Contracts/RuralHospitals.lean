import MatchingTheory.Contracts.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card

/-!
# Rural hospitals

Substitutability, IRC, and finite-menu size monotonicity imply that every
agent signs the same number of contracts at all stable outcomes in a finite
contract market. The agent types themselves need not be finite.
-/

open Function OrderDual
open scoped BigOperators

universe u v w

variable {B : Type u} {S : Type v} {X : Type w}

private theorem sum_eq_of_le_of_sum_le {ι : Type*} {s : Finset ι} {f g : ι → ℕ}
    (hfg : ∀ i ∈ s, f i ≤ g i) (hsum : ∑ i ∈ s, g i ≤ ∑ i ∈ s, f i) :
    ∀ i ∈ s, f i = g i := by
  intro i hi
  by_contra hne
  have hlt : ∑ j ∈ s, f j < ∑ j ∈ s, g j :=
    Finset.sum_lt_sum hfg ⟨i, hi, lt_of_le_of_ne (hfg i hi) hne⟩
  exact absurd hsum (not_le.mpr hlt)

namespace Market

variable (M : Market B S X)

section Counting

variable [Finite X]

private lemma ncard_eq_sum_buyerSide (A : Set X) (T : Finset B)
    (hT : ∀ x ∈ A, M.buyer x ∈ T) :
    A.ncard = ∑ b ∈ T, (M.buyerSide b A).ncard := by
  classical
  have hAf : A.Finite := Set.toFinite A
  have h0 : A.ncard = hAf.toFinset.card := Set.ncard_eq_toFinset_card A hAf
  rw [h0, Finset.card_eq_sum_card_fiberwise
      (fun x hx => hT x (hAf.mem_toFinset.mp hx))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Set.ncard_eq_toFinset_card (M.buyerSide b A) (Set.toFinite _)]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    exact (Set.Finite.mem_toFinset _).mpr ⟨hAf.mem_toFinset.mp hx1, hx2⟩
  · intro hx
    obtain ⟨hx1, hx2⟩ := (Set.Finite.mem_toFinset _).mp hx
    exact Finset.mem_filter.mpr ⟨hAf.mem_toFinset.mpr hx1, hx2⟩

private lemma ncard_eq_sum_sellerSide (A : Set X) (T : Finset S)
    (hT : ∀ x ∈ A, M.seller x ∈ T) :
    A.ncard = ∑ s ∈ T, (M.sellerSide s A).ncard := by
  classical
  have hAf : A.Finite := Set.toFinite A
  have h0 : A.ncard = hAf.toFinset.card := Set.ncard_eq_toFinset_card A hAf
  rw [h0, Finset.card_eq_sum_card_fiberwise
      (fun x hx => hT x (hAf.mem_toFinset.mp hx))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Set.ncard_eq_toFinset_card (M.sellerSide s A) (Set.toFinite _)]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    exact (Set.Finite.mem_toFinset _).mpr ⟨hAf.mem_toFinset.mp hx1, hx2⟩
  · intro hx
    obtain ⟨hx1, hx2⟩ := (Set.Finite.mem_toFinset _).mp hx
    exact Finset.mem_filter.mpr ⟨hAf.mem_toFinset.mpr hx1, hx2⟩

/-- The counting core: `|A| = Σ_b |A_b| = Σ_s |A_s|` squeezes the two
one-sided law-of-aggregate-demand inequalities into equalities. -/
private theorem ncard_eq_aux (hload : M.SizeMonotone) {A A₀ : Set X}
    (hA : M.Stable A) (hA₀ : M.Stable A₀)
    (hbc : M.BuyerChosen A A₀) (hsc : M.SellerChosen A₀ A) :
    (∀ b, (M.buyerSide b A).ncard = (M.buyerSide b A₀).ncard) ∧
    (∀ s, (M.sellerSide s A).ncard = (M.sellerSide s A₀).ncard) := by
  classical
  have hb : ∀ b, (M.buyerSide b A₀).ncard ≤ (M.buyerSide b A).ncard := by
    intro b
    have hsub' : A₀ ⊆ A ∪ A₀ := fun x hx => Or.inr hx
    have h : (M.choiceB b A₀).ncard ≤ (M.choiceB b (A ∪ A₀)).ncard :=
      (hload.1 b).ncard_le hsub'
    rwa [hA₀.1.1 b, hbc b] at h
  have hs : ∀ s, (M.sellerSide s A).ncard ≤ (M.sellerSide s A₀).ncard := by
    intro s
    have hsub' : A ⊆ A₀ ∪ A := fun x hx => Or.inr hx
    have h : (M.choiceS s A).ncard ≤ (M.choiceS s (A₀ ∪ A)).ncard :=
      (hload.2 s).ncard_le hsub'
    rwa [hA.1.2 s, hsc s] at h
  have hfin : (A ∪ A₀).Finite := Set.toFinite _
  have hmemB : ∀ x ∈ A ∪ A₀, M.buyer x ∈ hfin.toFinset.image M.buyer :=
    fun x hx => Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hx)
  have hmemS : ∀ x ∈ A ∪ A₀, M.seller x ∈ hfin.toFinset.image M.seller :=
    fun x hx => Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hx)
  have eA1 := M.ncard_eq_sum_buyerSide A _ fun x hx => hmemB x (Or.inl hx)
  have eA2 := M.ncard_eq_sum_sellerSide A _ fun x hx => hmemS x (Or.inl hx)
  have eB1 := M.ncard_eq_sum_buyerSide A₀ _ fun x hx => hmemB x (Or.inr hx)
  have eB2 := M.ncard_eq_sum_sellerSide A₀ _ fun x hx => hmemS x (Or.inr hx)
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
    · exact (sum_eq_of_le_of_sum_le (fun b _ => hb b) hsumB.symm.le b hbT).symm
    · have e1 : M.buyerSide b A = ∅ := by
        ext x
        simp only [mem_buyerSide, Set.mem_empty_iff_false, iff_false, not_and]
        intro hx hxb
        exact hbT (hxb ▸ hmemB x (Or.inl hx))
      have e2 : M.buyerSide b A₀ = ∅ := by
        ext x
        simp only [mem_buyerSide, Set.mem_empty_iff_false, iff_false, not_and]
        intro hx hxb
        exact hbT (hxb ▸ hmemB x (Or.inr hx))
      rw [e1, e2]
  · by_cases hsT : s ∈ hfin.toFinset.image M.seller
    · exact sum_eq_of_le_of_sum_le (fun s _ => hs s) hsumS.ge s hsT
    · have e1 : M.sellerSide s A = ∅ := by
        ext x
        simp only [mem_sellerSide, Set.mem_empty_iff_false, iff_false, not_and]
        intro hx hxs
        exact hsT (hxs ▸ hmemS x (Or.inl hx))
      have e2 : M.sellerSide s A₀ = ∅ := by
        ext x
        simp only [mem_sellerSide, Set.mem_empty_iff_false, iff_false, not_and]
        intro hx hxs
        exact hsT (hxs ▸ hmemS x (Or.inr hx))
      rw [e1, e2]

theorem ncard_buyerSide_eq_of_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) (hload : M.SizeMonotone) {A A' : Set X}
    (hA : M.Stable A) (hA' : M.Stable A') (b : B) :
    (M.buyerSide b A).ncard = (M.buyerSide b A').ncard := by
  have h1 := (M.ncard_eq_aux hload hA (M.stable_sellerOptimal hsub hcons)
    (M.buyerChosen_sellerOptimal hsub hcons hA)
    (M.sellerChosen_sellerOptimal hsub hcons hA)).1 b
  have h2 := (M.ncard_eq_aux hload hA' (M.stable_sellerOptimal hsub hcons)
    (M.buyerChosen_sellerOptimal hsub hcons hA')
    (M.sellerChosen_sellerOptimal hsub hcons hA')).1 b
  rw [h1, h2]

theorem ncard_sellerSide_eq_of_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) (hload : M.SizeMonotone) {A A' : Set X}
    (hA : M.Stable A) (hA' : M.Stable A') (s : S) :
    (M.sellerSide s A).ncard = (M.sellerSide s A').ncard := by
  have h1 := (M.ncard_eq_aux hload hA (M.stable_sellerOptimal hsub hcons)
    (M.buyerChosen_sellerOptimal hsub hcons hA)
    (M.sellerChosen_sellerOptimal hsub hcons hA)).2 s
  have h2 := (M.ncard_eq_aux hload hA' (M.stable_sellerOptimal hsub hcons)
    (M.buyerChosen_sellerOptimal hsub hcons hA')
    (M.sellerChosen_sellerOptimal hsub hcons hA')).2 s
  rw [h1, h2]

/-- Rural hospitals with no redundant IRC hypothesis. On a finite contract
type, substitutability and aggregate demand imply consistency. -/
theorem ruralHospitals (hsub : M.Substitutable) (hload : M.SizeMonotone)
    {A A' : Set X} (hA : M.Stable A) (hA' : M.Stable A') :
    (∀ b, (M.buyerSide b A).ncard = (M.buyerSide b A').ncard) ∧
    (∀ s, (M.sellerSide s A).ncard = (M.sellerSide s A').ncard) := by
  have hcons := M.consistent_of_substitutable_sizeMonotone hsub hload
  exact ⟨M.ncard_buyerSide_eq_of_stable hsub hcons hload hA hA',
    M.ncard_sellerSide_eq_of_stable hsub hcons hload hA hA'⟩

end Counting

end Market
