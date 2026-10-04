import MatchingTheory.Classical.Marriage.Translation
import MatchingTheory.Contracts.RuralHospitals

/-!
# The lone-wolf theorem

The many-to-many rural-hospitals theorem specializes to invariance of the
matched agents in a marriage market. Both the matched and unmatched formulations
are supplied for each side; the woman-side results follow by side exchange.
-/

open Function OrderDual

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}
variable (mkt : MarriageMarket M W)
variable [Fintype M] [Fintype W]

/-! ## Lone wolf -/

omit [Fintype M] [Fintype W] in
theorem sellerSide_graphOf_eq_empty {μ : M ≃. W} {m : M}
    (hμ : μ m = none) :
    mkt.toMarket.sellerSide m (mkt.graphOf μ) = ∅ := by
  ext p
  rcases p with ⟨m', w⟩
  simp only [Market.mem_sellerSide, mem_graphOf, toMarket_seller,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro hp rfl
  rw [hμ] at hp
  contradiction

omit [Fintype M] [Fintype W] in
theorem sellerSide_graphOf_eq_singleton {μ : M ≃. W}
    {m : M} {w : W} (hμ : μ m = some w) :
    mkt.toMarket.sellerSide m (mkt.graphOf μ) = {(m, w)} := by
  ext p
  rcases p with ⟨m', w'⟩
  constructor
  · rintro ⟨hp, hm'⟩
    obtain rfl : m = m' := hm'.symm
    have hpEq : μ m = some w' := mkt.mem_graphOf.mp hp
    have hww' : w = w' := Option.some.inj (hμ.symm.trans hpEq)
    subst hww'
    rfl
  · intro hp
    have hp' : (m', w') = (m, w) := hp
    rw [Prod.mk.injEq] at hp'
    obtain ⟨rfl, rfl⟩ := hp'
    exact ⟨mkt.mem_graphOf.mpr hμ, rfl⟩

omit [Fintype M] [Fintype W] in
theorem ncard_sellerSide_graphOf_eq_zero_iff
    (μ : M ≃. W) (m : M) :
    (mkt.toMarket.sellerSide m (mkt.graphOf μ)).ncard = 0 ↔
      μ m = none := by
  cases hμ : μ m with
  | none =>
      rw [mkt.sellerSide_graphOf_eq_empty hμ]
      simp
  | some w =>
      rw [mkt.sellerSide_graphOf_eq_singleton hμ]
      simp

omit [Fintype M] [Fintype W] in
theorem buyerSide_graphOf_eq_empty {μ : M ≃. W} {w : W}
    (hμ : μ.symm w = none) :
    mkt.toMarket.buyerSide w (mkt.graphOf μ) = ∅ := by
  ext p
  rcases p with ⟨m, w'⟩
  constructor
  · rintro ⟨hp, hw'⟩
    obtain rfl : w = w' := hw'.symm
    have hm : μ.symm w = some m := mkt.mem_graphOf_symm.mp hp
    rw [hμ] at hm
    cases hm
  · intro hp
    exact hp.elim

omit [Fintype M] [Fintype W] in
theorem buyerSide_graphOf_eq_singleton {μ : M ≃. W}
    {m : M} {w : W} (hμ : μ.symm w = some m) :
    mkt.toMarket.buyerSide w (mkt.graphOf μ) = {(m, w)} := by
  ext p
  rcases p with ⟨m', w'⟩
  constructor
  · rintro ⟨hp, hw'⟩
    obtain rfl : w = w' := hw'.symm
    have hpEq : μ.symm w = some m' := mkt.mem_graphOf_symm.mp hp
    have hmm' : m = m' := Option.some.inj (hμ.symm.trans hpEq)
    subst hmm'
    rfl
  · intro hp
    have hp' : (m', w') = (m, w) := hp
    rw [Prod.mk.injEq] at hp'
    obtain ⟨rfl, rfl⟩ := hp'
    exact ⟨mkt.mem_graphOf_symm.mpr hμ, rfl⟩

omit [Fintype M] [Fintype W] in
theorem ncard_buyerSide_graphOf_eq_zero_iff (μ : M ≃. W) (w : W) :
    (mkt.toMarket.buyerSide w (mkt.graphOf μ)).ncard = 0 ↔
      μ.symm w = none := by
  cases hμ : μ.symm w with
  | none =>
      rw [mkt.buyerSide_graphOf_eq_empty hμ]
      simp
  | some m =>
      rw [mkt.buyerSide_graphOf_eq_singleton hμ]
      simp

/-- The outside-option form of the rural-hospitals specialization. -/
theorem eq_none_iff_of_stable {μ ν : M ≃. W}
    (hμ : mkt.IsStableMatching μ) (hν : mkt.IsStableMatching ν) (m : M) :
    μ m = none ↔ ν m = none := by
  have hcard := mkt.toMarket.ncard_sellerSide_eq_of_stable
    mkt.substitutable_toMarket mkt.consistent_toMarket mkt.sizeMonotone_toMarket
    ((mkt.isStableMatching_iff_stable_graphOf μ).mp hμ)
    ((mkt.isStableMatching_iff_stable_graphOf ν).mp hν) m
  rw [← mkt.ncard_sellerSide_graphOf_eq_zero_iff μ m,
    ← mkt.ncard_sellerSide_graphOf_eq_zero_iff ν m, hcard]

/-- Lone wolf: a man is matched in one stable matching iff he is matched in
 every stable matching. -/
theorem isSome_iff_of_stable {μ ν : M ≃. W}
    (hμ : mkt.IsStableMatching μ) (hν : mkt.IsStableMatching ν) (m : M) :
    (μ m).isSome ↔ (ν m).isSome := by
  have hnone := mkt.eq_none_iff_of_stable hμ hν m
  cases hμm : μ m <;> cases hνm : ν m <;> simp_all

/-- The outside-option statement for women follows by side exchange. -/
theorem eq_none_symm_iff_of_stable {μ ν : M ≃. W}
    (hμ : mkt.IsStableMatching μ) (hν : mkt.IsStableMatching ν) (w : W) :
    μ.symm w = none ↔ ν.symm w = none :=
  mkt.symm.eq_none_iff_of_stable
    ((mkt.isStableMatching_symm μ).mpr hμ)
    ((mkt.isStableMatching_symm ν).mpr hν) w

/-- Lone wolf for women, obtained from the same theorem after side exchange. -/
theorem isSome_symm_iff_of_stable {μ ν : M ≃. W}
    (hμ : mkt.IsStableMatching μ) (hν : mkt.IsStableMatching ν) (w : W) :
    (μ.symm w).isSome ↔ (ν.symm w).isSome :=
  mkt.symm.isSome_iff_of_stable (μ := μ.symm) (ν := ν.symm)
    ((mkt.isStableMatching_symm μ).mpr hμ)
    ((mkt.isStableMatching_symm ν).mpr hν) w

end MarriageMarket
