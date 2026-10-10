import MathEconLib.Matching.Classical.Marriage.Translation
import MathEconLib.Matching.Contracts.RuralHospitals

/-!
# The lone-wolf theorem

The many-to-many rural-hospitals theorem specializes to invariance of the
matched agents in a marriage market. Both the matched and unmatched formulations
are supplied for each side; the woman-side results follow by side exchange.
-/

namespace MathEconLib.Matching

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
    mkt.toMarket.sellerSide m (mkt.graphOf μ) = ∅ :=
  PEquiv.graph_fiber_fst_eq_empty hμ

omit [Fintype M] [Fintype W] in
theorem sellerSide_graphOf_eq_singleton {μ : M ≃. W}
    {m : M} {w : W} (hμ : μ m = some w) :
    mkt.toMarket.sellerSide m (mkt.graphOf μ) = {(m, w)} :=
  PEquiv.graph_fiber_fst_eq_singleton hμ

omit [Fintype M] [Fintype W] in
theorem ncard_sellerSide_graphOf_eq_zero_iff
    (μ : M ≃. W) (m : M) :
    (mkt.toMarket.sellerSide m (mkt.graphOf μ)).ncard = 0 ↔
      μ m = none :=
  μ.ncard_graph_fiber_fst_eq_zero_iff m

omit [Fintype M] [Fintype W] in
theorem buyerSide_graphOf_eq_empty {μ : M ≃. W} {w : W}
    (hμ : μ.symm w = none) :
    mkt.toMarket.buyerSide w (mkt.graphOf μ) = ∅ :=
  PEquiv.graph_fiber_snd_eq_empty hμ

omit [Fintype M] [Fintype W] in
theorem buyerSide_graphOf_eq_singleton {μ : M ≃. W}
    {m : M} {w : W} (hμ : μ.symm w = some m) :
    mkt.toMarket.buyerSide w (mkt.graphOf μ) = {(m, w)} :=
  PEquiv.graph_fiber_snd_eq_singleton hμ

omit [Fintype M] [Fintype W] in
theorem ncard_buyerSide_graphOf_eq_zero_iff (μ : M ≃. W) (w : W) :
    (mkt.toMarket.buyerSide w (mkt.graphOf μ)).ncard = 0 ↔
      μ.symm w = none :=
  μ.ncard_graph_fiber_snd_eq_zero_iff w

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

end MathEconLib.Matching
