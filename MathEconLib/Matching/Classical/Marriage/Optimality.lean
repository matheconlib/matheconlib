/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import MathEconLib.Matching.Classical.Marriage.Existence
import MathEconLib.Matching.Contracts.StableOrder

/-!
# Both sides' optimal and pessimal stable matchings

The contracts extrema give man-optimal/woman-pessimal and
woman-optimal/man-pessimal matchings. All four specifications remain independent;
their coincidences and uniqueness are proved. Graph dictionaries also identify
the classical and contracts proofs of opposition of interests.
-/

namespace MathEconLib.Matching

open Function OrderDual

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}
variable (mkt : MarriageMarket M W)
variable [Fintype M] [Fintype W]

/-- The contracts proof gives exactly the same opposition statement as the
independent classical blocking-pair proof above. The graph dictionaries
identify the two orders, not merely the optimal outcomes. -/
theorem menWeaklyPrefer_iff_womenWeaklyPrefer_via_contracts {μ ν : M ≃. W}
    (hμ : mkt.IsStableMatching μ) (hν : mkt.IsStableMatching ν) :
    mkt.MenWeaklyPrefer μ ν ↔ mkt.WomenWeaklyPrefer ν μ := by
  rw [← mkt.sellerChosen_graphOf_iff_menWeaklyPrefer_of_individuallyRationalM hμ.1.1,
    ← mkt.buyerChosen_graphOf_iff_womenWeaklyPrefer_of_individuallyRationalW hν.1.2]
  exact mkt.toContractsMarket.sellerChosen_iff_buyerChosen
    mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket
    ((mkt.isStableMatching_iff_stable_graphOf ν).mp hν)
    ((mkt.isStableMatching_iff_stable_graphOf μ).mp hμ)

/-- The classical matching reconstructed from the man-optimal contracts outcome. -/
noncomputable def manOptimalMatching : M ≃. W :=
  mkt.matchingOfStable
    (mkt.toContractsMarket.stable_sellerOptimal
      mkt.substitutable_toContractsMarket
      mkt.consistent_toContractsMarket)

@[simp] theorem graphOf_manOptimalMatching :
    mkt.graphOf mkt.manOptimalMatching =
      mkt.toContractsMarket.sellerOptimal
        mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket :=
  mkt.graphOf_matchingOfStable
    (mkt.toContractsMarket.stable_sellerOptimal
      mkt.substitutable_toContractsMarket
      mkt.consistent_toContractsMarket)

theorem stable_manOptimalMatching :
    mkt.IsStableMatching mkt.manOptimalMatching :=
  mkt.stable_matchingOfStable
    (mkt.toContractsMarket.stable_sellerOptimal
      mkt.substitutable_toContractsMarket
      mkt.consistent_toContractsMarket)

theorem le_manOptimalMatching
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (ν m) (mkt.manOptimalMatching m) := by
  have hchosen :
      mkt.toContractsMarket.SellerChosen
        (mkt.graphOf mkt.manOptimalMatching)
        (mkt.graphOf ν) := by
    rw [mkt.graphOf_manOptimalMatching]
    exact mkt.toContractsMarket.sellerChosen_sellerOptimal
      mkt.substitutable_toContractsMarket
      mkt.consistent_toContractsMarket
      ((mkt.isStableMatching_iff_stable_graphOf ν).mp hν)
  exact mkt.menWeaklyPrefer_of_sellerChosen_graphOf hchosen m

/-- Classical man-optimality. -/
theorem exists_manOptimal_stableMatching :
    ∃ μ : M ≃. W, mkt.IsStableMatching μ ∧
      ∀ ν : M ≃. W, mkt.IsStableMatching ν →
        ∀ m, mkt.leM m (ν m) (μ m) :=
  ⟨mkt.manOptimalMatching,
    mkt.stable_manOptimalMatching,
    fun _ hν m => mkt.le_manOptimalMatching hν m⟩

/-! ### Symmetric extrema and their intrinsic characterizations -/

/-- The classical matching reconstructed from the woman-optimal contracts outcome. -/
noncomputable def womanOptimalMatching : M ≃. W :=
  mkt.matchingOfStable
    (mkt.toContractsMarket.stable_buyerOptimal
      mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket)

@[simp] theorem graphOf_womanOptimalMatching :
    mkt.graphOf mkt.womanOptimalMatching =
      mkt.toContractsMarket.buyerOptimal
        mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket :=
  mkt.graphOf_matchingOfStable _

theorem stable_womanOptimalMatching :
    mkt.IsStableMatching mkt.womanOptimalMatching :=
  mkt.stable_matchingOfStable _

theorem le_womanOptimalMatching
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (ν.symm w) (mkt.womanOptimalMatching.symm w) := by
  have hchosen :
      mkt.toContractsMarket.BuyerChosen
        (mkt.graphOf mkt.womanOptimalMatching) (mkt.graphOf ν) := by
    rw [mkt.graphOf_womanOptimalMatching]
    exact mkt.toContractsMarket.buyerChosen_buyerOptimal
      mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket
      ((mkt.isStableMatching_iff_stable_graphOf ν).mp hν)
  exact mkt.womenWeaklyPrefer_of_buyerChosen_graphOf hchosen w

/-- The woman-optimal matching is man-pessimal; this also records the
pointwise interpretation of generalized seller-pessimality. -/
theorem womanOptimalMatching_le
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (mkt.womanOptimalMatching m) (ν m) := by
  have hchosen :
      mkt.toContractsMarket.SellerChosen
        (mkt.graphOf ν) (mkt.graphOf mkt.womanOptimalMatching) := by
    rw [mkt.graphOf_womanOptimalMatching]
    exact mkt.toContractsMarket.sellerChosen_buyerOptimal
      mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket
      ((mkt.isStableMatching_iff_stable_graphOf ν).mp hν)
  exact mkt.menWeaklyPrefer_of_sellerChosen_graphOf hchosen m

/-- The man-optimal matching is woman-pessimal. -/
theorem manOptimalMatching_le
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (mkt.manOptimalMatching.symm w) (ν.symm w) := by
  have hchosen :
      mkt.toContractsMarket.BuyerChosen
        (mkt.graphOf ν) (mkt.graphOf mkt.manOptimalMatching) := by
    rw [mkt.graphOf_manOptimalMatching]
    exact mkt.toContractsMarket.buyerChosen_sellerOptimal
      mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket
      ((mkt.isStableMatching_iff_stable_graphOf ν).mp hν)
  exact mkt.womenWeaklyPrefer_of_buyerChosen_graphOf hchosen w

theorem isManOptimal_manOptimalMatching : mkt.IsManOptimal mkt.manOptimalMatching :=
  ⟨mkt.stable_manOptimalMatching, fun _ hν => mkt.le_manOptimalMatching hν⟩

theorem isWomanOptimal_womanOptimalMatching :
    mkt.IsWomanOptimal mkt.womanOptimalMatching :=
  ⟨mkt.stable_womanOptimalMatching, fun _ hν => mkt.le_womanOptimalMatching hν⟩

theorem isManPessimal_womanOptimalMatching :
    mkt.IsManPessimal mkt.womanOptimalMatching :=
  ⟨mkt.stable_womanOptimalMatching, fun _ hν => mkt.womanOptimalMatching_le hν⟩

theorem isWomanPessimal_manOptimalMatching :
    mkt.IsWomanPessimal mkt.manOptimalMatching :=
  ⟨mkt.stable_manOptimalMatching, fun _ hν => mkt.manOptimalMatching_le hν⟩

theorem exists_womanOptimal_stableMatching :
    ∃ μ : M ≃. W, mkt.IsStableMatching μ ∧
      ∀ ν : M ≃. W, mkt.IsStableMatching ν →
        ∀ w, mkt.leW w (ν.symm w) (μ.symm w) :=
  ⟨mkt.womanOptimalMatching, mkt.isWomanOptimal_womanOptimalMatching⟩

theorem exists_manPessimal_stableMatching :
    ∃ μ : M ≃. W, mkt.IsManPessimal μ :=
  ⟨mkt.womanOptimalMatching, mkt.isManPessimal_womanOptimalMatching⟩

theorem exists_womanPessimal_stableMatching :
    ∃ μ : M ≃. W, mkt.IsWomanPessimal μ :=
  ⟨mkt.manOptimalMatching, mkt.isWomanPessimal_manOptimalMatching⟩

/-- The unique stable matching worst for every man. This definition uses
its own preference specification, independently of `womanOptimalMatching`;
their equality is proved below by uniqueness. -/
noncomputable def manPessimalMatching : M ≃. W :=
  Classical.choose mkt.exists_manPessimal_stableMatching

/-- The unique stable matching worst for every woman. -/
noncomputable def womanPessimalMatching : M ≃. W :=
  Classical.choose mkt.exists_womanPessimal_stableMatching

theorem isManPessimal_manPessimalMatching :
    mkt.IsManPessimal mkt.manPessimalMatching :=
  Classical.choose_spec mkt.exists_manPessimal_stableMatching

theorem isWomanPessimal_womanPessimalMatching :
    mkt.IsWomanPessimal mkt.womanPessimalMatching :=
  Classical.choose_spec mkt.exists_womanPessimal_stableMatching

theorem stable_manPessimalMatching : mkt.IsStableMatching mkt.manPessimalMatching :=
  mkt.isManPessimal_manPessimalMatching.1

theorem stable_womanPessimalMatching : mkt.IsStableMatching mkt.womanPessimalMatching :=
  mkt.isWomanPessimal_womanPessimalMatching.1

theorem manPessimalMatching_le {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (mkt.manPessimalMatching m) (ν m) :=
  mkt.isManPessimal_manPessimalMatching.2 ν hν m

theorem womanPessimalMatching_le {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (mkt.womanPessimalMatching.symm w) (ν.symm w) :=
  mkt.isWomanPessimal_womanPessimalMatching.2 ν hν w

/-- Woman-optimality and man-pessimality select the same stable matching. -/
theorem womanOptimalMatching_eq_manPessimalMatching :
    mkt.womanOptimalMatching = mkt.manPessimalMatching :=
  IsManPessimal.unique mkt mkt.isManPessimal_womanOptimalMatching
    mkt.isManPessimal_manPessimalMatching

/-- Man-optimality and woman-pessimality select the same stable matching. -/
theorem manOptimalMatching_eq_womanPessimalMatching :
    mkt.manOptimalMatching = mkt.womanPessimalMatching :=
  IsWomanPessimal.unique mkt mkt.isWomanPessimal_manOptimalMatching
    mkt.isWomanPessimal_womanPessimalMatching

theorem le_manPessimalMatching {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (ν.symm w) (mkt.manPessimalMatching.symm w) := by
  rw [← mkt.womanOptimalMatching_eq_manPessimalMatching]
  exact mkt.le_womanOptimalMatching hν w

theorem le_womanPessimalMatching {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (ν m) (mkt.womanPessimalMatching m) := by
  rw [← mkt.manOptimalMatching_eq_womanPessimalMatching]
  exact mkt.le_manOptimalMatching hν m

theorem isManOptimal_iff_eq_manOptimalMatching (μ : M ≃. W) :
    mkt.IsManOptimal μ ↔ μ = mkt.manOptimalMatching := by
  constructor
  · exact fun h => IsManOptimal.unique mkt h mkt.isManOptimal_manOptimalMatching
  · rintro rfl
    exact mkt.isManOptimal_manOptimalMatching

theorem isWomanOptimal_iff_eq_womanOptimalMatching (μ : M ≃. W) :
    mkt.IsWomanOptimal μ ↔ μ = mkt.womanOptimalMatching := by
  constructor
  · exact fun h => IsWomanOptimal.unique mkt h mkt.isWomanOptimal_womanOptimalMatching
  · rintro rfl
    exact mkt.isWomanOptimal_womanOptimalMatching

theorem isManPessimal_iff_eq_manPessimalMatching (μ : M ≃. W) :
    mkt.IsManPessimal μ ↔ μ = mkt.manPessimalMatching := by
  constructor
  · exact fun h => IsManPessimal.unique mkt h mkt.isManPessimal_manPessimalMatching
  · rintro rfl
    exact mkt.isManPessimal_manPessimalMatching

theorem isWomanPessimal_iff_eq_womanPessimalMatching (μ : M ≃. W) :
    mkt.IsWomanPessimal μ ↔ μ = mkt.womanPessimalMatching := by
  constructor
  · exact fun h => IsWomanPessimal.unique mkt h mkt.isWomanPessimal_womanPessimalMatching
  · rintro rfl
    exact mkt.isWomanPessimal_womanPessimalMatching

/-- Swapping the two sides exchanges the optimal matchings. -/
@[simp] theorem manOptimalMatching_symm :
    mkt.symm.manOptimalMatching = mkt.womanOptimalMatching.symm := by
  apply IsManOptimal.unique mkt.symm mkt.symm.isManOptimal_manOptimalMatching
  refine ⟨(mkt.isStableMatching_symm _).mpr mkt.stable_womanOptimalMatching, ?_⟩
  intro ν hν w
  have hν' : mkt.IsStableMatching ν.symm := by
    simpa using (mkt.isStableMatching_symm ν.symm).mp hν
  simpa using mkt.le_womanOptimalMatching hν' w

@[simp] theorem womanOptimalMatching_symm :
    mkt.symm.womanOptimalMatching = mkt.manOptimalMatching.symm := by
  apply IsWomanOptimal.unique mkt.symm mkt.symm.isWomanOptimal_womanOptimalMatching
  refine ⟨(mkt.isStableMatching_symm _).mpr mkt.stable_manOptimalMatching, ?_⟩
  intro ν hν m
  have hν' : mkt.IsStableMatching ν.symm := by
    simpa using (mkt.isStableMatching_symm ν.symm).mp hν
  simpa using mkt.le_manOptimalMatching hν' m

@[simp] theorem manPessimalMatching_symm :
    mkt.symm.manPessimalMatching = mkt.womanPessimalMatching.symm := by
  rw [← mkt.symm.womanOptimalMatching_eq_manPessimalMatching,
    mkt.womanOptimalMatching_symm,
    mkt.manOptimalMatching_eq_womanPessimalMatching]

@[simp] theorem womanPessimalMatching_symm :
    mkt.symm.womanPessimalMatching = mkt.manPessimalMatching.symm := by
  rw [← mkt.symm.manOptimalMatching_eq_womanPessimalMatching,
    mkt.manOptimalMatching_symm,
    mkt.womanOptimalMatching_eq_manPessimalMatching]

end MarriageMarket

end MathEconLib.Matching
