import MathEconLib.Matching.Classical.Marriage.Optimality
import Mathlib.Order.CompleteLattice.Basic

/-!
# The lattice of stable marriage matchings

`MarriageMarket.StableMatching` packages a classical partial matching and
its stability proof. Its complete lattice is transported from the general
contracts fixed-point lattice. No order instance on bare `PEquiv` is changed.

The orientation is the same as in the contracts theory: `μ ≤ ν` means that
all men weakly prefer `ν` to `μ`, equivalently that all women weakly prefer
`μ` to `ν`. Thus top is man-optimal/woman-pessimal and bottom is
woman-optimal/man-pessimal. Exchanging the two sides reverses the order.
-/

namespace MathEconLib.Matching

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}

/-- A stable matching with its own economic order, separate from the
extension order on the underlying partial equivalence. -/
structure StableMatching (mkt : MarriageMarket M W) where
  matching : M ≃. W
  isStable : mkt.IsStableMatching matching

namespace StableMatching

variable (mkt : MarriageMarket M W)

@[ext] theorem ext {μ ν : mkt.StableMatching}
    (h : μ.matching = ν.matching) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

/-- Side exchange acts on stable matchings without any finiteness assumption. -/
def symmEquiv : mkt.StableMatching ≃ mkt.symm.StableMatching where
  toFun μ := ⟨μ.matching.symm,
    (mkt.isStableMatching_symm μ.matching).mpr μ.isStable⟩
  invFun ν := ⟨ν.matching.symm, by
    have h := (mkt.isStableMatching_symm ν.matching.symm).mp
    exact h (by simpa only [PEquiv.symm_symm] using ν.isStable)⟩
  left_inv μ := by
    apply ext
    exact PEquiv.symm_symm μ.matching
  right_inv ν := by
    apply ext
    exact PEquiv.symm_symm ν.matching

@[simp] theorem matching_symmEquiv (μ : mkt.StableMatching) :
    (symmEquiv mkt μ).matching = μ.matching.symm := rfl

variable [Fintype M] [Fintype W]

/-- The stability translation, packaged as an equivalence of carriers. -/
noncomputable def graphEquiv :
    mkt.StableMatching ≃ {A : Set (M × W) // mkt.toMarket.Stable A} where
  toFun μ := ⟨mkt.graphOf μ.matching,
    (mkt.isStableMatching_iff_stable_graphOf μ.matching).mp μ.isStable⟩
  invFun A := ⟨mkt.matchingOfStable A.2, mkt.stable_matchingOfStable A.2⟩
  left_inv μ := by
    apply ext
    exact mkt.matchingOfStable_graphOf μ.isStable
  right_inv A := Subtype.ext (mkt.graphOf_matchingOfStable A.2)

/-- Stable classical matchings and the general fixed-point lattice have
the same carrier through the graph and fixed-point correspondences. -/
noncomputable def contractsEquiv :
    mkt.StableMatching ≃ mkt.toMarket.StableOutcomes mkt.substitutable_toMarket :=
  (graphEquiv mkt).trans
    (mkt.toMarket.stableEquivFixedPoints
      mkt.substitutable_toMarket mkt.consistent_toMarket)

/-- The classical lattice is an instance of the general contracts lattice. -/
noncomputable instance : CompleteLattice mkt.StableMatching := by
  let e := contractsEquiv mkt
  letI : PartialOrder mkt.StableMatching :=
    { le := fun μ ν => e μ ≤ e ν
      le_refl := fun _ => le_rfl
      le_trans := fun _ _ _ hμν hνω => le_trans hμν hνω
      le_antisymm := fun _ _ hμν hνμ =>
        e.injective (le_antisymm hμν hνμ) }
  letI : SupSet mkt.StableMatching :=
    ⟨fun S => e.symm (sSup (e '' S))⟩
  refine completeLatticeOfSup mkt.StableMatching ?_
  intro S
  constructor
  · intro μ hμ
    change e μ ≤ e (e.symm (sSup (e '' S)))
    rw [e.apply_symm_apply]
    exact le_sSup ⟨μ, hμ, rfl⟩
  · intro μ hμ
    change e (e.symm (sSup (e '' S))) ≤ e μ
    rw [e.apply_symm_apply]
    apply sSup_le
    rintro _ ⟨ν, hν, rfl⟩
    exact hμ hν

/-- The carrier equivalence preserves the transported lattice order. -/
noncomputable def contractsOrderIso :
    mkt.StableMatching ≃o mkt.toMarket.StableOutcomes mkt.substitutable_toMarket where
  toEquiv := contractsEquiv mkt
  map_rel_iff' := Iff.rfl

@[simp] theorem outcome_contractsEquiv (μ : mkt.StableMatching) :
    (contractsEquiv mkt μ).outcome = mkt.graphOf μ.matching := by
  change (mkt.toMarket.ofStable mkt.substitutable_toMarket mkt.consistent_toMarket
    ((mkt.isStableMatching_iff_stable_graphOf μ.matching).mp μ.isStable)).outcome = _
  exact mkt.toMarket.outcome_ofStable
    mkt.substitutable_toMarket mkt.consistent_toMarket _

/-- Increasing in the lattice means weak improvement for every man. -/
theorem le_iff_menWeaklyPrefer {μ ν : mkt.StableMatching} :
    μ ≤ ν ↔ mkt.MenWeaklyPrefer ν.matching μ.matching := by
  change contractsEquiv mkt μ ≤ contractsEquiv mkt ν ↔ _
  rw [Market.StableOutcomes.le_iff_sellerChosen mkt.consistent_toMarket,
    outcome_contractsEquiv, outcome_contractsEquiv]
  exact mkt.sellerChosen_graphOf_iff_menWeaklyPrefer_of_individuallyRationalM
    ν.isStable.1.1

/-- Increasing in the lattice means weak deterioration for every woman. -/
theorem le_iff_womenWeaklyPrefer {μ ν : mkt.StableMatching} :
    μ ≤ ν ↔ mkt.WomenWeaklyPrefer μ.matching ν.matching := by
  change contractsEquiv mkt μ ≤ contractsEquiv mkt ν ↔ _
  rw [Market.StableOutcomes.le_iff_buyerChosen mkt.consistent_toMarket,
    outcome_contractsEquiv, outcome_contractsEquiv]
  exact mkt.buyerChosen_graphOf_iff_womenWeaklyPrefer_of_individuallyRationalW
    μ.isStable.1.2

/-- The top of the stable-matching lattice is the man-optimal matching. -/
@[simp] theorem matching_top :
    (⊤ : mkt.StableMatching).matching = mkt.manOptimalMatching := by
  apply (mkt.isManOptimal_iff_eq_manOptimalMatching _).mp
  refine ⟨(⊤ : mkt.StableMatching).isStable, ?_⟩
  intro μ hμ
  exact (le_iff_menWeaklyPrefer mkt).mp
    (le_top (a := (⟨μ, hμ⟩ : mkt.StableMatching)))

/-- The bottom of the stable-matching lattice is the woman-optimal matching. -/
@[simp] theorem matching_bot :
    (⊥ : mkt.StableMatching).matching = mkt.womanOptimalMatching := by
  apply (mkt.isWomanOptimal_iff_eq_womanOptimalMatching _).mp
  refine ⟨(⊥ : mkt.StableMatching).isStable, ?_⟩
  intro μ hμ
  exact (le_iff_womenWeaklyPrefer mkt).mp
    (bot_le (a := (⟨μ, hμ⟩ : mkt.StableMatching)))

/-- The same top is woman-pessimal. -/
theorem matching_top_eq_womanPessimalMatching :
    (⊤ : mkt.StableMatching).matching = mkt.womanPessimalMatching :=
  (matching_top mkt).trans mkt.manOptimalMatching_eq_womanPessimalMatching

/-- The same bottom is man-pessimal. -/
theorem matching_bot_eq_manPessimalMatching :
    (⊥ : mkt.StableMatching).matching = mkt.manPessimalMatching :=
  (matching_bot mkt).trans mkt.womanOptimalMatching_eq_manPessimalMatching

/-- Side exchange is an order isomorphism to the opposite lattice. -/
noncomputable def symmOrderIso :
    mkt.StableMatching ≃o (mkt.symm.StableMatching)ᵒᵈ where
  toEquiv := symmEquiv mkt
  map_rel_iff' := by
    intro μ ν
    change symmEquiv mkt ν ≤ symmEquiv mkt μ ↔ μ ≤ ν
    constructor
    · intro h
      have hw : mkt.WomenWeaklyPrefer μ.matching ν.matching :=
        (le_iff_menWeaklyPrefer mkt.symm).mp h
      exact (le_iff_womenWeaklyPrefer mkt).mpr hw
    · intro h
      have hw := (le_iff_womenWeaklyPrefer mkt).mp h
      exact (le_iff_menWeaklyPrefer mkt.symm).mpr hw

/-- The join is the least stable upper bound in the men's economic order. -/
theorem menWeaklyPrefer_sup_iff (μ ν ω : mkt.StableMatching) :
    mkt.MenWeaklyPrefer ω.matching (μ ⊔ ν).matching ↔
      mkt.MenWeaklyPrefer ω.matching μ.matching ∧
        mkt.MenWeaklyPrefer ω.matching ν.matching := by
  rw [← le_iff_menWeaklyPrefer, ← le_iff_menWeaklyPrefer,
    ← le_iff_menWeaklyPrefer]
  exact sup_le_iff

/-- The meet is the least stable upper bound in the women's economic order. -/
theorem womenWeaklyPrefer_inf_iff (μ ν ω : mkt.StableMatching) :
    mkt.WomenWeaklyPrefer ω.matching (μ ⊓ ν).matching ↔
      mkt.WomenWeaklyPrefer ω.matching μ.matching ∧
        mkt.WomenWeaklyPrefer ω.matching ν.matching := by
  rw [← le_iff_womenWeaklyPrefer, ← le_iff_womenWeaklyPrefer,
    ← le_iff_womenWeaklyPrefer]
  exact le_inf_iff

end StableMatching

end MarriageMarket

end MathEconLib.Matching
