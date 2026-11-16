/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.Distributive
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.SupClosed

/-!
# Threshold generators for the stable marriage lattice

An intrinsic ideal representation is supplied by `StableMatching.lowerSetSupIrred`.
Here a man and a partner threshold define the least stable matching meeting that
threshold, when one exists. Every join-irreducible stable matching is one of
these generators. `thresholdGenerator_le_iff` exposes the least-realization
property for feasible thresholds, and `sup_thresholdGenerator_matching`
decomposes any stable matching into its attained-threshold generators.
-/

@[expose] public section

namespace MathEconLib.Matching

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v} (mkt : MarriageMarket M W)
variable [Fintype M] [Fintype W]

namespace StableMatching

/-- Stable matchings in which man `m` gets an assignment at least `o`. -/
def MeetsThreshold (m : M) (o : Option W) (μ : mkt.StableMatching) : Prop :=
  mkt.leM m o (μ.matching m)

/-- Greatest lower bound of stable matchings meeting a coordinate threshold.
When the threshold is feasible, this is its least stable realization. -/
noncomputable def thresholdGenerator (m : M) (o : Option W) :
    mkt.StableMatching :=
  sInf {μ | MeetsThreshold mkt m o μ}

theorem thresholdGenerator_le {m : M} {o : Option W} {μ : mkt.StableMatching}
    (hμ : MeetsThreshold mkt m o μ) :
    thresholdGenerator mkt m o ≤ μ :=
  sInf_le hμ

theorem meetsThreshold_inf {m : M} {o : Option W}
    {μ ν : mkt.StableMatching}
    (hμ : MeetsThreshold mkt m o μ) (hν : MeetsThreshold mkt m o ν) :
    MeetsThreshold mkt m o (μ ⊓ ν) := by
  let := mkt.prefM m
  change o ≤ (μ ⊓ ν).matching m
  rw [matching_inf_apply]
  exact le_min hμ hν

/-- Stable matchings meeting a threshold are closed under meets. -/
theorem infClosed_meetsThreshold (m : M) (o : Option W) :
    InfClosed {μ : mkt.StableMatching | MeetsThreshold mkt m o μ} :=
  fun _ hμ _ hν => meetsThreshold_inf mkt hμ hν

/-- A feasible threshold is met by its least stable realization. -/
theorem thresholdGenerator_meets {m : M} {o : Option W}
    (hex : ∃ μ : mkt.StableMatching, MeetsThreshold mkt m o μ) :
    MeetsThreshold mkt m o (thresholdGenerator mkt m o) :=
  (infClosed_meetsThreshold mkt m o).sInf_mem_of_nonempty (Set.toFinite _) hex
    subset_rfl

/-- For a feasible threshold, its generator lies below exactly the stable
matchings that meet it. Feasibility is necessary: an infeasible threshold has
generator `⊤`, which lies below itself without meeting the threshold. -/
theorem thresholdGenerator_le_iff {m : M} {o : Option W}
    (hex : ∃ ν : mkt.StableMatching, MeetsThreshold mkt m o ν)
    (μ : mkt.StableMatching) :
    thresholdGenerator mkt m o ≤ μ ↔ MeetsThreshold mkt m o μ := by
  constructor
  · intro h
    let := mkt.prefM m
    exact (thresholdGenerator_meets mkt hex).trans
      ((le_iff_menWeaklyPrefer mkt).mp h m)
  · exact thresholdGenerator_le mkt

/-- An infeasible threshold has the empty meet, so its generator is the top
(man-optimal) stable matching, which does not meet the threshold. -/
theorem thresholdGenerator_eq_top_of_not_exists {m : M} {o : Option W}
    (hex : ¬ ∃ μ : mkt.StableMatching, MeetsThreshold mkt m o μ) :
    thresholdGenerator mkt m o = ⊤ := by
  have hempty : {μ : mkt.StableMatching | MeetsThreshold mkt m o μ} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun μ hμ => hex ⟨μ, hμ⟩
  rw [thresholdGenerator, hempty, sInf_empty]

/-- The generator meets its threshold exactly when the threshold is feasible. -/
theorem meetsThreshold_thresholdGenerator_iff {m : M} {o : Option W} :
    MeetsThreshold mkt m o (thresholdGenerator mkt m o) ↔
      ∃ μ : mkt.StableMatching, MeetsThreshold mkt m o μ :=
  ⟨fun h => ⟨_, h⟩, thresholdGenerator_meets mkt⟩

/-- The generator at an attained threshold keeps that man's assignment fixed. -/
theorem thresholdGenerator_matching (μ : mkt.StableMatching) (m : M) :
    (thresholdGenerator mkt m (μ.matching m)).matching m = μ.matching m := by
  let := mkt.prefM m
  have hmem : MeetsThreshold mkt m (μ.matching m) μ := le_rfl
  have hle := thresholdGenerator_le mkt hmem
  have hleft : mkt.leM m
      ((thresholdGenerator mkt m (μ.matching m)).matching m) (μ.matching m) :=
    (le_iff_menWeaklyPrefer mkt).mp hle m
  have hright : mkt.leM m (μ.matching m)
      ((thresholdGenerator mkt m (μ.matching m)).matching m) :=
    thresholdGenerator_meets mkt ⟨μ, hmem⟩
  exact le_antisymm hleft hright

/-- Every stable matching is the finite join of its attained-threshold
generators, one for each man. This also covers an empty population. -/
theorem sup_thresholdGenerator_matching (μ : mkt.StableMatching) :
    (Finset.univ : Finset M).sup
      (fun m => thresholdGenerator mkt m (μ.matching m)) = μ := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro m _
    apply thresholdGenerator_le mkt
    let := mkt.prefM m
    exact le_rfl
  · apply (le_iff_menWeaklyPrefer mkt).mpr
    intro m
    have hmember : thresholdGenerator mkt m (μ.matching m) ≤
        (Finset.univ : Finset M).sup
          (fun m => thresholdGenerator mkt m (μ.matching m)) :=
      Finset.le_sup (f := fun m => thresholdGenerator mkt m (μ.matching m))
        (Finset.mem_univ m)
    have hcoord := (le_iff_menWeaklyPrefer mkt).mp hmember m
    rw [thresholdGenerator_matching mkt μ m] at hcoord
    exact hcoord

/-- Every intrinsic join-irreducible has a coordinate threshold that generates it. -/
theorem exists_thresholdGenerator_eq (j : {μ : mkt.StableMatching // SupIrred μ}) :
    ∃ m : M, thresholdGenerator mkt m (j.1.matching m) = j.1 := by
  classical
  have hle : j.1 ≤
      (Finset.univ : Finset M).sup
        (fun m => thresholdGenerator mkt m (j.1.matching m)) :=
    (sup_thresholdGenerator_matching mkt j.1).ge
  obtain ⟨m, _, hj⟩ := j.2.supPrime.le_finset_sup.mp hle
  refine ⟨m, le_antisymm ?_ hj⟩
  have hmem : MeetsThreshold mkt m (j.1.matching m) j.1 := by
    let := mkt.prefM m
    exact le_rfl
  exact thresholdGenerator_le mkt hmem

/-- A canonical coordinate witness selected for a join-irreducible matching. -/
noncomputable def thresholdIndex
    (j : {μ : mkt.StableMatching // SupIrred μ}) : M × Option W :=
  let m := Classical.choose (exists_thresholdGenerator_eq mkt j)
  (m, j.1.matching m)

theorem thresholdIndex_generator
    (j : {μ : mkt.StableMatching // SupIrred μ}) :
    thresholdGenerator mkt (thresholdIndex mkt j).1 (thresholdIndex mkt j).2 = j.1 :=
  Classical.choose_spec (exists_thresholdGenerator_eq mkt j)

theorem thresholdIndex_injective :
    Function.Injective (thresholdIndex mkt) := by
  intro j k h
  apply Subtype.ext
  calc
    j.1 = thresholdGenerator mkt (thresholdIndex mkt j).1
        (thresholdIndex mkt j).2 := (thresholdIndex_generator mkt j).symm
    _ = thresholdGenerator mkt (thresholdIndex mkt k).1
        (thresholdIndex mkt k).2 := by rw [h]
    _ = k.1 := thresholdIndex_generator mkt k

/-- The intrinsic join-irreducible poset has at most one generator per
man and possible assignment. -/
theorem card_supIrred_le :
    Nat.card {μ : mkt.StableMatching // SupIrred μ} ≤
      Fintype.card M * (Fintype.card W + 1) := by
  classical
  have h := Nat.card_le_card_of_injective _ (thresholdIndex_injective mkt)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_option] using h

end StableMatching
end MarriageMarket
end MathEconLib.Matching
