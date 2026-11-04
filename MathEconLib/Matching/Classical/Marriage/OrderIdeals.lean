/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.Distributive
public import Mathlib.Data.Fintype.Card

/-!
# Threshold generators for the stable marriage lattice

An intrinsic ideal representation is supplied by `StableMatching.lowerSetSupIrred`.
Here a man and a partner threshold define the least stable matching meeting that
threshold, when one exists. Every join-irreducible stable matching is one of
these generators.
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

/-- A feasible threshold is met by its least stable realization. -/
theorem thresholdGenerator_meets {m : M} {o : Option W}
    (hex : ∃ μ : mkt.StableMatching, MeetsThreshold mkt m o μ) :
    MeetsThreshold mkt m o (thresholdGenerator mkt m o) := by
  classical
  let : Fintype mkt.StableMatching := by
    have hinj : Function.Injective
        (fun μ : mkt.StableMatching => fun m' : M => μ.matching m') := by
      intro μ ν h
      apply ext mkt
      apply PEquiv.ext
      intro m'
      exact congrFun h m'
    have : Finite mkt.StableMatching := Finite.of_injective _ hinj
    exact Fintype.ofFinite _
  let P : mkt.StableMatching → Prop := MeetsThreshold mkt m o
  have htop : P ⊤ := by
    obtain ⟨μ, hμ⟩ := hex
    let := mkt.prefM m
    exact le_trans hμ ((le_iff_menWeaklyPrefer mkt).mp (le_top (a := μ)) m)
  have hclosed : ∀ μ ν, P μ → P ν → P (μ ⊓ ν) := by
    intro μ ν hμ hν
    exact meetsThreshold_inf mkt hμ hν
  have hfin : ∀ s : Finset mkt.StableMatching,
      (∀ μ ∈ s, P μ) → P (s.inf id) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simpa using htop
    | @insert μ s hnot ih =>
        intro hall
        rw [Finset.inf_insert]
        apply hclosed
        · exact hall μ (Finset.mem_insert_self _ _)
        · apply ih
          intro ν hν
          exact hall ν (Finset.mem_insert_of_mem hν)
  let s : Finset mkt.StableMatching := Finset.univ.filter P
  have hall : ∀ μ ∈ s, P μ := by
    intro μ hμ
    exact (Finset.mem_filter.mp hμ).2
  have hs : (s : Set mkt.StableMatching) = {μ | P μ} := by
    ext μ
    simp [s]
  have h := hfin s hall
  change P (sInf {μ | P μ})
  rw [← hs, ← Finset.inf_id_eq_sInf]
  exact h

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

/-- Every intrinsic join-irreducible has a coordinate threshold that generates it. -/
theorem exists_thresholdGenerator_eq (j : {μ : mkt.StableMatching // SupIrred μ}) :
    ∃ m : M, thresholdGenerator mkt m (j.1.matching m) = j.1 := by
  classical
  have hle : j.1 ≤
      (Finset.univ : Finset M).sup
        (fun m => thresholdGenerator mkt m (j.1.matching m)) := by
    apply (le_iff_menWeaklyPrefer mkt).mpr
    intro m
    have hmember : thresholdGenerator mkt m (j.1.matching m) ≤
        (Finset.univ : Finset M).sup
          (fun m => thresholdGenerator mkt m (j.1.matching m)) :=
      Finset.le_sup (f := fun m => thresholdGenerator mkt m (j.1.matching m))
        (Finset.mem_univ m)
    have hcoord := (le_iff_menWeaklyPrefer mkt).mp hmember m
    rw [thresholdGenerator_matching mkt j.1 m] at hcoord
    exact hcoord
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
  let : Fintype mkt.StableMatching := by
    have hinj : Function.Injective
        (fun μ : mkt.StableMatching => fun m : M => μ.matching m) := by
      intro μ ν h
      apply ext mkt
      apply PEquiv.ext
      intro m
      exact congrFun h m
    have : Finite mkt.StableMatching := Finite.of_injective _ hinj
    exact Fintype.ofFinite _
  have hcard : Fintype.card {μ : mkt.StableMatching // SupIrred μ} ≤
      Fintype.card (M × Option W) :=
    Fintype.card_le_of_injective (thresholdIndex mkt) (thresholdIndex_injective mkt)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_option] using hcard

end StableMatching
end MarriageMarket
end MathEconLib.Matching
