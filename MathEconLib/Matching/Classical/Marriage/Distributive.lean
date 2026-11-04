/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.StableOrder
public import MathEconLib.Matching.Classical.Marriage.LoneWolf
public import Mathlib.Order.Birkhoff

/-!
# Distributivity of the stable marriage lattice

The order is the men's preference order. For finite populations, lattice join
and meet choose each man's better and worse assignment, respectively. These
formulas give a distributive lattice on the existing `StableMatching` type,
without changing its order or its previously defined lattice operations.

`lowerSetSupIrred` then applies Mathlib's finite Birkhoff representation theorem:
stable matchings are order-isomorphic to lower sets of their join-irreducible
elements. This is an intrinsic representation, not a rotation enumeration or
an algorithmic complexity theorem.

Preferences are strict orders over partners and the outside option. Populations
may have different sizes and some partners may be unacceptable. The proof uses
the existing lone-wolf theorem to handle unmatched participants.

## References

Alvin E. Roth and Marilda A. Oliveira Sotomayor (1990),
*Two-Sided Matching: A Study in Game-Theoretic Modeling and Analysis*,
Cambridge University Press, Chapter 3, "The structure of the set of stable matchings".
[Publisher](https://www.cambridge.org/core/books/twosided-matching/FF14E482078F3DBD8D82A50581C110C0).
The pointwise lattice operations are classical; the representation uses
`OrderIso.lowerSetSupIrred` from Mathlib.
-/

@[expose] public section

namespace MathEconLib.Matching

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v} (mkt : MarriageMarket M W)

namespace StableMatching

/-- A partial matching bijects its matched participants on the two sides. -/
private noncomputable def matchedEquiv (ρ : M ≃. W) :
    {m : M // (ρ m).isSome} ≃ {w : W // (ρ.symm w).isSome} where
  toFun x := ⟨(ρ x.1).get x.2, by
    have hx : ρ x.1 = some ((ρ x.1).get x.2) := (Option.coe_get x.2).symm
    rw [ρ.eq_some_iff.mpr hx]
    rfl⟩
  invFun y := ⟨(ρ.symm y.1).get y.2, by
    have hy : ρ.symm y.1 = some ((ρ.symm y.1).get y.2) := (Option.coe_get y.2).symm
    rw [ρ.eq_some_iff.mp hy]
    rfl⟩
  left_inv x := by
    apply Subtype.ext
    have hx : ρ x.1 = some ((ρ x.1).get x.2) := (Option.coe_get x.2).symm
    simp [ρ.eq_some_iff.mpr hx]
  right_inv y := by
    apply Subtype.ext
    have hy : ρ.symm y.1 = some ((ρ.symm y.1).get y.2) := (Option.coe_get y.2).symm
    simp [ρ.eq_some_iff.mp hy]

/-- The better of two assignments according to man `m`. -/
noncomputable def preferredM (μ ν : mkt.StableMatching) (m : M) : Option W := by
  letI := mkt.prefM m
  exact max (μ.matching m) (ν.matching m)

theorem le_preferredM_left (μ ν : mkt.StableMatching) (m : M) :
    mkt.leM m (μ.matching m) (preferredM mkt μ ν m) := by
  let := mkt.prefM m
  exact le_max_left _ _

theorem le_preferredM_right (μ ν : mkt.StableMatching) (m : M) :
    mkt.leM m (ν.matching m) (preferredM mkt μ ν m) := by
  let := mkt.prefM m
  exact le_max_right _ _

theorem preferredM_eq_left_or_right (μ ν : mkt.StableMatching) (m : M) :
    preferredM mkt μ ν m = μ.matching m ∨
      preferredM mkt μ ν m = ν.matching m := by
  let := mkt.prefM m
  rcases le_total (μ.matching m) (ν.matching m) with h | h
  · right
    exact max_eq_right h
  · left
    exact max_eq_left h

theorem preferredM_rightUnique (μ ν : mkt.StableMatching) (m : M)
    {w w' : W} (hw : preferredM mkt μ ν m = some w)
    (hw' : preferredM mkt μ ν m = some w') : w = w' :=
  Option.some.inj (hw.symm.trans hw')

/-- Crossed preferred choices cannot assign one woman twice. -/
private theorem preferredM_crossUnique (μ ν : mkt.StableMatching)
    {m m' : M} {w : W}
    (hmw : μ.matching m = some w) (hm'w : ν.matching m' = some w)
    (hμ : preferredM mkt μ ν m = some w)
    (hν : preferredM mkt μ ν m' = some w) : m = m' := by
  let := mkt.prefW w
  by_contra hne
  have hνm : ν.matching m ≠ some w := by
    intro heq
    exact hne (ν.matching.graph_leftUnique heq hm'w)
  have hμm' : μ.matching m' ≠ some w := by
    intro heq
    exact hne (μ.matching.graph_leftUnique heq hmw).symm
  have hltν : mkt.ltM m (ν.matching m) (some w) := by
    let := mkt.prefM m
    have hle : mkt.leM m (ν.matching m) (some w) := by
      simpa only [hμ] using (le_preferredM_right mkt μ ν m)
    exact lt_of_le_of_ne hle hνm
  have hltμ : mkt.ltM m' (μ.matching m') (some w) := by
    let := mkt.prefM m'
    have hle : mkt.leM m' (μ.matching m') (some w) := by
      simpa only [hν] using (le_preferredM_left mkt μ ν m')
    exact lt_of_le_of_ne hle hμm'
  have hνle : mkt.leW w (some m) (some m') := by
    have hnot := ν.isStable.2.1 m w
    have hle : mkt.leW w (some m) (ν.matching.symm w) :=
      le_of_not_gt (fun h => hnot ⟨hltν, h⟩)
    simpa only [ν.matching.eq_some_iff.mpr hm'w] using hle
  have hμle : mkt.leW w (some m') (some m) := by
    have hnot := μ.isStable.2.1 m' w
    have hle : mkt.leW w (some m') (μ.matching.symm w) :=
      le_of_not_gt (fun h => hnot ⟨hltμ, h⟩)
    simpa only [μ.matching.eq_some_iff.mpr hmw] using hle
  exact hne (Option.some.inj (le_antisymm hνle hμle))

/-- Two men cannot choose the same woman from two stable matchings. -/
theorem preferredM_leftUnique (μ ν : mkt.StableMatching) (w : W)
    {m m' : M} (hm : preferredM mkt μ ν m = some w)
    (hm' : preferredM mkt μ ν m' = some w) : m = m' := by
  rcases preferredM_eq_left_or_right mkt μ ν m with hμ | hν <;>
    rcases preferredM_eq_left_or_right mkt μ ν m' with hμ' | hν'
  · exact μ.matching.graph_leftUnique (hμ.symm.trans hm) (hμ'.symm.trans hm')
  · exact preferredM_crossUnique mkt μ ν (hμ.symm.trans hm) (hν'.symm.trans hm')
      hm hm'
  · exact preferredM_crossUnique mkt ν μ (hν.symm.trans hm)
      (hμ'.symm.trans hm')
      (by simpa [preferredM, max_comm] using hm)
      (by simpa [preferredM, max_comm] using hm')
  · exact ν.matching.graph_leftUnique (hν.symm.trans hm) (hν'.symm.trans hm')

/-- The pointwise preferred assignment is a partial matching. -/
noncomputable def preferredMatching (μ ν : mkt.StableMatching) : M ≃. W :=
  PEquiv.ofRelation (fun m w => preferredM mkt μ ν m = some w)
    (fun m _ hw _ hw' => preferredM_rightUnique mkt μ ν m hw hw')
    (fun w _ hm _ hm' => preferredM_leftUnique mkt μ ν w hm hm')

@[simp] theorem preferredMatching_apply (μ ν : mkt.StableMatching) (m : M) :
    preferredMatching mkt μ ν m = preferredM mkt μ ν m := by
  apply Option.ext
  intro w
  exact PEquiv.ofRelation_apply_eq_some_iff _ _ _

/-- Every man weakly prefers the constructed matching to both inputs. -/
theorem le_preferredMatching_left (μ ν : mkt.StableMatching) (m : M) :
    mkt.leM m (μ.matching m) (preferredMatching mkt μ ν m) := by
  rw [preferredMatching_apply]
  exact le_preferredM_left mkt μ ν m

theorem le_preferredMatching_right (μ ν : mkt.StableMatching) (m : M) :
    mkt.leM m (ν.matching m) (preferredMatching mkt μ ν m) := by
  rw [preferredMatching_apply]
  exact le_preferredM_right mkt μ ν m

section Finite

variable [Finite M] [Finite W]

/-- The pointwise choice preserves the matched men. -/
private theorem preferredMatching_isSome_iff (μ ν : mkt.StableMatching) (m : M) :
    (preferredMatching mkt μ ν m).isSome ↔ (μ.matching m).isSome := by
  have hnone := mkt.eq_none_iff_of_stable μ.isStable ν.isStable m
  cases hμ : μ.matching m with
  | none =>
      have hν : ν.matching m = none := hnone.mp hμ
      simp [preferredMatching_apply, preferredM, hμ, hν]
  | some w =>
      cases hν : ν.matching m with
      | none =>
          have : μ.matching m = none := hnone.mpr hν
          simp [hμ] at this
      | some w' =>
          rcases preferredM_eq_left_or_right mkt μ ν m with hleft | hright
          · simp [preferredMatching_apply, hleft, hμ]
          · simp [preferredMatching_apply, hright, hν]

/-- Every woman chosen by the constructed matching is matched in each input. -/
private theorem preferredMatching_woman_isSome_imp (μ ν : mkt.StableMatching)
    (w : W) (hw : ((preferredMatching mkt μ ν).symm w).isSome) :
    (μ.matching.symm w).isSome := by
  let σ := preferredMatching mkt μ ν
  cases hσ : σ.symm w with
  | none =>
      change (σ.symm w).isSome at hw
      simp [hσ] at hw
  | some m =>
      have hmw : σ m = some w := σ.eq_some_iff.mp hσ
      rw [preferredMatching_apply] at hmw
      rcases preferredM_eq_left_or_right mkt μ ν m with hμ | hν
      · have hμw : μ.matching.symm w = some m :=
          μ.matching.eq_some_iff.mpr (hμ.symm.trans hmw)
        simp [hμw]
      · have hνw : ν.matching.symm w = some m :=
          ν.matching.eq_some_iff.mpr (hν.symm.trans hmw)
        have hνsome : (ν.matching.symm w).isSome := by simp [hνw]
        exact (mkt.isSome_symm_iff_of_stable μ.isStable ν.isStable w).mpr hνsome

/-- The pointwise choice also preserves the matched women. -/
theorem preferredMatching_woman_isSome_iff (μ ν : mkt.StableMatching) (w : W) :
    ((preferredMatching mkt μ ν).symm w).isSome ↔
      (μ.matching.symm w).isSome := by
  classical
  let σ := preferredMatching mkt μ ν
  have hD : ∀ m : M, (σ m).isSome ↔ (μ.matching m).isSome :=
    preferredMatching_isSome_iff mkt μ ν
  let domainEquiv : {m : M // (σ m).isSome} ≃ {m : M // (μ.matching m).isSome} :=
    { toFun := fun x => ⟨x.1, (hD x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (hD x.1).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let womanEquiv : {w : W // (σ.symm w).isSome} ≃
      {w : W // (μ.matching.symm w).isSome} :=
    (matchedEquiv σ).symm.trans (domainEquiv.trans (matchedEquiv μ.matching))
  let inclusion : {w : W // (σ.symm w).isSome} →
      {w : W // (μ.matching.symm w).isSome} :=
    fun x => ⟨x.1, preferredMatching_woman_isSome_imp mkt μ ν x.1 x.2⟩
  have hinj : Function.Injective inclusion := by
    intro x y h
    have hv : (inclusion x).1 = (inclusion y).1 :=
      congrArg (fun z : {w : W // (μ.matching.symm w).isSome} => z.1) h
    exact Subtype.ext hv
  have hsurj : Function.Surjective inclusion :=
    (Finite.injective_iff_surjective_of_equiv womanEquiv).mp hinj
  constructor
  · exact preferredMatching_woman_isSome_imp mkt μ ν w
  · intro hw
    obtain ⟨x, hx⟩ := hsurj ⟨w, hw⟩
    have : x.1 = w := congrArg Subtype.val hx
    simpa only [this] using x.2

/-- A woman's assignment in the pointwise construction comes from an input. -/
theorem preferredMatching_woman_eq_left_or_right (μ ν : mkt.StableMatching) (w : W) :
    (preferredMatching mkt μ ν).symm w = μ.matching.symm w ∨
      (preferredMatching mkt μ ν).symm w = ν.matching.symm w := by
  let σ := preferredMatching mkt μ ν
  cases hσ : σ.symm w with
  | none =>
      have hμnone : μ.matching.symm w = none := by
        cases hμ : μ.matching.symm w with
        | none => rfl
        | some m =>
            have hs := (preferredMatching_woman_isSome_iff mkt μ ν w).mpr
              (by simp [hμ])
            change (σ.symm w).isSome at hs
            simp [hσ] at hs
      left
      exact hμnone.symm
  | some m =>
      have hmw : σ m = some w := σ.eq_some_iff.mp hσ
      rw [preferredMatching_apply] at hmw
      rcases preferredM_eq_left_or_right mkt μ ν m with hμ | hν
      · left
        exact (μ.matching.eq_some_iff.mpr (hμ.symm.trans hmw)).symm
      · right
        exact (ν.matching.eq_some_iff.mpr (hν.symm.trans hmw)).symm

/-- Pointwise preferred choice of two stable matchings is stable. -/
theorem stable_preferredMatching (μ ν : mkt.StableMatching) :
    mkt.IsStableMatching (preferredMatching mkt μ ν) := by
  let σ := preferredMatching mkt μ ν
  refine ⟨⟨?_, ?_⟩, (mkt.unblocked_iff_no_blockingPair σ).mpr ?_⟩
  · intro m
    let := mkt.prefM m
    exact le_trans (μ.isStable.1.1 m) (le_preferredMatching_left mkt μ ν m)
  · intro w
    change mkt.leW w none ((preferredMatching mkt μ ν).symm w)
    rcases preferredMatching_woman_eq_left_or_right mkt μ ν w with h | h
    · rw [h]
      exact μ.isStable.1.2 w
    · rw [h]
      exact ν.isStable.1.2 w
  · intro m w hblock
    have hmμ : mkt.ltM m (μ.matching m) (some w) := by
      let := mkt.prefM m
      exact lt_of_le_of_lt (le_preferredMatching_left mkt μ ν m) hblock.1
    have hmν : mkt.ltM m (ν.matching m) (some w) := by
      let := mkt.prefM m
      exact lt_of_le_of_lt (le_preferredMatching_right mkt μ ν m) hblock.1
    have hwμ : mkt.leW w (some m) (μ.matching.symm w) := by
      let := mkt.prefW w
      exact le_of_not_gt (fun h => μ.isStable.2.1 m w ⟨hmμ, h⟩)
    have hwν : mkt.leW w (some m) (ν.matching.symm w) := by
      let := mkt.prefW w
      exact le_of_not_gt (fun h => ν.isStable.2.1 m w ⟨hmν, h⟩)
    change mkt.ltM m (σ m) (some w) ∧
      mkt.ltW w ((preferredMatching mkt μ ν).symm w) (some m) at hblock
    let := mkt.prefW w
    rcases preferredMatching_woman_eq_left_or_right mkt μ ν w with h | h
    · rw [h] at hblock
      exact (not_lt_of_ge hwμ) hblock.2
    · rw [h] at hblock
      exact (not_lt_of_ge hwν) hblock.2

end Finite

variable [Fintype M] [Fintype W]

/-- The lattice join is pointwise maximum in each man's preference order. -/
theorem matching_sup_apply (μ ν : mkt.StableMatching) (m : M) :
    (μ ⊔ ν).matching m = preferredM mkt μ ν m := by
  let σ : mkt.StableMatching :=
    ⟨preferredMatching mkt μ ν, stable_preferredMatching mkt μ ν⟩
  have hμσ : μ ≤ σ :=
    (le_iff_menWeaklyPrefer mkt).mpr (le_preferredMatching_left mkt μ ν)
  have hνσ : ν ≤ σ :=
    (le_iff_menWeaklyPrefer mkt).mpr (le_preferredMatching_right mkt μ ν)
  have hsupσ : μ ⊔ ν ≤ σ := sup_le hμσ hνσ
  have hσsup : σ ≤ μ ⊔ ν := by
    apply (le_iff_menWeaklyPrefer mkt).mpr
    intro m'
    let := mkt.prefM m'
    have hμ : mkt.leM m' (μ.matching m') ((μ ⊔ ν).matching m') :=
      (le_iff_menWeaklyPrefer mkt).mp le_sup_left m'
    have hν : mkt.leM m' (ν.matching m') ((μ ⊔ ν).matching m') :=
      (le_iff_menWeaklyPrefer mkt).mp le_sup_right m'
    change mkt.leM m' ((preferredMatching mkt μ ν) m') _
    rw [preferredMatching_apply]
    exact max_le hμ hν
  have hσ : μ ⊔ ν = σ := le_antisymm hsupσ hσsup
  have h := congrArg (fun ρ : mkt.StableMatching => ρ.matching m) hσ
  simpa only [σ, preferredMatching_apply] using h

/-- The meet assigns each woman her preferred input assignment. -/
theorem matching_inf_symm_apply (μ ν : mkt.StableMatching) (w : W) :
    (μ ⊓ ν).matching.symm w =
      preferredM mkt.symm (symmEquiv mkt μ) (symmEquiv mkt ν) w := by
  have h := (symmOrderIso mkt).map_inf μ ν
  change symmEquiv mkt (μ ⊓ ν) =
    (symmEquiv mkt μ ⊔ symmEquiv mkt ν) at h
  have hw := congrArg (fun ρ : mkt.symm.StableMatching => ρ.matching w) h
  simpa only [matching_symmEquiv, matching_sup_apply] using hw

/-- Each man's assignment at the meet comes from one of its inputs. -/
theorem matching_inf_eq_left_or_right (μ ν : mkt.StableMatching) (m : M) :
    (μ ⊓ ν).matching m = μ.matching m ∨
      (μ ⊓ ν).matching m = ν.matching m := by
  cases hτ : (μ ⊓ ν).matching m with
  | none =>
      have hμ : μ.matching m = none :=
        (mkt.eq_none_iff_of_stable (μ ⊓ ν).isStable μ.isStable m).mp hτ
      exact Or.inl hμ.symm
  | some w =>
      have hτw : (μ ⊓ ν).matching.symm w = some m :=
        (μ ⊓ ν).matching.eq_some_iff.mpr hτ
      have hpreferred := matching_inf_symm_apply mkt μ ν w
      rcases preferredM_eq_left_or_right mkt.symm
          (symmEquiv mkt μ) (symmEquiv mkt ν) w with hμ | hν
      · have hμw : μ.matching.symm w = some m := by
          simpa only [matching_symmEquiv] using hμ.symm.trans (hpreferred.symm.trans hτw)
        exact Or.inl (μ.matching.eq_some_iff.mp hμw).symm
      · have hνw : ν.matching.symm w = some m := by
          simpa only [matching_symmEquiv] using hν.symm.trans (hpreferred.symm.trans hτw)
        exact Or.inr (ν.matching.eq_some_iff.mp hνw).symm

/-- The lattice meet is pointwise minimum in each man's preference order. -/
theorem matching_inf_apply (μ ν : mkt.StableMatching) (m : M) :
    (μ ⊓ ν).matching m =
      (letI := mkt.prefM m; min (μ.matching m) (ν.matching m)) := by
  let := mkt.prefM m
  have hμ : mkt.leM m ((μ ⊓ ν).matching m) (μ.matching m) :=
    (le_iff_menWeaklyPrefer mkt).mp inf_le_left m
  have hν : mkt.leM m ((μ ⊓ ν).matching m) (ν.matching m) :=
    (le_iff_menWeaklyPrefer mkt).mp inf_le_right m
  rcases matching_inf_eq_left_or_right mkt μ ν m with hleft | hright
  · rw [hleft] at hν ⊢
    exact (min_eq_left hν).symm
  · rw [hright] at hμ ⊢
    exact (min_eq_right hμ).symm

/-- Stable marriage satisfies the distributive law. -/
theorem inf_sup_distrib (μ ν ω : mkt.StableMatching) :
    μ ⊓ (ν ⊔ ω) = (μ ⊓ ν) ⊔ (μ ⊓ ω) := by
  apply ext mkt
  apply PEquiv.ext
  intro m
  let := mkt.prefM m
  simp only [matching_inf_apply, matching_sup_apply, preferredM]
  exact min_max_distrib_left _ _ _

/-- The finite stable-matching lattice is distributive. -/
noncomputable instance : DistribLattice mkt.StableMatching :=
  DistribLattice.ofInfSupLe fun μ ν ω => le_of_eq (inf_sup_distrib mkt μ ν ω)

/-- Canonical Birkhoff representation of the finite stable-matching lattice.
The poset is its intrinsic set of join-irreducible stable matchings. -/
noncomputable def lowerSetSupIrred :
    mkt.StableMatching ≃o LowerSet {μ : mkt.StableMatching // SupIrred μ} := by
  classical
  have hinj : Function.Injective
      (fun μ : mkt.StableMatching => fun m : M => μ.matching m) := by
    intro μ ν h
    apply ext mkt
    apply PEquiv.ext
    intro m
    exact congrFun h m
  letI : Finite mkt.StableMatching := Finite.of_injective _ hinj
  letI : Fintype mkt.StableMatching := Fintype.ofFinite _
  exact OrderIso.lowerSetSupIrred

@[simp] theorem mem_lowerSetSupIrred (μ : mkt.StableMatching)
    (j : {ν : mkt.StableMatching // SupIrred ν}) :
    j ∈ lowerSetSupIrred mkt μ ↔ j.1 ≤ μ := by
  rfl

end StableMatching
end MarriageMarket
end MathEconLib.Matching
