/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Module
public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import MathEconLib.Probability.FinDist.Basic

/-!
# Lotteries

A lottery over prizes `Z` is a finitely supported probability on `Z`: Mathlib's `StdSimplex ℝ Z`.
`[z]` denotes the sure lottery and `α · p ⊕ (1 − α) · q` the compound lottery `mix α p q`.

## Main definitions

* `Lottery Z`, `Lottery.mix`: lotteries and mixtures of two lotteries.
* `Lottery.degenerate`, `Lottery.binary`: the lotteries `[z]` and `α · a ⊕ (1 − α) · b`.
* `Lottery.ofFinDist`: for finite `Z`, the equivalence `FinDist Z ≃ Lottery Z`.

## Main statements

* `exists_iConvexComb_update_eq_mix`: replacing one lottery of a compound lottery is a mixture.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Sections 3.1 and 3.2
-/

@[expose] public section

namespace MathEconLib.DecisionTheory

open Convexity

universe u v

/-- A *lottery* over the prizes `Z`; the probability of `z` under `p` is `p.weights z`. -/
abbrev Lottery (Z : Type u) : Type u := StdSimplex ℝ Z

namespace Lottery

variable {Z : Type u} {I : Type v}

/-! ### Mixtures of two lotteries -/

/-- The compound lottery `α · p ⊕ (1 − α) · q`. -/
noncomputable def mix (α : unitInterval) (p q : Lottery Z) : Lottery Z :=
  convexCombPair (α : ℝ) (1 - α) (unitInterval.nonneg α) (unitInterval.one_sub_nonneg α)
    (add_sub_cancel _ _) p q

variable {α : unitInterval} {p q r : Lottery Z}

theorem mix_def (α : unitInterval) (p q : Lottery Z) :
    mix α p q = convexCombPair (α : ℝ) (1 - α) (unitInterval.nonneg α)
      (unitInterval.one_sub_nonneg α) (add_sub_cancel _ _) p q :=
  rfl

@[simp]
theorem weights_mix (α : unitInterval) (p q : Lottery Z) (z : Z) :
    (mix α p q).weights z = α * p.weights z + (1 - α) * q.weights z := by
  simp [mix]

@[simp]
theorem mix_self (α : unitInterval) (p : Lottery Z) : mix α p p = p := by
  ext z; simp only [weights_mix]; ring

theorem mix_of_coe_eq_one (h : (α : ℝ) = 1) (p q : Lottery Z) : mix α p q = p := by
  ext z; simp [h]

theorem mix_of_coe_eq_zero (h : (α : ℝ) = 0) (p q : Lottery Z) : mix α p q = q := by
  ext z; simp [h]

@[simp]
theorem mix_one (p q : Lottery Z) : mix 1 p q = p := mix_of_coe_eq_one rfl p q

@[simp]
theorem mix_zero (p q : Lottery Z) : mix 0 p q = q := mix_of_coe_eq_zero rfl p q

theorem mix_comm (α : unitInterval) (p q : Lottery Z) :
    mix α p q = mix (unitInterval.symm α) q p := by
  ext z; simp only [weights_mix, unitInterval.coe_symm_eq]; ring

/-- For `β < α`, `α · a ⊕ (1 − α) · b` and `β · a ⊕ (1 − β) · b` mix `[a]` and `[b]`, with
probability `α − β`, with one common lottery. -/
theorem mix_mix_single (a b : Z) {α β : unitInterval} (hβα : (β : ℝ) < α)
    (hα : (α : ℝ) - β < 1) :
    ∃ (t β' : unitInterval), (t : ℝ) = α - β ∧
      mix α (.single a) (.single b) = mix t (.single a) (mix β' (.single a) (.single b)) ∧
      mix β (.single a) (.single b) = mix t (.single b) (mix β' (.single a) (.single b)) := by
  have h1 : (0 : ℝ) < 1 - (α - β) := by linarith
  refine ⟨⟨α - β, Set.mem_Icc.2 ⟨by linarith, by linarith [α.2.2, β.2.1]⟩⟩,
    ⟨β / (1 - (α - β)), Set.mem_Icc.2 ⟨div_nonneg β.2.1 h1.le,
      (div_le_one h1).2 (by linarith [α.2.2])⟩⟩, rfl, ?_, ?_⟩ <;>
  · ext z
    simp only [weights_mix]
    field_simp
    ring

/-! ### Compound lotteries -/

theorem weights_iConvexComb_apply (w : StdSimplex ℝ I) (f : I → Lottery Z) (z : Z) :
    (w.iConvexComb f).weights z = w.weights.sum fun i a => a * (f i).weights z := by
  rw [iConvexComb, StdSimplex.weights_sConvexComb, StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul]),
    Finsupp.sum_apply]
  rfl

/-- Compounding is affine in the weights. -/
theorem iConvexComb_mix (α : unitInterval) (w w' : StdSimplex ℝ I) (f : I → Lottery Z) :
    (mix α w w').iConvexComb f = mix α (w.iConvexComb f) (w'.iConvexComb f) := by
  have h := (StdSimplex.affineMapMk (R := ℝ) f).isAffineMap.map_convexCombPair
    (unitInterval.nonneg α) (unitInterval.one_sub_nonneg α) (add_sub_cancel _ _) w w'
  simpa only [StdSimplex.affineMapMk_apply, mix] using h

/-! ### Decompositions -/

theorem eq_single_of_weights_eq_one (w : Lottery I) (k : I) (hk : w.weights k = 1) :
    w = .single k := by
  classical
  ext i
  by_cases hik : i = k
  · subst hik; simp [hk]
  · simp only [StdSimplex.weights_single, Finsupp.single_apply, Ne.symm hik, ↓reduceIte]
    by_contra hi
    have hsub : ({i, k} : Finset I) ⊆ w.weights.support := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact Finsupp.mem_support_iff.2 hi
      · exact Finsupp.mem_support_iff.2 (by rw [hk]; exact one_ne_zero)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun j => w.weights j) fun j _ _ => w.nonneg j
    rw [Finset.sum_pair hik, hk] at hle
    have htot : (∑ j ∈ w.weights.support, w.weights j) = 1 := w.total
    have hpos : 0 < w.weights i := lt_of_le_of_ne (w.nonneg i) (Ne.symm hi)
    linarith

/-- If `w(k) < 1` then `w = w(k) · [k] ⊕ (1 − w(k)) · r`, where `r` is supported in that of `w`
minus `k`. -/
theorem exists_eq_mix_single (w : Lottery I) (k : I) (hk : w.weights k < 1) :
    ∃ r : Lottery I, r.weights k = 0 ∧ (∀ i, w.weights i = 0 → r.weights i = 0) ∧
      w = mix ⟨w.weights k, Set.mem_Icc.2 ⟨w.nonneg k, hk.le⟩⟩ (.single k) r := by
  classical
  have h1 : (0 : ℝ) < 1 - w.weights k := by linarith
  have hsum : (w.weights.erase k).sum (fun _ a => a) = 1 - w.weights k := by
    have h := w.total
    rw [← Finsupp.single_add_erase k w.weights,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl] at h
    linarith
  refine ⟨⟨(1 - w.weights k)⁻¹ • w.weights.erase k, fun i => ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
    exact mul_nonneg (inv_nonneg.2 h1.le) (by
      rw [Finsupp.erase_apply]; split_ifs
      · exact le_rfl
      · exact w.nonneg i)
  · rw [Finsupp.sum_smul_index' (fun _ => rfl)]
    simp only [smul_eq_mul]
    rw [← Finsupp.mul_sum, hsum, inv_mul_cancel₀ h1.ne']
  · simp
  · intro i hi
    simp [Finsupp.erase_apply, hi]
  · ext i
    simp only [weights_mix, StdSimplex.weights_single, Finsupp.single_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, Finsupp.erase_apply]
    by_cases hik : k = i
    · subst hik; simp
    · simp only [hik, Ne.symm hik, ↓reduceIte]
      field_simp
      ring

/-- Replacing `f k` by `x` in `∑ᵢ wᵢ · fᵢ` gives `w_k · x ⊕ (1 − w_k) · r`, with `r` independent
of `x`. -/
theorem exists_iConvexComb_update_eq_mix [DecidableEq I] (w : StdSimplex ℝ I)
    (f : I → Lottery Z) (k : I) :
    ∃ r : Lottery Z, ∀ x : Lottery Z, w.iConvexComb (Function.update f k x) =
      mix ⟨w.weights k, Set.mem_Icc.2 ⟨w.nonneg k, StdSimplex.weights_apply_le_one w k⟩⟩ x r := by
  rcases (StdSimplex.weights_apply_le_one w k).lt_or_eq with hk | hk
  · obtain ⟨w', hw'k, -, hw⟩ := exists_eq_mix_single w k hk
    refine ⟨w'.iConvexComb f, fun x => ?_⟩
    have hcongr : w'.iConvexComb (Function.update f k x) = w'.iConvexComb f :=
      iConvexComb_congr fun i hi => by
        rw [Function.update_of_ne (by rintro rfl; exact hi hw'k)]
    conv_lhs => rw [hw]
    rw [iConvexComb_mix, Convexity.iConvexComb_single, Function.update_self, hcongr]
  · refine ⟨f k, fun x => ?_⟩
    rw [mix_of_coe_eq_one hk]
    conv_lhs => rw [eq_single_of_weights_eq_one w k hk]
    rw [Convexity.iConvexComb_single, Function.update_self]

/-! ### Degenerate and binary lotteries -/

/-- The degenerate lotteries `[z]`. -/
def degenerate : Set (Lottery Z) := Set.range StdSimplex.single

/-- The lotteries `α · a ⊕ (1 − α) · b` over two prizes `a`, `b` (which may coincide). -/
def binary : Set (Lottery Z) :=
  Set.range fun x : unitInterval × Z × Z => mix x.1 (.single x.2.1) (.single x.2.2)

theorem mem_degenerate : p ∈ degenerate ↔ ∃ z, StdSimplex.single z = p := Iff.rfl

@[simp]
theorem single_mem_degenerate (z : Z) : (StdSimplex.single z : Lottery Z) ∈ degenerate :=
  ⟨z, rfl⟩

theorem mem_binary :
    p ∈ binary ↔ ∃ (α : unitInterval) (a b : Z), mix α (.single a) (.single b) = p :=
  ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2.1, x.2.2, hx⟩, fun ⟨α, a, b, h⟩ => ⟨(α, a, b), h⟩⟩

@[simp]
theorem mix_mem_binary (α : unitInterval) (a b : Z) :
    mix α (.single a) (.single b) ∈ (binary : Set (Lottery Z)) :=
  ⟨(α, a, b), rfl⟩

theorem degenerate_subset_binary : (degenerate : Set (Lottery Z)) ⊆ binary := by
  rintro _ ⟨z, rfl⟩
  exact ⟨(1, z, z), mix_one _ _⟩

/-! ### Lotteries over a finite set as distributions -/

section FinDist

open MathEconLib.Probability

variable [Fintype Z]

/-- On a finite set of prizes, a distribution `FinDist Z` as a lottery. -/
noncomputable def ofFinDist : FinDist Z ≃ Lottery Z where
  toFun d := ⟨Finsupp.equivFunOnFinite.symm d.pmf, fun z => d.nonneg z, by
    simp [Finsupp.sum_fintype]⟩
  invFun p := ⟨p.weights, fun z => p.nonneg z, by simp⟩
  left_inv d := by ext z; simp
  right_inv p := StdSimplex.ext (Finsupp.equivFunOnFinite_symm_coe p.weights)

@[simp]
theorem weights_ofFinDist (d : FinDist Z) (z : Z) : (ofFinDist d).weights z = d z :=
  congrFun (Finsupp.coe_equivFunOnFinite_symm d.pmf) z

@[simp]
theorem ofFinDist_symm_apply (p : Lottery Z) (z : Z) : ofFinDist.symm p z = p.weights z := by
  simp [ofFinDist]; rfl

@[simp]
theorem ofFinDist_pure [DecidableEq Z] (z : Z) : ofFinDist (FinDist.pure z) = .single z := by
  ext y; simp [Finsupp.single_apply]

@[simp]
theorem ofFinDist_mixture (α : unitInterval) (d₁ d₂ : FinDist Z) :
    ofFinDist (FinDist.mixture α d₁ d₂) = mix α (ofFinDist d₁) (ofFinDist d₂) := by
  ext z; simpa using FinDist.mixture_pmf α d₁ d₂ z

end FinDist

end Lottery

section FinDist

open MathEconLib.Probability

variable {Z : Type u} [Fintype Z] [DecidableEq Z]

/-- The degenerate lotteries `[z]`, as distributions. -/
def degenerate : Set (FinDist Z) := Set.range FinDist.pure

/-- The binary lotteries `α · a ⊕ (1 − α) · b`, as distributions. -/
def binary : Set (FinDist Z) :=
  Set.range fun x : unitInterval × Z × Z =>
    FinDist.mixture x.1 (FinDist.pure x.2.1) (FinDist.pure x.2.2)

@[simp]
theorem image_ofFinDist_degenerate :
    Lottery.ofFinDist '' degenerate = Lottery.degenerate (Z := Z) := by
  simp only [degenerate, Lottery.degenerate, ← Set.range_comp, Function.comp_def,
    Lottery.ofFinDist_pure]

@[simp]
theorem image_ofFinDist_binary : Lottery.ofFinDist '' binary = Lottery.binary (Z := Z) := by
  simp only [binary, Lottery.binary, ← Set.range_comp, Function.comp_def,
    Lottery.ofFinDist_mixture, Lottery.ofFinDist_pure]

end FinDist

end MathEconLib.DecisionTheory

/-! ### Worked examples -/

section Examples

open MathEconLib.DecisionTheory MathEconLib.DecisionTheory.Lottery Convexity

example : (mix ⟨0.6, by norm_num, by norm_num⟩ (.single (0 : Fin 3)) (.single 2)).weights 0 = 0.6 ∧
    (mix ⟨0.6, by norm_num, by norm_num⟩ (.single (0 : Fin 3)) (.single 2)).weights 1 = 0 := by
  simp

example (b : Fin 3) : mix ⟨0.6, by norm_num, by norm_num⟩ (.single b) (.single b) = .single b :=
  mix_self _ _

example (α : unitInterval) (q : Lottery (Fin 3)) (hq : q.weights 0 = 0.2) :
    (mix α (mix ⟨0.6, by norm_num, by norm_num⟩ (.single 0) (.single 2)) q).weights 0 =
      α * 0.6 + (1 - α) * 0.2 := by
  simp [hq]

example (p q : Lottery (Fin 2)) : mix 0 p q = q := mix_zero p q

/-- A binary lottery has at most two prizes in its support. -/
example (p : Lottery (Fin 3)) (hp : p ∈ Lottery.binary) : p.weights.support.card ≤ 2 := by
  classical
  obtain ⟨α, a, b, rfl⟩ := mem_binary.1 hp
  calc (mix α (.single a) (.single b)).weights.support.card
        ≤ ({a, b} : Finset (Fin 3)).card := by
        refine Finset.card_le_card fun z hz => ?_
        rw [Finsupp.mem_support_iff] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra h
        rw [not_or] at h
        exact hz (by simp [Ne.symm h.1, Ne.symm h.2])
    _ ≤ 2 := Finset.card_le_two

end Examples
