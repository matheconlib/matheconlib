/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-!
# Finite-step normalization for infinite-data rationalization

Gonczarowski, Kominers, and Shorrer (2025), "To infinity and beyond: A general
framework for scaling economic theories", Theoretical Economics 20, Theorem 8,
use prescribed positive gaps to retain strict monotonicity under compactness.
This module supplies a finite-constraint adaptation: a bounded strictly
increasing scalar baseline plus finitely many nondecreasing scalar-utility
threshold steps. Thresholds are utility levels, so the transformation preserves
all weak and strict comparisons of the original utility.

This is normalization infrastructure, not by itself Reny's infinite-data
Afriat theorem. No continuity or concavity of the transformed score is claimed.

## References and Lean provenance

Yannai A. Gonczarowski, Scott Duke Kominers and Ran I. Shorrer (2025),
*To infinity and beyond: A general framework for scaling economic theories*,
Theoretical Economics **20**(2), 511–542, Theorem 8.
[DOI: 10.3982/TE5878](https://doi.org/10.3982/TE5878).

Ported from Victor H. Aguiar's Apache-2.0 Lean development
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), module `RenyNormalization`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

open Finset

/-- A bounded strictly increasing baseline on the nonnegative real axis. -/
noncomputable def renyScalarBase (r : ℝ) : ℝ := r / (2 * (1 + r))

theorem renyScalarBase_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ renyScalarBase r := by
  unfold renyScalarBase
  exact div_nonneg hr (by positivity)

theorem renyScalarBase_lt_half {r : ℝ} (hr : 0 ≤ r) :
    renyScalarBase r < 1 / 2 := by
  unfold renyScalarBase
  apply (div_lt_iff₀ (by positivity : 0 < 2 * (1 + r))).2
  linarith

theorem renyScalarBase_strictMonoOn :
    StrictMonoOn renyScalarBase (Set.Ici 0) := by
  intro r hr s hs hrs
  change 0 ≤ r at hr
  change 0 ≤ s at hs
  unfold renyScalarBase
  apply (div_lt_div_iff₀ (by positivity : 0 < 2 * (1 + r))
    (by positivity : 0 < 2 * (1 + s))).2
  nlinarith

/-- A utility-threshold step; its argument is a scalar utility, not a bundle. -/
noncomputable def renyThresholdStep (w threshold t : ℝ) : ℝ := by
  classical
  exact if threshold ≤ t then w else 0

theorem renyThresholdStep_nonneg {w threshold t : ℝ} (hw : 0 ≤ w) :
    0 ≤ renyThresholdStep w threshold t := by
  classical
  unfold renyThresholdStep
  split_ifs <;> linarith

theorem renyThresholdStep_le_weight {w threshold t : ℝ} (hw : 0 ≤ w) :
    renyThresholdStep w threshold t ≤ w := by
  classical
  unfold renyThresholdStep
  split_ifs <;> linarith

theorem renyThresholdStep_monotone {w threshold : ℝ} (hw : 0 ≤ w) :
    Monotone (renyThresholdStep w threshold) := by
  classical
  intro a b hab
  unfold renyThresholdStep
  split_ifs with ha hb
  · exact le_rfl
  · exact (hb (ha.trans hab)).elim
  · exact hw
  · exact le_rfl

/-- A finite scalar normalization with threshold weights of total mass at most
one half. `anchor` is a lower bound on the original utility's relevant range. -/
noncomputable def renyFiniteTransform {J : Type*} (K : Finset J)
    (w threshold : J → ℝ) (anchor t : ℝ) : ℝ :=
  renyScalarBase (t - anchor) + ∑ j ∈ K, renyThresholdStep (w j) (threshold j) t

theorem renyFiniteTransform_nonneg {J : Type*} (K : Finset J)
    (w threshold : J → ℝ) (anchor : ℝ)
    (hw : ∀ j ∈ K, 0 ≤ w j) {t : ℝ} (ht : anchor ≤ t) :
    0 ≤ renyFiniteTransform K w threshold anchor t := by
  apply add_nonneg (renyScalarBase_nonneg (sub_nonneg.mpr ht))
  exact sum_nonneg fun j hj => renyThresholdStep_nonneg (hw j hj)

theorem renyFiniteTransform_lt_one {J : Type*} (K : Finset J)
    (w threshold : J → ℝ) (anchor : ℝ)
    (hw : ∀ j ∈ K, 0 ≤ w j) (hsum : ∑ j ∈ K, w j ≤ 1 / 2)
    {t : ℝ} (ht : anchor ≤ t) :
    renyFiniteTransform K w threshold anchor t < 1 := by
  have hbase := renyScalarBase_lt_half (sub_nonneg.mpr ht)
  have hsteps : (∑ j ∈ K, renyThresholdStep (w j) (threshold j) t) ≤ 1 / 2 := by
    exact (sum_le_sum fun j hj => renyThresholdStep_le_weight (hw j hj)).trans hsum
  unfold renyFiniteTransform
  linarith

theorem renyFiniteTransform_strictMonoOn {J : Type*} (K : Finset J)
    (w threshold : J → ℝ) (anchor : ℝ)
    (hw : ∀ j ∈ K, 0 ≤ w j) :
    StrictMonoOn (renyFiniteTransform K w threshold anchor) (Set.Ici anchor) := by
  intro a ha b hb hab
  change anchor ≤ a at ha
  change anchor ≤ b at hb
  have hbase : renyScalarBase (a - anchor) < renyScalarBase (b - anchor) :=
    renyScalarBase_strictMonoOn (a := a - anchor) (b := b - anchor)
      (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
      (sub_lt_sub_right hab anchor)
  have hsteps : (∑ j ∈ K, renyThresholdStep (w j) (threshold j) a) ≤
      ∑ j ∈ K, renyThresholdStep (w j) (threshold j) b := by
    exact sum_le_sum fun j hj => renyThresholdStep_monotone (hw j hj) hab.le
  exact add_lt_add_of_lt_of_le hbase hsteps

/-- Crossing a selected threshold creates at least its prescribed utility gap. -/
theorem renyFiniteTransform_gap {J : Type*} (K : Finset J)
    (w threshold : J → ℝ) (anchor : ℝ)
    (hw : ∀ j ∈ K, 0 ≤ w j) {j : J} (hj : j ∈ K)
    {a : ℝ} (ha : anchor ≤ a) (hab : a < threshold j) :
    renyFiniteTransform K w threshold anchor a + w j ≤
      renyFiniteTransform K w threshold anchor (threshold j) := by
  classical
  have hsteps : w j ≤ ∑ i ∈ K,
      (renyThresholdStep (w i) (threshold i) (threshold j) -
        renyThresholdStep (w i) (threshold i) a) := by
    have h := single_le_sum
      (f := fun i => renyThresholdStep (w i) (threshold i) (threshold j) -
        renyThresholdStep (w i) (threshold i) a)
      (fun i hi => sub_nonneg.mpr
        (renyThresholdStep_monotone (threshold := threshold i) (hw i hi) hab.le)) hj
    simpa [renyThresholdStep, not_le.mpr hab] using h
  rw [sum_sub_distrib] at hsteps
  have hbase : renyScalarBase (a - anchor) ≤
      renyScalarBase (threshold j - anchor) :=
    (renyScalarBase_strictMonoOn (a := a - anchor) (b := threshold j - anchor)
      (sub_nonneg.mpr ha)
      (sub_nonneg.mpr (ha.trans hab.le)) (sub_lt_sub_right hab anchor)).le
  unfold renyFiniteTransform
  linarith

/-- Composing with the scalar normalization preserves an original weak utility
comparison whenever both utility values lie above the anchor. -/
theorem renyFiniteTransform_preserves_le {J X : Type*} (K : Finset J)
    (w threshold : J → ℝ) (anchor : ℝ) (U : X → ℝ)
    (hw : ∀ j ∈ K, 0 ≤ w j) {x y : X}
    (hx : anchor ≤ U x) (hy : anchor ≤ U y) (hxy : U x ≤ U y) :
    renyFiniteTransform K w threshold anchor (U x) ≤
      renyFiniteTransform K w threshold anchor (U y) := by
  exact (renyFiniteTransform_strictMonoOn K w threshold anchor hw).monotoneOn hx hy hxy

/-- Composing with the scalar normalization preserves an original strict utility
comparison whenever both utility values lie above the anchor. -/
theorem renyFiniteTransform_preserves_lt {J X : Type*} (K : Finset J)
    (w threshold : J → ℝ) (anchor : ℝ) (U : X → ℝ)
    (hw : ∀ j ∈ K, 0 ≤ w j) {x y : X}
    (hx : anchor ≤ U x) (hy : anchor ≤ U y) (hxy : U x < U y) :
    renyFiniteTransform K w threshold anchor (U x) <
      renyFiniteTransform K w threshold anchor (U y) := by
  exact renyFiniteTransform_strictMonoOn K w threshold anchor hw hx hy hxy

/-- The pointwise inequality defining quasiconcavity survives normalization. -/
theorem renyFiniteTransform_preserves_min_le {J X : Type*} (K : Finset J)
    (w threshold : J → ℝ) (anchor : ℝ) (U : X → ℝ)
    (hw : ∀ j ∈ K, 0 ≤ w j) {x y z : X}
    (hx : anchor ≤ U x) (hy : anchor ≤ U y) (hz : anchor ≤ U z)
    (hxyz : min (U x) (U y) ≤ U z) :
    min (renyFiniteTransform K w threshold anchor (U x))
        (renyFiniteTransform K w threshold anchor (U y)) ≤
      renyFiniteTransform K w threshold anchor (U z) := by
  rcases le_total (U x) (U y) with hxy | hyx
  · exact (min_le_left _ _).trans
      (renyFiniteTransform_preserves_le K w threshold anchor U hw hx hz
        (by simpa [min_eq_left hxy] using hxyz))
  · exact (min_le_right _ _).trans
      (renyFiniteTransform_preserves_le K w threshold anchor U hw hy hz
        (by simpa [min_eq_right hyx] using hxyz))

end MathEconLib.RevealedPreference
