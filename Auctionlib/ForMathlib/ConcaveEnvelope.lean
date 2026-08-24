/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set

/-!
# Concave envelope as the infimum over affine majorants

The **concave envelope** of `φ` on `[a, b]` is the pointwise infimum over all affine majorants of
`φ`; on `[a, b]` it is the **least concave majorant** of `φ`. This file also sets up the
**two-point value**: The supremum, over all mean-preserving two-point splittings with atoms in
`[a, b]`, of the objective `(xL, xR, q) ↦ (1 - q) φ xL + q φ xR`.

## Main definitions

* `IsAffineMajorant a b φ m c` — `(m, c)` dominates `φ` on `[a, b]`.
* `concaveEnvelope a b φ` — pointwise infimum over affine majorants.
* `twoPointFeasibleSet`, `twoPointObjective`, `twoPointValue` — the two-point splitting program.

## Main statements

* `le_concaveEnvelope`, `concaveEnvelope_le_affineMajorant` — sandwich bounds.
* `concaveEnvelope_congr` — the envelope depends only on `φ` restricted to `[a, b]`.
* `exists_twoPointOptimum` — the two-point supremum is attained.

## Tags

concave envelope, least concave majorant, affine majorant, two-point value, concavification
-/

@[expose] public section

/-- `(m, c)` is an affine majorant of `φ` on `[a, b]` if `m t + c ≥ φ t` throughout. -/
def IsAffineMajorant (a b : ℝ) (φ : ℝ → ℝ) (m c : ℝ) : Prop :=
  ∀ t ∈ Icc a b, φ t ≤ m * t + c

/-- The set of values `m x + c` as `(m, c)` ranges over affine majorants of `φ` on `[a, b]`. -/
def affineMajorantValueSet (a b : ℝ) (φ : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {y | ∃ m c, IsAffineMajorant a b φ m c ∧ y = m * x + c}

/-- The **concave envelope** of `φ` on `[a, b]`, defined as the pointwise infimum over all affine
majorants of `φ`. On `[a, b]` this is the smallest concave function dominating `φ`. -/
noncomputable def concaveEnvelope (a b : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  sInf (affineMajorantValueSet a b φ x)

/-- A function continuous on `[a, b]` admits an affine majorant (the constant maximum value). -/
lemma exists_affineMajorant_of_continuousOn
    {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) :
    ∃ m c, IsAffineMajorant a b φ m c := by
  have hcpt : IsCompact (Icc a b) := isCompact_Icc
  have hne : (Icc a b).Nonempty := nonempty_Icc.mpr hab
  obtain ⟨M, _, hM_max⟩ := hcpt.exists_isMaxOn hne hφ
  refine ⟨0, φ M, ?_⟩
  intro t ht
  simpa using hM_max ht

/-- The affine-majorant value set at `x ∈ [a, b]` is bounded below by `φ x`. -/
lemma bddBelow_affineMajorantValueSet
    {a b : ℝ} {φ : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc a b) :
    BddBelow (affineMajorantValueSet a b φ x) := by
  refine ⟨φ x, ?_⟩
  rintro y ⟨m, c, hm, rfl⟩
  exact hm x hx

/-- The affine-majorant predicate depends only on the values of `φ` on `[a, b]`. -/
lemma isAffineMajorant_congr {a b : ℝ} {φ ψ : ℝ → ℝ}
    (h : Set.EqOn φ ψ (Icc a b)) {m c : ℝ} :
    IsAffineMajorant a b φ m c ↔ IsAffineMajorant a b ψ m c :=
  forall₂_congr fun t ht => by rw [h ht]

/-- The concave envelope depends only on the values of `φ` on `[a, b]`. -/
lemma concaveEnvelope_congr {a b : ℝ} {φ ψ : ℝ → ℝ} (h : Set.EqOn φ ψ (Icc a b)) (x : ℝ) :
    concaveEnvelope a b φ x = concaveEnvelope a b ψ x := by
  unfold concaveEnvelope affineMajorantValueSet
  congr 1
  ext y
  simp only [mem_setOf_eq, isAffineMajorant_congr h]

/-- The concave envelope dominates `φ` on `[a, b]`. -/
lemma le_concaveEnvelope
    {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) {x : ℝ} (hx : x ∈ Icc a b) :
    φ x ≤ concaveEnvelope a b φ x := by
  obtain ⟨m₀, c₀, hm₀⟩ := exists_affineMajorant_of_continuousOn hab hφ
  refine le_csInf ⟨m₀ * x + c₀, ⟨m₀, c₀, hm₀, rfl⟩⟩ ?_
  rintro y ⟨m, c, hm, rfl⟩
  exact hm x hx

/-- The concave envelope is bounded above by every affine majorant of `φ` on `[a, b]`. -/
lemma concaveEnvelope_le_affineMajorant
    {a b : ℝ} {φ : ℝ → ℝ} {m c : ℝ} (hm : IsAffineMajorant a b φ m c)
    {x : ℝ} (hx : x ∈ Icc a b) :
    concaveEnvelope a b φ x ≤ m * x + c := by
  refine csInf_le (bddBelow_affineMajorantValueSet hx) ?_
  exact ⟨m, c, hm, rfl⟩

/-! ### Two-point optimizer value and attainment -/

/-- Feasible set of two-point splittings of a mean `x` with atoms in `[a, b]`. -/
def twoPointFeasibleSet (a b x : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc (0 : ℝ) 1 ∧
    (1 - p.2.2) * p.1 + p.2.2 * p.2.1 = x}

/-- The continuous objective `(xL, xR, q) ↦ (1 - q) φ xL + q φ xR`. -/
noncomputable def twoPointObjective (φ : ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  (1 - p.2.2) * φ p.1 + p.2.2 * φ p.2.1

/-- The **two-point value** of `φ` at `x` on `[a, b]`: The supremum over all mean-`x` two-point
laws in `[a, b]` of the `φ`-expectation. -/
noncomputable def twoPointValue (a b : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup (twoPointObjective φ '' twoPointFeasibleSet a b x)

/-- For `x ∈ [a, b]`, the two-point feasible set is nonempty (the point mass at `x`). -/
lemma twoPointFeasibleSet_nonempty {a b x : ℝ} (hx : x ∈ Icc a b) :
    (twoPointFeasibleSet a b x).Nonempty :=
  ⟨(x, x, 0), hx, hx, ⟨le_refl 0, zero_le_one⟩, by simp⟩

/-- The two-point feasible set is compact, being a closed subset of a product of compact boxes. -/
lemma isCompact_twoPointFeasibleSet (a b x : ℝ) :
    IsCompact (twoPointFeasibleSet a b x) := by
  have hbox : IsCompact (Icc a b ×ˢ Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : Continuous (fun p : ℝ × ℝ × ℝ => (1 - p.2.2) * p.1 + p.2.2 * p.2.1) := by
    fun_prop
  have hclosed_eq : IsClosed {p : ℝ × ℝ × ℝ | (1 - p.2.2) * p.1 + p.2.2 * p.2.1 = x} :=
    isClosed_eq hcont continuous_const
  have heq :
      twoPointFeasibleSet a b x =
        (Icc a b ×ˢ Icc a b ×ˢ Icc (0 : ℝ) 1) ∩
          {p : ℝ × ℝ × ℝ | (1 - p.2.2) * p.1 + p.2.2 * p.2.1 = x} := by
    ext ⟨u, v, w⟩
    simp only [twoPointFeasibleSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_Icc]
    tauto
  rw [heq]
  exact hbox.inter_right hclosed_eq

/-- For continuous `φ`, the two-point objective is continuous. -/
lemma continuous_twoPointObjective {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Continuous (twoPointObjective φ) := by
  unfold twoPointObjective
  fun_prop

/-- The two-point supremum is attained by some triple `(xL*, xR*, q*)` in the feasible set. -/
lemma exists_twoPointOptimum
    {a b : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ∃ p ∈ twoPointFeasibleSet a b x,
      IsMaxOn (twoPointObjective φ) (twoPointFeasibleSet a b x) p :=
  (isCompact_twoPointFeasibleSet a b x).exists_isMaxOn
    (twoPointFeasibleSet_nonempty hx)
    (continuous_twoPointObjective hφ).continuousOn

/-- The concave envelope is concave on `Icc a b`. -/
lemma concaveOn_concaveEnvelope
    {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) :
    ConcaveOn ℝ (Icc a b) (concaveEnvelope a b φ) := by
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  refine le_csInf ?_ ?_
  · obtain ⟨m₀, c₀, hm₀⟩ := exists_affineMajorant_of_continuousOn hab hφ
    exact ⟨m₀ * (α • x + β • y) + c₀, ⟨m₀, c₀, hm₀, rfl⟩⟩
  rintro _ ⟨m, c, hm, rfl⟩
  have hxb : concaveEnvelope a b φ x ≤ m * x + c :=
    concaveEnvelope_le_affineMajorant hm hx
  have hyb : concaveEnvelope a b φ y ≤ m * y + c :=
    concaveEnvelope_le_affineMajorant hm hy
  have hαx : α * concaveEnvelope a b φ x ≤ α * (m * x + c) :=
    mul_le_mul_of_nonneg_left hxb hα
  have hβy : β * concaveEnvelope a b φ y ≤ β * (m * y + c) :=
    mul_le_mul_of_nonneg_left hyb hβ
  have hsum := add_le_add hαx hβy
  have hconv : α * (m * x + c) + β * (m * y + c) = m * (α • x + β • y) + c := by
    simp only [smul_eq_mul]
    linear_combination c * hαβ
  calc
    α • concaveEnvelope a b φ x + β • concaveEnvelope a b φ y =
        α * concaveEnvelope a b φ x + β * concaveEnvelope a b φ y := by
      simp [smul_eq_mul]
    _ ≤ α * (m * x + c) + β * (m * y + c) := hsum
    _ = m * (α • x + β • y) + c := hconv
