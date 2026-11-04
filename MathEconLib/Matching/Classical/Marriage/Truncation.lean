/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.Basic
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Truncating one man's list at a partner threshold

The transformation moves his outside option immediately below the threshold,
while preserving every comparison between partners. The other participants'
preferences are unchanged. It is a transformation of the existing marriage
market model, with no additional market structure.
-/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

universe u v

variable {M : Type u} {W : Type v}

/-- Three ordered bands: discarded partners, outside option, retained partners. -/
def truncationTag (pref : LinearOrder (Option W)) (threshold : W) : Option W → Nat :=
  let := pref
  fun o => match o with
    | none => 1
    | some w => if some threshold ≤ some w then 2 else 0

/-- The comparison key retains the original ordering within each partner band. -/
def truncationKey (pref : LinearOrder (Option W)) (threshold : W)
    (o : Option W) : Nat ×ₗ Option W :=
  toLex (truncationTag pref threshold o, o)

/-- Keep the partner order and place `none` just below the given partner. -/
@[instance_reducible]
def truncateOptionOrder (pref : LinearOrder (Option W)) (threshold : W) :
    LinearOrder (Option W) := by
  let := pref
  apply LinearOrder.lift' (truncationKey pref threshold)
  intro x y h
  exact congrArg (fun z => (ofLex z).2) h

theorem truncateOptionOrder_some_le_some (pref : LinearOrder (Option W))
    (threshold x y : W) :
    @LE.le (Option W) (truncateOptionOrder pref threshold).toLE (some x) (some y) ↔
      @LE.le (Option W) pref.toLE (some x) (some y) := by
  let := pref
  change truncationKey pref threshold (some x) ≤ truncationKey pref threshold (some y) ↔ _
  simp only [truncationKey, Prod.Lex.toLex_le_toLex]
  by_cases hx : some threshold ≤ some x
  · by_cases hy : some threshold ≤ some y
    · simp [truncationTag, hx, hy]
    · have hxy : ¬ some x ≤ some y := fun h => hy (hx.trans h)
      simp [truncationTag, hx, hy, hxy]
  · by_cases hy : some threshold ≤ some y
    · have hxy : some x ≤ some y := (lt_of_not_ge hx).le.trans hy
      simp [truncationTag, hx, hy, hxy]
    · simp [truncationTag, hx, hy]

theorem truncateOptionOrder_some_lt_some (pref : LinearOrder (Option W))
    (threshold x y : W) :
    @LT.lt (Option W) (truncateOptionOrder pref threshold).toLT (some x) (some y) ↔
      @LT.lt (Option W) pref.toLT (some x) (some y) := by
  rw [@lt_iff_le_not_ge (Option W) (truncateOptionOrder pref threshold).toPreorder,
    @lt_iff_le_not_ge (Option W) pref.toPreorder,
    truncateOptionOrder_some_le_some, truncateOptionOrder_some_le_some]

theorem truncateOptionOrder_none_le_some (pref : LinearOrder (Option W))
    (threshold w : W) :
    @LE.le (Option W) (truncateOptionOrder pref threshold).toLE none (some w) ↔
      @LE.le (Option W) pref.toLE (some threshold) (some w) := by
  let := pref
  change truncationKey pref threshold none ≤ truncationKey pref threshold (some w) ↔ _
  simp only [truncationKey, Prod.Lex.toLex_le_toLex]
  by_cases h : some threshold ≤ some w <;> simp [truncationTag, h]

theorem truncateOptionOrder_some_le_none (pref : LinearOrder (Option W))
    (threshold w : W) :
    @LE.le (Option W) (truncateOptionOrder pref threshold).toLE (some w) none ↔
      ¬ @LE.le (Option W) pref.toLE (some threshold) (some w) := by
  let := pref
  change truncationKey pref threshold (some w) ≤ truncationKey pref threshold none ↔ _
  simp only [truncationKey, Prod.Lex.toLex_le_toLex]
  by_cases h : some threshold ≤ some w <;> simp [truncationTag, h]

variable [DecidableEq M] (mkt : MarriageMarket M W)

/-- Truncate a single man's acceptable list, retaining all other preferences. -/
def truncateMan (m : M) (threshold : W) : MarriageMarket M W where
  prefM m' := if m' = m then truncateOptionOrder (mkt.prefM m') threshold else mkt.prefM m'
  prefW := mkt.prefW

theorem truncateMan_prefM_self (m : M) (threshold : W) :
    (mkt.truncateMan m threshold).prefM m = truncateOptionOrder (mkt.prefM m) threshold := by
  simp [truncateMan]

theorem truncateMan_prefM_of_ne (m m' : M) (threshold : W) (hne : m' ≠ m) :
    (mkt.truncateMan m threshold).prefM m' = mkt.prefM m' := by
  simp [truncateMan, hne]

@[simp] theorem truncateMan_leW (m : M) (threshold : W) (w : W) (x y : Option M) :
    (mkt.truncateMan m threshold).leW w x y ↔ mkt.leW w x y := Iff.rfl

@[simp] theorem truncateMan_ltW (m : M) (threshold : W) (w : W) (x y : Option M) :
    (mkt.truncateMan m threshold).ltW w x y ↔ mkt.ltW w x y := Iff.rfl

theorem truncateMan_leM_of_ne (m m' : M) (threshold : W) (hne : m' ≠ m)
    (x y : Option W) :
    (mkt.truncateMan m threshold).leM m' x y ↔ mkt.leM m' x y := by
  change @LE.le _ ((mkt.truncateMan m threshold).prefM m').toLE x y ↔ _
  rw [truncateMan_prefM_of_ne mkt m m' threshold hne]
  rfl

theorem truncateMan_ltM_of_ne (m m' : M) (threshold : W) (hne : m' ≠ m)
    (x y : Option W) :
    (mkt.truncateMan m threshold).ltM m' x y ↔ mkt.ltM m' x y := by
  change @LT.lt _ ((mkt.truncateMan m threshold).prefM m').toLT x y ↔ _
  rw [truncateMan_prefM_of_ne mkt m m' threshold hne]
  rfl

theorem truncateMan_leM_some_some (m m' : M) (threshold x y : W) :
    (mkt.truncateMan m threshold).leM m' (some x) (some y) ↔
      mkt.leM m' (some x) (some y) := by
  by_cases h : m' = m
  · subst m'
    change @LE.le _ ((mkt.truncateMan m threshold).prefM m).toLE (some x) (some y) ↔ _
    rw [truncateMan_prefM_self]
    exact truncateOptionOrder_some_le_some _ _ _ _
  · exact truncateMan_leM_of_ne mkt m m' threshold h _ _

theorem truncateMan_ltM_some_some (m m' : M) (threshold x y : W) :
    (mkt.truncateMan m threshold).ltM m' (some x) (some y) ↔
      mkt.ltM m' (some x) (some y) := by
  by_cases h : m' = m
  · subst m'
    change @LT.lt _ ((mkt.truncateMan m threshold).prefM m).toLT (some x) (some y) ↔ _
    rw [truncateMan_prefM_self]
    exact truncateOptionOrder_some_lt_some _ _ _ _
  · exact truncateMan_ltM_of_ne mkt m m' threshold h _ _

theorem truncateMan_none_le_some (m : M) (threshold w : W) :
    (mkt.truncateMan m threshold).leM m none (some w) ↔
      mkt.leM m (some threshold) (some w) := by
  change @LE.le _ ((mkt.truncateMan m threshold).prefM m).toLE none (some w) ↔ _
  rw [truncateMan_prefM_self]
  exact truncateOptionOrder_none_le_some _ _ _

/-- An original stable matching that meets the cut is stable after truncation. -/
theorem stable_truncateMan_of_stable {μ : M ≃. W} {m : M} {threshold current : W}
    (hμ : mkt.IsStableMatching μ) (hcurrent : μ m = some current)
    (hthreshold : mkt.leM m (some threshold) (some current)) :
    (mkt.truncateMan m threshold).IsStableMatching μ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro m'
    by_cases hm : m' = m
    · subst m'
      change (mkt.truncateMan m threshold).leM m none (μ m)
      rw [hcurrent]
      exact (truncateMan_none_le_some mkt m threshold current).mpr hthreshold
    · exact (truncateMan_leM_of_ne mkt m m' threshold hm _ _).mpr
        (hμ.1.1 m')
  · intro w
    exact hμ.1.2 w
  · apply ((mkt.truncateMan m threshold).unblocked_iff_no_blockingPair μ).mpr
    intro m' w hb
    apply hμ.2.1 m' w
    refine ⟨?_, hb.2⟩
    by_cases hm : m' = m
    · subst m'
      have h : (mkt.truncateMan m threshold).ltM m (μ m) (some w) := hb.1
      rw [hcurrent] at h
      change mkt.ltM m (μ m) (some w)
      rw [hcurrent]
      exact (truncateMan_ltM_some_some mkt m m threshold current w).mp h
    · exact (truncateMan_ltM_of_ne mkt m m' threshold hm _ _).mp hb.1

/-- Once the truncated man is matched, no removed pair can create a new block. -/
theorem stable_of_stable_truncateMan {μ : M ≃. W} {m : M} {threshold current : W}
    (hacceptable : mkt.leM m none (some threshold))
    (hμ : (mkt.truncateMan m threshold).IsStableMatching μ)
    (hcurrent : μ m = some current) : mkt.IsStableMatching μ := by
  have hthreshold : mkt.leM m (some threshold) (some current) := by
    apply (truncateMan_none_le_some mkt m threshold current).mp
    have hir : (mkt.truncateMan m threshold).leM m none (μ m) := hμ.1.1 m
    rw [hcurrent] at hir
    exact hir
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro m'
    by_cases hm : m' = m
    · subst m'
      let := mkt.prefM m
      change none ≤ μ m
      rw [hcurrent]
      exact hacceptable.trans hthreshold
    · exact (truncateMan_leM_of_ne mkt m m' threshold hm _ _).mp
        (hμ.1.1 m')
  · intro w
    exact hμ.1.2 w
  · apply (mkt.unblocked_iff_no_blockingPair μ).mpr
    intro m' w hb
    apply hμ.2.1 m' w
    refine ⟨?_, hb.2⟩
    by_cases hm : m' = m
    · subst m'
      have h : mkt.ltM m (μ m) (some w) := hb.1
      rw [hcurrent] at h
      change (mkt.truncateMan m threshold).ltM m (μ m) (some w)
      rw [hcurrent]
      exact (truncateMan_ltM_some_some mkt m m threshold current w).mpr h
    · exact (truncateMan_ltM_of_ne mkt m m' threshold hm _ _).mpr hb.1

end MathEconLib.Matching.MarriageMarket
