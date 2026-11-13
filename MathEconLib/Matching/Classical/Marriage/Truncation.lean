/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.Basic
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Moving one man's reservation cutoff to a partner threshold

`truncateOptionOrder pref threshold` keeps every comparison between partners
and moves the outside option `none` immediately below `threshold`. After the
change, a partner `w` is acceptable exactly when `threshold ≤ w` in the
original order (`truncateOptionOrder_none_le_some`), whatever the original
position of `none` was.

This is a general change of reservation cutoff, not always a truncation:

* if `threshold` was originally acceptable, the new acceptable set is the
  upper set of `threshold` within the originally acceptable partners, so it
  shrinks (`truncateMan_acceptable_of_acceptable`);
* if `threshold` was originally unacceptable, every originally acceptable
  partner stays acceptable (`truncateMan_acceptable_of_unacceptable`), and
  the partners from `threshold` up to the old cutoff become acceptable.

For instance, with one man ranking `[0, 1]` (woman `0`, then single) and one
woman ranking `[1, 0]`, the man finds the woman unacceptable. Moving his cutoff
below her makes the full matching stable in the new market, although it is not
stable in the original one. This is why `stable_of_stable_truncateMan` assumes
that the threshold is originally acceptable. A checked version of this
counterexample is in `MathEconLibExamples.Matching.CountingFoundations`.

`truncateMan` applies the change to one man and leaves the other participants'
preferences unchanged. It is a transformation of the existing marriage market
model, with no additional market structure.
-/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

universe u v

variable {M : Type u} {W : Type v}

/-- Three ordered bands: partners below the threshold, the outside option,
and partners from the threshold up. Implementation detail of
`truncateOptionOrder`. -/
def truncateOptionOrder.tag (pref : LinearOrder (Option W)) (threshold : W) : Option W → Nat :=
  let := pref
  fun o => match o with
    | none => 1
    | some w => if some threshold ≤ some w then 2 else 0

/-- The comparison key retains the original ordering within each band.
Implementation detail of `truncateOptionOrder`. -/
def truncateOptionOrder.key (pref : LinearOrder (Option W)) (threshold : W)
    (o : Option W) : Nat ×ₗ Option W :=
  toLex (truncateOptionOrder.tag pref threshold o, o)

/-- Compatibility alias for the nested reservation-cutoff tag. -/
abbrev truncationTag := @truncateOptionOrder.tag

/-- Compatibility alias for the nested reservation-cutoff key. -/
abbrev truncationKey := @truncateOptionOrder.key

/-- Keep the partner order and place `none` just below the given partner.
Partners at least `threshold` become acceptable and all others unacceptable,
regardless of where `none` was originally. -/
@[instance_reducible]
def truncateOptionOrder (pref : LinearOrder (Option W)) (threshold : W) :
    LinearOrder (Option W) := by
  let := pref
  apply LinearOrder.lift' (truncateOptionOrder.key pref threshold)
  intro x y h
  exact congrArg (fun z => (ofLex z).2) h

theorem truncateOptionOrder_some_le_some (pref : LinearOrder (Option W))
    (threshold x y : W) :
    @LE.le (Option W) (truncateOptionOrder pref threshold).toLE (some x) (some y) ↔
      @LE.le (Option W) pref.toLE (some x) (some y) := by
  let := pref
  change truncateOptionOrder.key pref threshold (some x) ≤
      truncateOptionOrder.key pref threshold (some y) ↔ _
  simp only [truncateOptionOrder.key, Prod.Lex.toLex_le_toLex]
  by_cases hx : some threshold ≤ some x
  · by_cases hy : some threshold ≤ some y
    · simp [truncateOptionOrder.tag, hx, hy]
    · have hxy : ¬ some x ≤ some y := fun h => hy (hx.trans h)
      simp [truncateOptionOrder.tag, hx, hy, hxy]
  · by_cases hy : some threshold ≤ some y
    · have hxy : some x ≤ some y := (lt_of_not_ge hx).le.trans hy
      simp [truncateOptionOrder.tag, hx, hy, hxy]
    · simp [truncateOptionOrder.tag, hx, hy]

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
  change truncateOptionOrder.key pref threshold none ≤
      truncateOptionOrder.key pref threshold (some w) ↔ _
  simp only [truncateOptionOrder.key, Prod.Lex.toLex_le_toLex]
  by_cases h : some threshold ≤ some w <;> simp [truncateOptionOrder.tag, h]

theorem truncateOptionOrder_some_le_none (pref : LinearOrder (Option W))
    (threshold w : W) :
    @LE.le (Option W) (truncateOptionOrder pref threshold).toLE (some w) none ↔
      ¬ @LE.le (Option W) pref.toLE (some threshold) (some w) := by
  let := pref
  change truncateOptionOrder.key pref threshold (some w) ≤
      truncateOptionOrder.key pref threshold none ↔ _
  simp only [truncateOptionOrder.key, Prod.Lex.toLex_le_toLex]
  by_cases h : some threshold ≤ some w <;> simp [truncateOptionOrder.tag, h]

variable [DecidableEq M] (mkt : MarriageMarket M W)

/-- Move one man's outside option immediately below `threshold`, retaining all
other preferences. It shrinks his acceptable set exactly when `threshold` was
originally acceptable; see the module documentation. -/
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

/-- After the change, a partner is strictly preferred to staying single exactly
when it is at least the threshold in the original order. -/
theorem truncateMan_none_lt_some (m : M) (threshold w : W) :
    (mkt.truncateMan m threshold).ltM m none (some w) ↔
      mkt.leM m (some threshold) (some w) := by
  rw [← truncateMan_none_le_some mkt m threshold w]
  let := (mkt.truncateMan m threshold).prefM m
  change none < some w ↔ none ≤ some w
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (Option.some_ne_none w).symm⟩

/-- If the threshold was acceptable, the change only removes acceptable partners. -/
theorem truncateMan_acceptable_of_acceptable {m : M} {threshold w : W}
    (hacceptable : mkt.leM m none (some threshold))
    (hw : (mkt.truncateMan m threshold).leM m none (some w)) :
    mkt.leM m none (some w) := by
  let := mkt.prefM m
  exact hacceptable.trans ((truncateMan_none_le_some mkt m threshold w).mp hw)

/-- The new acceptable set is contained in the original one exactly when
the threshold was originally acceptable. Containment may be equality. -/
theorem truncateMan_acceptable_subset_iff (m : M) (threshold : W) :
    (∀ w, (mkt.truncateMan m threshold).leM m none (some w) →
      mkt.leM m none (some w)) ↔ mkt.leM m none (some threshold) := by
  constructor
  · intro h
    apply h threshold
    apply (truncateMan_none_le_some mkt m threshold threshold).mpr
    let := mkt.prefM m
    exact le_rfl
  · intro h w hw
    exact truncateMan_acceptable_of_acceptable mkt h hw

/-- If the threshold was unacceptable, the change keeps every acceptable partner.
Partners from the threshold up to the old cutoff are added. -/
theorem truncateMan_acceptable_of_unacceptable {m : M} {threshold w : W}
    (hunacceptable : mkt.leM m (some threshold) none)
    (hw : mkt.leM m none (some w)) :
    (mkt.truncateMan m threshold).leM m none (some w) := by
  let := mkt.prefM m
  exact (truncateMan_none_le_some mkt m threshold w).mpr (hunacceptable.trans hw)

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

/-- If the threshold was originally acceptable and the truncated man is matched,
no removed pair can create a new block. The acceptability assumption cannot be
dropped; see the module documentation. -/
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
