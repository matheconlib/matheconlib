/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.Afriat
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Local nonsatiation on the consumption orthant

The metric definition requires an improving nonnegative bundle arbitrarily close
to each nonnegative bundle. No continuity of utility is required. Continuity of
expenditure alone gives budget exhaustion and the GARP necessity implication.
Strictly increasing utilities are locally nonsatiated when there is at least one
good. In dimension zero, the consumption space is a singleton and local
nonsatiation cannot hold; the dimension hypothesis is therefore explicit.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

variable {L : ℕ} {T : Type*}

/-- Local nonsatiation relative to the nonnegative consumption orthant. -/
def LocallyNonsatiatedOnNonnegative (u : Utility L) : Prop :=
  ∀ x, Nonnegative x → ∀ ε : ℝ, 0 < ε →
    ∃ y, Nonnegative y ∧ dist y x < ε ∧ u x < u y

/-- A strictly increasing utility admits arbitrarily nearby improvements in
nonnegative consumption when at least one commodity exists. -/
theorem locallyNonsatiatedOnNonnegative_of_strictlyIncreasing
    (hL : 0 < L) {u : Utility L} (hinc : StrictlyIncreasing u) :
    LocallyNonsatiatedOnNonnegative u := by
  intro x hx ε hε
  let y : Bundle L := fun k => x k + ε / 2
  have hdom : StrictDominates y x := by
    apply strictDominates_iff_lt.mpr
    apply Pi.lt_def.mpr
    refine ⟨fun k => ?_, ⟨0, hL⟩, ?_⟩
    · dsimp [y]
      linarith
    · dsimp [y]
      linarith
  refine ⟨y, (fun k => le_trans (hx k) (hdom.1 k)), ?_, hinc hdom⟩
  apply (dist_pi_lt_iff hε).mpr
  intro k
  dsimp [y]
  rw [Real.dist_eq]
  have heq : x k + ε / 2 - x k = ε / 2 := by ring
  rw [heq, abs_of_pos (by linarith : 0 < ε / 2)]
  linarith

/-- Local nonsatiation improves any strictly affordable bundle while preserving
affordability. Prices need not be positive for this topological argument. -/
theorem exists_strictlyPreferred_affordable_of_lt
    {u : Utility L} (hlns : LocallyNonsatiatedOnNonnegative u)
    (p x : Bundle L) (m : ℝ) (hx : Nonnegative x) (hcheap : dot p x < m) :
    ∃ y, Nonnegative y ∧ dot p y ≤ m ∧ u x < u y := by
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.mp (continuous_dot p).continuousAt)
      (m - dot p x) (sub_pos.mpr hcheap)
  obtain ⟨y, hy, hdist, himprove⟩ := hlns x hx δ hδ
  refine ⟨y, hy, ?_, himprove⟩
  have habs := hclose hdist
  rw [Real.dist_eq] at habs
  have hupper := (abs_lt.mp habs).2
  linarith

/-- A locally nonsatiated utility maximizer exhausts its budget. -/
theorem budget_exhaustion_of_locallyNonsatiated
    {u : Utility L} (hlns : LocallyNonsatiatedOnNonnegative u)
    (p x : Bundle L) (m : ℝ) (hx : Nonnegative x) (hbudget : dot p x ≤ m)
    (hmax : ∀ y, Nonnegative y → dot p y ≤ m → u y ≤ u x) :
    dot p x = m := by
  apply le_antisymm hbudget
  by_contra h
  obtain ⟨y, hy, hcost, himprove⟩ :=
    exists_strictlyPreferred_affordable_of_lt hlns p x m hx (lt_of_not_ge h)
  exact (not_lt_of_ge (hmax y hy hcost)) himprove

/-- Raw locally nonsatiated utility maximization implies graph GARP. Prices may
have arbitrary signs; only the observed choices must be nonnegative. -/
theorem graphGARP_of_locallyNonsatiated_utilityMaximization
    (p q : T → Bundle L) (u : Utility L) (hq : ∀ t, Nonnegative (q t))
    (hlns : LocallyNonsatiatedOnNonnegative u)
    (hmax : ∀ t y, Nonnegative y → dot (p t) y ≤ dot (p t) (q t) → u y ≤ u (q t)) :
    GraphGARP p q := by
  intro s t hst hcheap
  have hchain : u (q t) ≤ u (q s) :=
    revealedPreferred_mono p q (fun r => u (q r))
      (fun {a b} hab => hmax a (q b) (hq b) hab) hst
  obtain ⟨y, hy, hcost, himprove⟩ := exists_strictlyPreferred_affordable_of_lt
    hlns (p t) (q s) (dot (p t) (q t)) (hq s) hcheap
  exact (not_lt_of_ge hchain) (himprove.trans_le (hmax t y hy hcost))

/-- Ordinary locally nonsatiated utility rationalization implies GARP. -/
theorem garp_of_locallyNonsatiated_utilityRationalization
    (D : Dataset L T) (u : Utility L)
    (hlns : LocallyNonsatiatedOnNonnegative u) (hrat : UtilityRationalizes D u) :
    GARP D :=
  graphGARP_of_locallyNonsatiated_utilityMaximization D.price D.choice u
    D.choice_nonneg hlns (fun t y hy hcost => hrat t y ⟨hy, hcost⟩)

end MathEconLib.RevealedPreference
