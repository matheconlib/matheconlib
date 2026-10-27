/-
Copyright (c) 2026 Scott Duke Kominers, Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers, Bo Cowgill
-/
module

public import MathEconLib.Matching.Classical.Marriage.Preferences
public import MathEconLib.ForMathlib.Data.PartialMatching
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Basic

/-!
# Marriage matchings, stability, and optimality specifications

Starting from the preference data in `Marriage.Preferences`, this module
defines classical stability, the four independent optimal/pessimal
specifications, side exchange, graph representations, and the direct
blocking-pair proof of opposition of interests. It is independent of the
matching-with-contracts model.

The order on bare `PEquiv` is its extension order; unanimous preference is
expressed by `MenWeaklyPrefer` and `WomenWeaklyPrefer`.
-/

@[expose] public section

namespace MathEconLib.Matching

open Function OrderDual

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}
variable (mkt : MarriageMarket M W)

/-! ## Classical matchings and stability -/

/-- Individual rationality for a given man: his assignment is no worse
than remaining single. -/
def IndividuallyRationalForM (μ : M ≃. W) (m : M) : Prop :=
  mkt.leM m none (μ m)

/-- Individual rationality for a given woman: her assignment is no worse
than remaining single. -/
def IndividuallyRationalForW (μ : M ≃. W) (w : W) : Prop :=
  mkt.leW w none (μ.symm w)

/-- Individual rationality for all men. -/
def IndividuallyRationalM (μ : M ≃. W) : Prop :=
  ∀ m, mkt.IndividuallyRationalForM μ m

/-- Individual rationality for all women. -/
def IndividuallyRationalW (μ : M ≃. W) : Prop :=
  ∀ w, mkt.IndividuallyRationalForW μ w

/-- Individual rationality for every agent. -/
def IndividuallyRational (μ : M ≃. W) : Prop :=
  mkt.IndividuallyRationalM μ ∧
    mkt.IndividuallyRationalW μ

/-- Man `m` strictly prefers `w` to his current assignment.

This is only the man's condition for blocking; it does not require that
`w` reciprocates. -/
def BlocksM (μ : M ≃. W) (m : M) (w : W) : Prop :=
  mkt.ltM m (μ m) (some w)

/-- Woman `w` strictly prefers `m` to her current assignment.

This is only the woman's condition for blocking; it does not require that
`m` reciprocates. The woman is the first agent argument. -/
def BlocksW (μ : M ≃. W) (w : W) (m : M) : Prop :=
  mkt.ltW w (μ.symm w) (some m)

/-- `(m, w)` blocks `μ` if both agents strictly prefer one another to their
current assignments. -/
def IsBlockingPair (μ : M ≃. W) (m : M) (w : W) : Prop :=
  mkt.toPartnerComparisons.Blocks m w (μ m) (μ.symm w)

/-- No blocking pair involves man `m`. -/
def UnblockedM (μ : M ≃. W) (m : M) : Prop :=
  ∀ w, ¬mkt.IsBlockingPair μ m w

/-- No blocking pair involves woman `w`. -/
def UnblockedW (μ : M ≃. W) (w : W) : Prop :=
  ∀ m, ¬mkt.IsBlockingPair μ m w

/-- The matching has no blocking pair.

Both side-indexed formulations are retained for a symmetric API.
They quantify over the same blocking pairs and are proved equivalent below. -/
def Unblocked (μ : M ≃. W) : Prop :=
  (∀ m, mkt.UnblockedM μ m) ∧ (∀ w, mkt.UnblockedW μ w)

/-- Classical stability: individual rationality and no blocking pair. -/
def IsStableMatching (μ : M ≃. W) : Prop :=
  mkt.IndividuallyRational μ ∧ mkt.Unblocked μ

/-! ### Elementary interfaces -/

theorem unblocked_iff_forall_m (μ : M ≃. W) :
    mkt.Unblocked μ ↔ ∀ m, mkt.UnblockedM μ m := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, fun w m => h m w⟩

theorem unblocked_iff_forall_w (μ : M ≃. W) :
    mkt.Unblocked μ ↔ ∀ w, mkt.UnblockedW μ w := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨fun m w => h w m, h⟩

theorem unblocked_iff_no_blockingPair (μ : M ≃. W) :
    mkt.Unblocked μ ↔
      ∀ m w, ¬mkt.IsBlockingPair μ m w := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, fun w m => h m w⟩

theorem IsStableMatching.individuallyRationalForM
    {μ : M ≃. W} (h : mkt.IsStableMatching μ) (m : M) :
    mkt.IndividuallyRationalForM μ m :=
  h.1.1 m

theorem IsStableMatching.individuallyRationalForW
    {μ : M ≃. W} (h : mkt.IsStableMatching μ) (w : W) :
    mkt.IndividuallyRationalForW μ w :=
  h.1.2 w

theorem IsStableMatching.unblockedM
    {μ : M ≃. W} (h : mkt.IsStableMatching μ) (m : M) :
    mkt.UnblockedM μ m :=
  h.2.1 m

theorem IsStableMatching.unblockedW
    {μ : M ≃. W} (h : mkt.IsStableMatching μ) (w : W) :
    mkt.UnblockedW μ w :=
  h.2.2 w

/-! ### Symmetry and unanimous preferences -/

@[simp] theorem individuallyRationalForM_symm (μ : M ≃. W) (w : W) :
    mkt.symm.IndividuallyRationalForM μ.symm w ↔
      mkt.IndividuallyRationalForW μ w := Iff.rfl

@[simp] theorem individuallyRationalForW_symm (μ : M ≃. W) (m : M) :
    mkt.symm.IndividuallyRationalForW μ.symm m ↔
      mkt.IndividuallyRationalForM μ m := Iff.rfl

@[simp] theorem individuallyRationalM_symm (μ : M ≃. W) :
    mkt.symm.IndividuallyRationalM μ.symm ↔
      mkt.IndividuallyRationalW μ := Iff.rfl

@[simp] theorem individuallyRationalW_symm (μ : M ≃. W) :
    mkt.symm.IndividuallyRationalW μ.symm ↔
      mkt.IndividuallyRationalM μ := Iff.rfl

@[simp] theorem individuallyRational_symm (μ : M ≃. W) :
    mkt.symm.IndividuallyRational μ.symm ↔ mkt.IndividuallyRational μ := by
  exact and_comm

@[simp] theorem blocksM_symm (μ : M ≃. W) (w : W) (m : M) :
    mkt.symm.BlocksM μ.symm w m ↔ mkt.BlocksW μ w m := Iff.rfl

@[simp] theorem blocksW_symm (μ : M ≃. W) (m : M) (w : W) :
    mkt.symm.BlocksW μ.symm m w ↔ mkt.BlocksM μ m w := Iff.rfl

@[simp] theorem isBlockingPair_symm (μ : M ≃. W) (w : W) (m : M) :
    mkt.symm.IsBlockingPair μ.symm w m ↔ mkt.IsBlockingPair μ m w := by
  simpa only [IsBlockingPair, toPartnerComparisons_symm, PEquiv.symm_symm] using
    mkt.toPartnerComparisons.blocks_symm m w (μ m) (μ.symm w)

@[simp] theorem unblockedM_symm (μ : M ≃. W) (w : W) :
    mkt.symm.UnblockedM μ.symm w ↔ mkt.UnblockedW μ w := by
  simp only [UnblockedM, UnblockedW, isBlockingPair_symm]

@[simp] theorem unblockedW_symm (μ : M ≃. W) (m : M) :
    mkt.symm.UnblockedW μ.symm m ↔ mkt.UnblockedM μ m := by
  simp only [UnblockedM, UnblockedW, isBlockingPair_symm]

@[simp] theorem unblocked_symm (μ : M ≃. W) :
    mkt.symm.Unblocked μ.symm ↔ mkt.Unblocked μ := by
  simp only [Unblocked, unblockedM_symm, unblockedW_symm, and_comm]

@[simp] theorem isStableMatching_symm (μ : M ≃. W) :
    mkt.symm.IsStableMatching μ.symm ↔ mkt.IsStableMatching μ := by
  simp only [IsStableMatching, individuallyRational_symm, unblocked_symm]

/-- Every man weakly prefers `μ` to `ν`. This is the preference order,
not the extension order that `PEquiv` already carries. -/
def MenWeaklyPrefer (μ ν : M ≃. W) : Prop :=
  ∀ m, mkt.leM m (ν m) (μ m)

/-- Every woman weakly prefers `μ` to `ν`. -/
def WomenWeaklyPrefer (μ ν : M ≃. W) : Prop :=
  ∀ w, mkt.leW w (ν.symm w) (μ.symm w)

@[simp] theorem menWeaklyPrefer_symm (μ ν : M ≃. W) :
    mkt.symm.MenWeaklyPrefer μ.symm ν.symm ↔
      mkt.WomenWeaklyPrefer μ ν := Iff.rfl

@[simp] theorem womenWeaklyPrefer_symm (μ ν : M ≃. W) :
    mkt.symm.WomenWeaklyPrefer μ.symm ν.symm ↔
      mkt.MenWeaklyPrefer μ ν := Iff.rfl

theorem menWeaklyPrefer_antisymm {μ ν : M ≃. W}
    (hμν : mkt.MenWeaklyPrefer μ ν) (hνμ : mkt.MenWeaklyPrefer ν μ) :
    μ = ν := by
  apply PEquiv.ext
  intro m
  let := mkt.prefM m
  exact le_antisymm (hνμ m) (hμν m)

theorem womenWeaklyPrefer_antisymm {μ ν : M ≃. W}
    (hμν : mkt.WomenWeaklyPrefer μ ν) (hνμ : mkt.WomenWeaklyPrefer ν μ) :
    μ = ν := by
  have h : μ.symm = ν.symm :=
    mkt.symm.menWeaklyPrefer_antisymm (μ := μ.symm) (ν := ν.symm) hμν hνμ
  simpa using congrArg PEquiv.symm h

/-- The classical blocking-pair proof of opposition of interests.
If all men prefer `μ` to a stable `ν`, no woman can strictly prefer `μ`
to `ν`: her partner in `μ` would form a blocking pair for `ν`.
No finiteness or contracts theorem is used. -/
theorem womenWeaklyPrefer_of_menWeaklyPrefer {μ ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (h : mkt.MenWeaklyPrefer μ ν) :
    mkt.WomenWeaklyPrefer ν μ := by
  intro w
  let := mkt.prefW w
  cases hμw : μ.symm w with
  | none => exact hν.1.2 w
  | some m =>
      by_contra hnot
      have hw : mkt.BlocksW ν w m := lt_of_not_ge hnot
      have hμm : μ m = some w := μ.eq_some_iff.mp hμw
      have hmle : mkt.leM m (ν m) (some w) := by
        simpa only [hμm] using h m
      have hmne : ν m ≠ some w := by
        intro hm
        have hnuw : ν.symm w = some m := ν.eq_some_iff.mpr hm
        have hlt : ν.symm w < some m := hw
        rw [hnuw] at hlt
        exact (lt_irrefl _ hlt)
      have hm : mkt.BlocksM ν m w := by
        let := mkt.prefM m
        exact lt_of_le_of_ne hmle hmne
      exact hν.2.1 m w ⟨hm, hw⟩

/-- The symmetric blocking-pair proof. -/
theorem menWeaklyPrefer_of_womenWeaklyPrefer {μ ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (h : mkt.WomenWeaklyPrefer μ ν) :
    mkt.MenWeaklyPrefer ν μ := by
  exact mkt.symm.womenWeaklyPrefer_of_menWeaklyPrefer (μ := μ.symm) (ν := ν.symm)
    ((mkt.isStableMatching_symm ν).mpr hν) h

/-- On stable matchings, unanimous preferences of the two sides are opposite. -/
theorem menWeaklyPrefer_iff_womenWeaklyPrefer {μ ν : M ≃. W}
    (hμ : mkt.IsStableMatching μ) (hν : mkt.IsStableMatching ν) :
    mkt.MenWeaklyPrefer μ ν ↔ mkt.WomenWeaklyPrefer ν μ :=
  ⟨mkt.womenWeaklyPrefer_of_menWeaklyPrefer hν,
    mkt.menWeaklyPrefer_of_womenWeaklyPrefer hμ⟩

/-- A stable matching that every man weakly prefers to every stable matching. -/
def IsManOptimal (μ : M ≃. W) : Prop :=
  mkt.IsStableMatching μ ∧ ∀ ν, mkt.IsStableMatching ν → mkt.MenWeaklyPrefer μ ν

/-- A stable matching that every woman weakly prefers to every stable matching. -/
def IsWomanOptimal (μ : M ≃. W) : Prop :=
  mkt.IsStableMatching μ ∧ ∀ ν, mkt.IsStableMatching ν → mkt.WomenWeaklyPrefer μ ν

/-- A stable matching that every man ranks weakly below every stable matching. -/
def IsManPessimal (μ : M ≃. W) : Prop :=
  mkt.IsStableMatching μ ∧ ∀ ν, mkt.IsStableMatching ν → mkt.MenWeaklyPrefer ν μ

/-- A stable matching that every woman ranks weakly below every stable matching. -/
def IsWomanPessimal (μ : M ≃. W) : Prop :=
  mkt.IsStableMatching μ ∧ ∀ ν, mkt.IsStableMatching ν → mkt.WomenWeaklyPrefer ν μ

theorem isManOptimal_iff_isWomanPessimal (μ : M ≃. W) :
    mkt.IsManOptimal μ ↔ mkt.IsWomanPessimal μ := by
  constructor
  · rintro ⟨hμ, h⟩
    exact ⟨hμ, fun ν hν => mkt.womenWeaklyPrefer_of_menWeaklyPrefer hν (h ν hν)⟩
  · rintro ⟨hμ, h⟩
    exact ⟨hμ, fun ν hν => mkt.menWeaklyPrefer_of_womenWeaklyPrefer hμ (h ν hν)⟩

theorem isWomanOptimal_iff_isManPessimal (μ : M ≃. W) :
    mkt.IsWomanOptimal μ ↔ mkt.IsManPessimal μ := by
  constructor
  · rintro ⟨hμ, h⟩
    exact ⟨hμ, fun ν hν => mkt.menWeaklyPrefer_of_womenWeaklyPrefer hν (h ν hν)⟩
  · rintro ⟨hμ, h⟩
    exact ⟨hμ, fun ν hν => mkt.womenWeaklyPrefer_of_menWeaklyPrefer hμ (h ν hν)⟩

theorem IsManOptimal.unique {μ ν : M ≃. W}
    (hμ : mkt.IsManOptimal μ) (hν : mkt.IsManOptimal ν) : μ = ν :=
  mkt.menWeaklyPrefer_antisymm (hμ.2 ν hν.1) (hν.2 μ hμ.1)

theorem IsWomanOptimal.unique {μ ν : M ≃. W}
    (hμ : mkt.IsWomanOptimal μ) (hν : mkt.IsWomanOptimal ν) : μ = ν :=
  mkt.womenWeaklyPrefer_antisymm (hμ.2 ν hν.1) (hν.2 μ hμ.1)

theorem IsManPessimal.unique {μ ν : M ≃. W}
    (hμ : mkt.IsManPessimal μ) (hν : mkt.IsManPessimal ν) : μ = ν :=
  mkt.menWeaklyPrefer_antisymm (hν.2 μ hμ.1) (hμ.2 ν hν.1)

theorem IsWomanPessimal.unique {μ ν : M ≃. W}
    (hμ : mkt.IsWomanPessimal μ) (hν : mkt.IsWomanPessimal ν) : μ = ν :=
  mkt.womenWeaklyPrefer_antisymm (hν.2 μ hμ.1) (hμ.2 ν hν.1)

/-! ## Graphs of partial matchings

The graph itself and its structural properties belong to `PEquiv`. These
wrappers retain the classical `mkt.graphOf` statement interface.
-/

set_option linter.unusedVariables false in
/-- The contract graph of a partial matching. -/
def graphOf (mkt : MarriageMarket M W) (μ : M ≃. W) : Set (M × W) :=
  μ.graph

@[simp] theorem mem_graphOf {μ : M ≃. W} {m : M} {w : W} :
    (m, w) ∈ mkt.graphOf μ ↔ μ m = some w :=
  PEquiv.mem_graph

@[simp] theorem mem_graphOf_symm {μ : M ≃. W} {m : M} {w : W} :
    (m, w) ∈ mkt.graphOf μ ↔ μ.symm w = some m :=
  PEquiv.mem_graph_symm

theorem graphOf_rightUnique (μ : M ≃. W) {m : M} {w w' : W}
    (hw : (m, w) ∈ mkt.graphOf μ)
    (hw' : (m, w') ∈ mkt.graphOf μ) :
    w = w' :=
  μ.graph_rightUnique hw hw'

theorem graphOf_leftUnique (μ : M ≃. W) {m m' : M} {w : W}
    (hm : (m, w) ∈ mkt.graphOf μ)
    (hm' : (m', w) ∈ mkt.graphOf μ) :
    m = m' :=
  μ.graph_leftUnique hm hm'

theorem graphOf_injective : Function.Injective mkt.graphOf :=
  PEquiv.graph_injective

@[simp] theorem graphOf_symm (μ : M ≃. W) :
    mkt.symm.graphOf μ.symm = Prod.swap ⁻¹' mkt.graphOf μ :=
  μ.graph_symm

/-! ## Decidability -/

section Decide

variable [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

instance : DecidablePred mkt.IsStableMatching := by
  intro μ
  unfold IsStableMatching
  unfold IndividuallyRational
  unfold IndividuallyRationalM IndividuallyRationalW
  unfold IndividuallyRationalForM IndividuallyRationalForW
  unfold Unblocked UnblockedM UnblockedW
  unfold IsBlockingPair PartnerComparisons.Blocks toPartnerComparisons
  unfold leM leW ltM ltW
  infer_instance

end Decide

end MarriageMarket

end MathEconLib.Matching
