/-
  Matching with contracts ~> classical model instance:
    the Gale–Shapley marriage model.
-/

import MatchingTheory.Contracts.Order
import MatchingTheory.Contracts.RuralHospitals
import MatchingTheory.Contracts.Iteration

import Mathlib.Data.PEquiv
import Mathlib.Data.Finset.Max

/-!
# The classical marriage market (Gale–Shapley 1962)

Men are sellers/proposers and women are buyers/receivers. Contracts are pairs
`M × W`, with seller `Prod.fst` and buyer `Prod.snd`.

The file defines preference-induced unit-demand choice directly. The outside
option `none` is included in every finite menu; the selected contract is the
one corresponding to the maximum option, unless that maximum is `none`.

Classical matchings are `PEquiv`s. Their graphs are outcomes in the induced
contracts market, and classical stability is proved equivalent to contracts
stability.

Generalized deferred-acceptance iterates from `(univ, ∅)` and `(∅, univ)`
reach the greatest and least fixed points. Their outcomes yield the
man-optimal/woman-pessimal and woman-optimal/man-pessimal matchings.
`Classical.DeferredAcceptance` supplies the classical proposal process and
its agreement with these contracts outcomes.
-/

open Function OrderDual

universe u v

variable {M : Type u} {W : Type v}

/-- A classical marriage market. Each agent has a linear order over possible
partners together with the outside option `none`. -/
structure MarriageMarket (M : Type u) (W : Type v) where
  /-- Man `m`'s preference over women-or-single. -/
  prefM : M → LinearOrder (Option W)
  /-- Woman `w`'s preference over men-or-single. -/
  prefW : W → LinearOrder (Option M)

namespace MarriageMarket

variable (mkt : MarriageMarket M W)

/-- Exchange the two sides of the marriage market. The first side of
`mkt.symm` consists of the original women. -/
def symm : MarriageMarket W M where
  prefM := mkt.prefW
  prefW := mkt.prefM

@[simp] theorem symm_symm : mkt.symm.symm = mkt := by
  cases mkt
  rfl

/-! ## Preference relations as data -/

/-- Strict preference of man `m`. -/
def ltM (m : M) (y z : Option W) : Prop :=
  letI := mkt.prefM m
  y < z

/-- Weak preference of man `m`. -/
def leM (m : M) (y z : Option W) : Prop :=
  letI := mkt.prefM m
  y ≤ z

/-- Strict preference of woman `w`. -/
def ltW (w : W) (y z : Option M) : Prop :=
  letI := mkt.prefW w
  y < z

/-- Weak preference of woman `w`. -/
def leW (w : W) (y z : Option M) : Prop :=
  letI := mkt.prefW w
  y ≤ z

/-- `w` is acceptable to `m`. -/
def AcceptableM (m : M) (w : W) : Prop :=
  mkt.ltM m none (some w)

/-- `m` is acceptable to `w`. -/
def AcceptableW (w : W) (m : M) : Prop :=
  mkt.ltW w none (some m)

@[simp] theorem ltM_symm (w : W) (y z : Option M) :
    mkt.symm.ltM w y z ↔ mkt.ltW w y z := Iff.rfl

@[simp] theorem leM_symm (w : W) (y z : Option M) :
    mkt.symm.leM w y z ↔ mkt.leW w y z := Iff.rfl

@[simp] theorem ltW_symm (m : M) (y z : Option W) :
    mkt.symm.ltW m y z ↔ mkt.ltM m y z := Iff.rfl

@[simp] theorem leW_symm (m : M) (y z : Option W) :
    mkt.symm.leW m y z ↔ mkt.leM m y z := Iff.rfl

@[simp] theorem acceptableM_symm (w : W) (m : M) :
    mkt.symm.AcceptableM w m ↔ mkt.AcceptableW w m := Iff.rfl

@[simp] theorem acceptableW_symm (m : M) (w : W) :
    mkt.symm.AcceptableW m w ↔ mkt.AcceptableM m w := Iff.rfl

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
  mkt.BlocksM μ m w ∧ mkt.BlocksW μ w m

/-- No blocking pair involves man `m`. -/
def UnblockedM (μ : M ≃. W) (m : M) : Prop :=
  ∀ w, ¬mkt.IsBlockingPair μ m w

/-- No blocking pair involves woman `w`. -/
def UnblockedW (μ : M ≃. W) (w : W) : Prop :=
  ∀ m, ¬mkt.IsBlockingPair μ m w

/-- The matching has no blocking pair.

Note that we impose no blocking on both sides of the market for the sake of
symmetry even though in this setting blocking on one side of the market implies
blocking on the other side.-/
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
  exact and_comm

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
  letI := mkt.prefM m
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
  letI := mkt.prefW w
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
        letI := mkt.prefM m
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

/-! ## Finite preference-induced choice

The internal menu consists of `none` together with the partners whose
contracts are available. Its maximum is the agent's assignment from that
menu. -/

section InducedChoice

variable [Fintype M] [Fintype W]

set_option linter.unusedVariables false in
/-- The option menu available to man `m`. -/
noncomputable def menuM
    (mkt : MarriageMarket M W) (m : M) (Y : Set (M × W)) :
    Finset (Option W) := by
  classical
  exact Finset.univ.filter fun o =>
    o = none ∨ ∃ w, o = some w ∧ (m, w) ∈ Y

set_option linter.unusedVariables false in
/-- The option menu available to woman `w`. -/
noncomputable def menuW
    (mkt : MarriageMarket M W) (w : W) (Y : Set (M × W)) :
    Finset (Option M) := by
  classical
  exact Finset.univ.filter fun o =>
    o = none ∨ ∃ m, o = some m ∧ (m, w) ∈ Y

omit [Fintype M] in
theorem none_mem_menuM (m : M) (Y : Set (M × W)) :
    none ∈ mkt.menuM m Y := by
  classical
  simp [menuM]

omit [Fintype W] in
theorem none_mem_menuW (w : W) (Y : Set (M × W)) :
    none ∈ mkt.menuW w Y := by
  classical
  simp [menuW]

omit [Fintype M] in
theorem menuM_nonempty (m : M) (Y : Set (M × W)) :
    (mkt.menuM m Y).Nonempty :=
  ⟨none, mkt.none_mem_menuM m Y⟩

omit [Fintype W] in
theorem menuW_nonempty (w : W) (Y : Set (M × W)) :
    (mkt.menuW w Y).Nonempty :=
  ⟨none, mkt.none_mem_menuW w Y⟩

omit [Fintype M] in
@[simp] theorem some_mem_menuM {m : M} {w : W}
    {Y : Set (M × W)} :
    some w ∈ mkt.menuM m Y ↔ (m, w) ∈ Y := by
  classical
  simp [menuM]

omit [Fintype W] in
@[simp] theorem some_mem_menuW {m : M} {w : W}
    {Y : Set (M × W)} :
    some m ∈ mkt.menuW w Y ↔ (m, w) ∈ Y := by
  classical
  simp [menuW]

omit [Fintype M] in
theorem menuM_mono {m : M} {Y Z : Set (M × W)}
    (hYZ : Y ⊆ Z) :
    mkt.menuM m Y ⊆ mkt.menuM m Z := by
  classical
  intro o ho
  simp only [menuM, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
  rcases ho with rfl | ⟨w, rfl, hw⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨w, rfl, hYZ hw⟩

omit [Fintype W] in
theorem menuW_mono {w : W} {Y Z : Set (M × W)}
    (hYZ : Y ⊆ Z) :
    mkt.menuW w Y ⊆ mkt.menuW w Z := by
  classical
  intro o ho
  simp only [menuW, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
  rcases ho with rfl | ⟨m, rfl, hm⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨m, rfl, hYZ hm⟩

/-- Man `m`'s best option from `Y`, including remaining single. -/
noncomputable def bestM (m : M) (Y : Set (M × W)) : Option W := by
  letI := mkt.prefM m
  exact (mkt.menuM m Y).max' (mkt.menuM_nonempty m Y)

/-- Woman `w`'s best option from `Y`, including remaining single. -/
noncomputable def bestW (w : W) (Y : Set (M × W)) : Option M := by
  letI := mkt.prefW w
  exact (mkt.menuW w Y).max' (mkt.menuW_nonempty w Y)

omit [Fintype M] in
theorem bestM_mem_menuM (m : M) (Y : Set (M × W)) :
    mkt.bestM m Y ∈ mkt.menuM m Y := by
  classical
  letI := mkt.prefM m
  exact Finset.max'_mem _ _

omit [Fintype W] in
theorem bestW_mem_menuW (w : W) (Y : Set (M × W)) :
    mkt.bestW w Y ∈ mkt.menuW w Y := by
  classical
  letI := mkt.prefW w
  exact Finset.max'_mem _ _

omit [Fintype M] in
theorem none_le_bestM (m : M) (Y : Set (M × W)) :
    mkt.leM m none (mkt.bestM m Y) := by
  classical
  letI := mkt.prefM m
  exact Finset.le_max' _ _ (mkt.none_mem_menuM m Y)

omit [Fintype W] in
theorem none_le_bestW (w : W) (Y : Set (M × W)) :
    mkt.leW w none (mkt.bestW w Y) := by
  classical
  letI := mkt.prefW w
  exact Finset.le_max' _ _ (mkt.none_mem_menuW w Y)

omit [Fintype M] in
theorem le_bestM_of_mem {m : M} {Y : Set (M × W)} {o : Option W}
    (ho : o ∈ mkt.menuM m Y) :
    mkt.leM m o (mkt.bestM m Y) := by
  classical
  letI := mkt.prefM m
  exact Finset.le_max' _ _ ho

omit [Fintype W] in
theorem le_bestW_of_mem {w : W} {Y : Set (M × W)} {o : Option M}
    (ho : o ∈ mkt.menuW w Y) :
    mkt.leW w o (mkt.bestW w Y) := by
  classical
  letI := mkt.prefW w
  exact Finset.le_max' _ _ ho

omit [Fintype M] in
theorem bestM_mono {m : M} {Y Z : Set (M × W)}
    (hYZ : Y ⊆ Z) :
    mkt.leM m (mkt.bestM m Y) (mkt.bestM m Z) := by
  apply mkt.le_bestM_of_mem
  exact mkt.menuM_mono hYZ (mkt.bestM_mem_menuM m Y)

omit [Fintype W] in
theorem bestW_mono {w : W} {Y Z : Set (M × W)}
    (hYZ : Y ⊆ Z) :
    mkt.leW w (mkt.bestW w Y) (mkt.bestW w Z) := by
  apply mkt.le_bestW_of_mem
  exact mkt.menuW_mono hYZ (mkt.bestW_mem_menuW w Y)

/-- Man `m` chooses the contract corresponding to his best available
non-single option. -/
noncomputable def inducedChoiceM (m : M) : ChoiceFunction (M × W) where
  toFun Y := {p | p.1 = m ∧ some p.2 = mkt.bestM m Y}
  choose_subset := by
    intro Y p hp
    rcases hp with ⟨rfl, hp⟩
    have hmem := bestM_mem_menuM (mkt := mkt) p.1 Y
    rw [← hp] at hmem
    exact (some_mem_menuM (mkt := mkt)).mp hmem

/-- Woman `w` chooses the contract corresponding to her best available
non-single option. -/
noncomputable def inducedChoiceW (w : W) : ChoiceFunction (M × W) where
  toFun Y := {p | p.2 = w ∧ some p.1 = mkt.bestW w Y}
  choose_subset := by
    intro Y p hp
    rcases hp with ⟨rfl, hp⟩
    have hmem := bestW_mem_menuW (mkt := mkt) p.2 Y
    rw [← hp] at hmem
    exact (some_mem_menuW (mkt := mkt)).mp hmem

omit [Fintype M] in
@[simp] theorem mem_inducedChoiceM {m : M} {p : M × W}
    {Y : Set (M × W)} :
    p ∈ mkt.inducedChoiceM m Y ↔
      p.1 = m ∧ some p.2 = mkt.bestM m Y :=
  Iff.rfl

omit [Fintype W] in
@[simp] theorem mem_inducedChoiceW {w : W} {p : M × W}
    {Y : Set (M × W)} :
    p ∈ mkt.inducedChoiceW w Y ↔
      p.2 = w ∧ some p.1 = mkt.bestW w Y :=
  Iff.rfl

omit [Fintype M] in
/-- Choice characterized without mentioning `bestM`. -/
theorem mem_inducedChoiceM_iff {m : M} {w : W} {Y : Set (M × W)} :
    (m, w) ∈ mkt.inducedChoiceM m Y ↔
      (m, w) ∈ Y ∧
        mkt.leM m none (some w) ∧
        ∀ w', (m, w') ∈ Y → mkt.leM m (some w') (some w) := by
  classical
  letI := mkt.prefM m
  constructor
  · intro h
    have hbest : some w = mkt.bestM m Y :=
      (mkt.mem_inducedChoiceM.mp h).2
    refine ⟨(mkt.inducedChoiceM m).choose_subset Y h, ?_, ?_⟩
    · simpa [leM, hbest] using mkt.none_le_bestM m Y
    · intro w' hw'
      have hle := mkt.le_bestM_of_mem
        (m := m) (Y := Y) (o := some w') (mkt.some_mem_menuM.mpr hw')
      simpa [leM, ← hbest] using hle
  · rintro ⟨hwY, hnone, hmax⟩
    rw [mkt.mem_inducedChoiceM]
    have hub : mkt.bestM m Y ≤ some w := by
      refine Finset.max'_le (mkt.menuM m Y)
        (menuM_nonempty (mkt := mkt) m Y) (some w) ?_
      intro o ho
      simp only [menuM, Finset.mem_filter, Finset.mem_univ, true_and] at ho
      rcases ho with rfl | ⟨w', rfl, hw'⟩
      · exact hnone
      · exact hmax w' hw'
    have hlb : some w ≤ mkt.bestM m Y :=
      mkt.le_bestM_of_mem (mkt.some_mem_menuM.mpr hwY)
    exact ⟨rfl, le_antisymm hlb hub⟩

omit [Fintype W] in
/-- Choice characterized without mentioning `bestW`. -/
theorem mem_inducedChoiceW_iff {m : M} {w : W} {Y : Set (M × W)} :
    (m, w) ∈ mkt.inducedChoiceW w Y ↔
      (m, w) ∈ Y ∧
        mkt.leW w none (some m) ∧
        ∀ m', (m', w) ∈ Y → mkt.leW w (some m') (some m) := by
  classical
  letI := mkt.prefW w
  constructor
  · intro h
    have hbest : some m = mkt.bestW w Y :=
      (mkt.mem_inducedChoiceW.mp h).2
    refine ⟨(mkt.inducedChoiceW w).choose_subset Y h, ?_, ?_⟩
    · simpa [leW, hbest] using mkt.none_le_bestW w Y
    · intro m' hm'
      have hle := mkt.le_bestW_of_mem
        (w := w) (Y := Y) (o := some m') (mkt.some_mem_menuW.mpr hm')
      simpa [leW, ← hbest] using hle
  · rintro ⟨hmY, hnone, hmax⟩
    rw [mkt.mem_inducedChoiceW]
    have hub : mkt.bestW w Y ≤ some m := by
      refine Finset.max'_le (mkt.menuW w Y)
        (menuW_nonempty (mkt := mkt) w Y) (some m) ?_
      intro o ho
      simp only [menuW, Finset.mem_filter, Finset.mem_univ, true_and] at ho
      rcases ho with rfl | ⟨m', rfl, hm'⟩
      · exact hnone
      · exact hmax m' hm'
    have hlb : some m ≤ mkt.bestW w Y :=
      mkt.le_bestW_of_mem (mkt.some_mem_menuW.mpr hmY)
    exact ⟨rfl, le_antisymm hlb hub⟩

omit [Fintype M] in
theorem unitDemand_inducedChoiceM (m : M) :
    (mkt.inducedChoiceM m).UnitDemand := by
  intro Y p hp q hq
  obtain ⟨hp1, hp2⟩ := mkt.mem_inducedChoiceM.mp hp
  obtain ⟨hq1, hq2⟩ := mkt.mem_inducedChoiceM.mp hq
  apply Prod.ext
  · exact hp1.trans hq1.symm
  · exact Option.some.inj (hp2.trans hq2.symm)

omit [Fintype W] in
theorem unitDemand_inducedChoiceW (w : W) :
    (mkt.inducedChoiceW w).UnitDemand := by
  intro Y p hp q hq
  obtain ⟨hp2, hp1⟩ := mkt.mem_inducedChoiceW.mp hp
  obtain ⟨hq2, hq1⟩ := mkt.mem_inducedChoiceW.mp hq
  apply Prod.ext
  · exact Option.some.inj (hp1.trans hq1.symm)
  · exact hp2.trans hq2.symm

omit [Fintype M] in
theorem bestM_eq_of_choice_subset {m : M} {Y Z : Set (M × W)}
    (hchoice : mkt.inducedChoiceM m Y ⊆ Z) (hZY : Z ⊆ Y) :
    mkt.bestM m Z = mkt.bestM m Y := by
  classical
  letI := mkt.prefM m
  have hle : mkt.bestM m Z ≤ mkt.bestM m Y :=
    mkt.bestM_mono hZY
  cases hY : mkt.bestM m Y with
  | none =>
      rw [hY] at hle
      exact le_antisymm hle (mkt.none_le_bestM m Z)
  | some w =>
      rw [hY] at hle
      have hwY : (m, w) ∈ mkt.inducedChoiceM m Y := by
        rw [mkt.mem_inducedChoiceM]
        exact ⟨rfl, hY.symm⟩
      have hwZ : (m, w) ∈ Z := hchoice hwY
      have hge : some w ≤ mkt.bestM m Z :=
        mkt.le_bestM_of_mem (mkt.some_mem_menuM.mpr hwZ)
      exact le_antisymm hle hge

omit [Fintype W] in
theorem bestW_eq_of_choice_subset {w : W} {Y Z : Set (M × W)}
    (hchoice : mkt.inducedChoiceW w Y ⊆ Z) (hZY : Z ⊆ Y) :
    mkt.bestW w Z = mkt.bestW w Y := by
  classical
  letI := mkt.prefW w
  have hle : mkt.bestW w Z ≤ mkt.bestW w Y :=
    mkt.bestW_mono hZY
  cases hY : mkt.bestW w Y with
  | none =>
      rw [hY] at hle
      exact le_antisymm hle (mkt.none_le_bestW w Z)
  | some m =>
      rw [hY] at hle
      have hmY : (m, w) ∈ mkt.inducedChoiceW w Y := by
        rw [mkt.mem_inducedChoiceW]
        exact ⟨rfl, hY.symm⟩
      have hmZ : (m, w) ∈ Z := hchoice hmY
      have hge : some m ≤ mkt.bestW w Z :=
        mkt.le_bestW_of_mem (mkt.some_mem_menuW.mpr hmZ)
      exact le_antisymm hle hge

omit [Fintype M] in
theorem consistent_inducedChoiceM (m : M) :
    (mkt.inducedChoiceM m).Consistent := by
  intro Y Z hchoice hZY
  ext p
  simp only [mem_inducedChoiceM]
  rw [mkt.bestM_eq_of_choice_subset hchoice hZY]

omit [Fintype W] in
theorem consistent_inducedChoiceW (w : W) :
    (mkt.inducedChoiceW w).Consistent := by
  intro Y Z hchoice hZY
  ext p
  simp only [mem_inducedChoiceW]
  rw [mkt.bestW_eq_of_choice_subset hchoice hZY]

/-! ## The induced contracts market -/

/-- The contracts market induced by a marriage market.

Women are buyers and men are sellers, so seller-proposing deferred acceptance
is man-proposing deferred acceptance. -/
noncomputable def toMarket : Market W M (M × W) where
  buyer := Prod.snd
  seller := Prod.fst
  choiceB := mkt.inducedChoiceW
  choiceS := mkt.inducedChoiceM
  buyer_eq_of_mem := by
    intro w Y p hp
    exact (mkt.mem_inducedChoiceW.mp hp).1
  seller_eq_of_mem := by
    intro m Y p hp
    exact (mkt.mem_inducedChoiceM.mp hp).1

@[simp] theorem toMarket_buyer (p : M × W) :
    mkt.toMarket.buyer p = p.2 :=
  rfl

@[simp] theorem toMarket_seller (p : M × W) :
    mkt.toMarket.seller p = p.1 :=
  rfl

@[simp] theorem toMarket_choiceB (w : W) :
    mkt.toMarket.choiceB w = mkt.inducedChoiceW w :=
  rfl

@[simp] theorem toMarket_choiceS (m : M) :
    mkt.toMarket.choiceS m = mkt.inducedChoiceM m :=
  rfl

theorem consistent_toMarket : mkt.toMarket.Consistent :=
  ⟨mkt.consistent_inducedChoiceW, mkt.consistent_inducedChoiceM⟩

theorem substitutable_toMarket : mkt.toMarket.Substitutable :=
  ⟨fun w =>
      (mkt.unitDemand_inducedChoiceW w).substitutable
        (mkt.consistent_inducedChoiceW w),
    fun m =>
      (mkt.unitDemand_inducedChoiceM m).substitutable
        (mkt.consistent_inducedChoiceM m)⟩

theorem sizeMonotone_toMarket : mkt.toMarket.SizeMonotone :=
  ⟨fun w =>
      (mkt.unitDemand_inducedChoiceW w).sizeMonotone
        (mkt.consistent_inducedChoiceW w),
    fun m =>
      (mkt.unitDemand_inducedChoiceM m).sizeMonotone
        (mkt.consistent_inducedChoiceM m)⟩

/-! ## Graphs of partial matchings -/

set_option linter.unusedVariables false in
/-- The contract graph of a partial matching.

The market parameter is intentionally explicit even though the graph itself
does not depend on preferences. This preserves the downstream API
`mkt.graphOf μ`. -/
def graphOf (mkt : MarriageMarket M W) (μ : M ≃. W) : Set (M × W) :=
  {p | μ p.1 = some p.2}

omit [Fintype M] [Fintype W] in
@[simp] theorem mem_graphOf {μ : M ≃. W} {m : M} {w : W} :
    (m, w) ∈ mkt.graphOf μ ↔ μ m = some w :=
  Iff.rfl

omit [Fintype M] [Fintype W] in
@[simp] theorem mem_graphOf_symm {μ : M ≃. W} {m : M} {w : W} :
    (m, w) ∈ mkt.graphOf μ ↔ μ.symm w = some m := by
  change μ m = some w ↔ μ.symm w = some m
  exact (μ.eq_some_iff).symm

omit [Fintype M] [Fintype W] in
theorem graphOf_rightUnique (μ : M ≃. W) {m : M} {w w' : W}
    (hw : (m, w) ∈ mkt.graphOf μ)
    (hw' : (m, w') ∈ mkt.graphOf μ) :
    w = w' := by
  have hwEq : μ m = some w :=
    mkt.mem_graphOf.mp hw
  have hwEq' : μ m = some w' :=
    mkt.mem_graphOf.mp hw'
  exact Option.some.inj (hwEq.symm.trans hwEq')

omit [Fintype M] [Fintype W] in
theorem graphOf_leftUnique (μ : M ≃. W) {m m' : M} {w : W}
    (hm : (m, w) ∈ mkt.graphOf μ)
    (hm' : (m', w) ∈ mkt.graphOf μ) :
    m = m' := by
  have hmEq : μ.symm w = some m :=
    mkt.mem_graphOf_symm.mp hm
  have hmEq' : μ.symm w = some m' :=
    mkt.mem_graphOf_symm.mp hm'
  exact Option.some.inj (hmEq.symm.trans hmEq')

omit [Fintype M] [Fintype W] in
theorem graphOf_injective : Function.Injective mkt.graphOf := by
  intro μ ν h
  apply PEquiv.ext
  intro m
  have hm : ∀ w, μ m = some w ↔ ν m = some w := by
    intro w
    change (m, w) ∈ mkt.graphOf μ ↔ (m, w) ∈ mkt.graphOf ν
    rw [h]
  cases hμ : μ m with
  | none =>
      cases hν : ν m with
      | none => rfl
      | some w =>
          have hbad := (hm w).mpr hν
          rw [hμ] at hbad
          cases hbad
  | some w => exact ((hm w).mp hμ).symm

omit [Fintype M] [Fintype W] in
@[simp] theorem graphOf_symm (μ : M ≃. W) :
    mkt.symm.graphOf μ.symm = Prod.swap ⁻¹' mkt.graphOf μ := by
  ext p
  exact μ.eq_some_iff

/-! ## Individual rationality translation -/

/-- A man's individual rationality implies that he chooses his entire
side of the matching graph. -/
theorem choiceM_graphOf_eq_side
    {μ : M ≃. W} {m : M}
    (hIR : mkt.IndividuallyRationalForM μ m) :
    mkt.toMarket.choiceS m (mkt.graphOf μ) =
      mkt.toMarket.sellerSide m (mkt.graphOf μ) := by
  ext p
  rcases p with ⟨m', w⟩
  constructor
  · intro hp
    have hpY :=
      (mkt.toMarket.choiceS m).choose_subset (mkt.graphOf μ) hp
    exact ⟨hpY, (mkt.mem_inducedChoiceM.mp hp).1⟩
  · rintro ⟨hpY, hm'⟩
    obtain rfl : m = m' := hm'.symm
    rw [mkt.toMarket_choiceS, mkt.mem_inducedChoiceM_iff]
    have hμ : μ m = some w := mkt.mem_graphOf.mp hpY
    refine ⟨hpY, ?_, ?_⟩
    · have h : mkt.leM m none (μ m) := hIR
      rwa [hμ] at h
    · intro w' hw'
      letI := mkt.prefM m
      have hww' : w' = w := mkt.graphOf_rightUnique μ hw' hpY
      exact le_of_eq (congrArg Option.some hww')

/-- A woman's individual rationality implies that she chooses her entire
side of the matching graph. -/
theorem choiceW_graphOf_eq_side
    {μ : M ≃. W} {w : W}
    (hIR : mkt.IndividuallyRationalForW μ w) :
    mkt.toMarket.choiceB w (mkt.graphOf μ) =
      mkt.toMarket.buyerSide w (mkt.graphOf μ) := by
  ext p
  rcases p with ⟨m, w'⟩
  constructor
  · intro hp
    have hpY :=
      (mkt.toMarket.choiceB w).choose_subset (mkt.graphOf μ) hp
    exact ⟨hpY, (mkt.mem_inducedChoiceW.mp hp).1⟩
  · rintro ⟨hpY, hw'⟩
    obtain rfl : w = w' := hw'.symm
    rw [mkt.toMarket_choiceB, mkt.mem_inducedChoiceW_iff]
    have hμ : μ.symm w = some m := mkt.mem_graphOf_symm.mp hpY
    refine ⟨hpY, ?_, ?_⟩
    · have h : mkt.leW w none (μ.symm w) := hIR
      rwa [hμ] at h
    · intro m' hm'
      letI := mkt.prefW w
      have hmm' : m' = m := mkt.graphOf_leftUnique μ hm' hpY
      exact le_of_eq (congrArg Option.some hmm')

theorem individuallyRational_graphOf
    {μ : M ≃. W} (hIR : mkt.IndividuallyRational μ) :
    mkt.toMarket.IndRational (mkt.graphOf μ) :=
  ⟨fun w => mkt.choiceW_graphOf_eq_side (hIR.2 w),
    fun m => mkt.choiceM_graphOf_eq_side (hIR.1 m)⟩

theorem individuallyRational_of_graphOf
    {μ : M ≃. W}
    (hIR : mkt.toMarket.IndRational (mkt.graphOf μ)) :
    mkt.IndividuallyRational μ := by
  constructor
  · intro m
    change mkt.leM m none (μ m)
    letI := mkt.prefM m
    cases hμ : μ m with
    | none =>
        exact le_rfl
    | some w =>
        have hw : (m, w) ∈ mkt.graphOf μ :=
          mkt.mem_graphOf.mpr hμ
        have hwSide :
            (m, w) ∈ mkt.toMarket.sellerSide m (mkt.graphOf μ) :=
          ⟨hw, rfl⟩
        have hwChoice :
            (m, w) ∈ mkt.toMarket.choiceS m (mkt.graphOf μ) := by
          rw [hIR.2 m]
          exact hwSide
        exact (mkt.mem_inducedChoiceM_iff.mp hwChoice).2.1
  · intro w
    change mkt.leW w none (μ.symm w)
    letI := mkt.prefW w
    cases hμ : μ.symm w with
    | none =>
        exact le_rfl
    | some m =>
        have hw : (m, w) ∈ mkt.graphOf μ :=
          mkt.mem_graphOf_symm.mpr hμ
        have hwSide :
            (m, w) ∈ mkt.toMarket.buyerSide w (mkt.graphOf μ) :=
          ⟨hw, rfl⟩
        have hwChoice :
            (m, w) ∈ mkt.toMarket.choiceB w (mkt.graphOf μ) := by
          rw [hIR.1 w]
          exact hwSide
        exact (mkt.mem_inducedChoiceW_iff.mp hwChoice).2.1

theorem individuallyRational_iff_indRational_graphOf (μ : M ≃. W) :
    mkt.IndividuallyRational μ ↔
      mkt.toMarket.IndRational (mkt.graphOf μ) :=
  ⟨mkt.individuallyRational_graphOf,
    mkt.individuallyRational_of_graphOf⟩

/-! ## Singleton acceptance and blocking pairs -/

/-- An individually rational man accepts a new contract precisely when
his side of the blocking condition holds. -/
theorem mem_choiceM_insert_graphOf_iff
    {μ : M ≃. W} {m : M} {w : W}
    (hIR : mkt.IndividuallyRationalForM μ m)
    (hnew : μ m ≠ some w) :
    (m, w) ∈ mkt.toMarket.choiceS m
        (insert (m, w) (mkt.graphOf μ)) ↔
      mkt.BlocksM μ m w := by
  classical
  letI := mkt.prefM m
  unfold BlocksM
  rw [mkt.toMarket_choiceS, mkt.mem_inducedChoiceM_iff]
  constructor
  · rintro ⟨-, hnone, hmax⟩
    have hle : μ m ≤ some w := by
      cases hμ : μ m with
      | none => exact hnone
      | some w' =>
          exact hmax w' (Set.mem_insert_iff.mpr
            (Or.inr (mkt.mem_graphOf.mpr hμ)))
    exact lt_of_le_of_ne hle hnew
  · intro hlt
    refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · exact le_trans hIR (le_of_lt hlt)
    · intro w' hw'
      rcases Set.mem_insert_iff.mp hw' with hw' | hw'
      · exact le_of_eq (congrArg Option.some (congrArg Prod.snd hw'))
      · have hμ : μ m = some w' := mkt.mem_graphOf.mp hw'
        have h := le_of_lt hlt
        rw [hμ] at h
        exact h

/-- An individually rational woman accepts a new contract precisely when
her side of the blocking condition holds. -/
theorem mem_choiceW_insert_graphOf_iff
    {μ : M ≃. W} {m : M} {w : W}
    (hIR : mkt.IndividuallyRationalForW μ w)
    (hnew : μ.symm w ≠ some m) :
    (m, w) ∈ mkt.toMarket.choiceB w
        (insert (m, w) (mkt.graphOf μ)) ↔
      mkt.BlocksW μ w m := by
  classical
  letI := mkt.prefW w
  unfold BlocksW
  rw [mkt.toMarket_choiceB, mkt.mem_inducedChoiceW_iff]
  constructor
  · rintro ⟨-, hnone, hmax⟩
    have hle : μ.symm w ≤ some m := by
      cases hμ : μ.symm w with
      | none => exact hnone
      | some m' =>
          exact hmax m' (Set.mem_insert_iff.mpr
            (Or.inr (mkt.mem_graphOf_symm.mpr hμ)))
    exact lt_of_le_of_ne hle hnew
  · intro hlt
    refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · exact le_trans hIR (le_of_lt hlt)
    · intro m' hm'
      rcases Set.mem_insert_iff.mp hm' with hm' | hm'
      · exact le_of_eq (congrArg Option.some (congrArg Prod.fst hm'))
      · have hμ : μ.symm w = some m' := mkt.mem_graphOf_symm.mp hm'
        have h := le_of_lt hlt
        rw [hμ] at h
        exact h

theorem blocks_singleton_graphOf_iff
    {μ : M ≃. W} (hIR : mkt.IndividuallyRational μ)
    {m : M} {w : W} :
    mkt.toMarket.Blocks (mkt.graphOf μ) {(m, w)} ↔
      mkt.IsBlockingPair μ m w := by
  rw [mkt.toMarket.blocks_singleton_iff]
  constructor
  · rintro ⟨hnew, hw, hm⟩
    have hnewM : μ m ≠ some w := fun h =>
      hnew (mkt.mem_graphOf.mpr h)
    have hnewW : μ.symm w ≠ some m := fun h =>
      hnew (mkt.mem_graphOf_symm.mpr h)
    exact ⟨
      (mkt.mem_choiceM_insert_graphOf_iff (hIR.1 m) hnewM).mp hm,
      (mkt.mem_choiceW_insert_graphOf_iff (hIR.2 w) hnewW).mp hw⟩
  · rintro ⟨hm, hw⟩
    have hnewM : μ m ≠ some w := by
      letI := mkt.prefM m
      exact ne_of_lt hm
    have hnewW : μ.symm w ≠ some m := by
      letI := mkt.prefW w
      exact ne_of_lt hw
    refine ⟨?_, ?_, ?_⟩
    · intro hmem
      exact hnewM (mkt.mem_graphOf.mp hmem)
    · exact
        (mkt.mem_choiceW_insert_graphOf_iff (hIR.2 w) hnewW).mpr hw
    · exact
        (mkt.mem_choiceM_insert_graphOf_iff (hIR.1 m) hnewM).mpr hm

/-- Classical stability is exactly stability of the matching graph in the
induced contracts market. -/
theorem isStableMatching_iff_stable_graphOf (μ : M ≃. W) :
    mkt.IsStableMatching μ ↔
      mkt.toMarket.Stable (mkt.graphOf μ) := by
  let hsub := mkt.substitutable_toMarket
  let hcons := mkt.consistent_toMarket
  rw [← mkt.toMarket.pairwiseStable_iff_stable hsub hcons]
  constructor
  · rintro ⟨hIR, hno⟩
    refine ⟨mkt.individuallyRational_graphOf hIR, ?_⟩
    rintro ⟨m, w⟩
    rw [mkt.blocks_singleton_graphOf_iff hIR]
    exact hno.1 m w
  · rintro ⟨hIRg, hno⟩
    have hIR : mkt.IndividuallyRational μ :=
      mkt.individuallyRational_of_graphOf hIRg
    refine ⟨hIR, ?_⟩
    apply (mkt.unblocked_iff_no_blockingPair μ).mpr
    intro m w
    rw [← mkt.blocks_singleton_graphOf_iff hIR]
    exact hno (m, w)

/-! ## Recovering a partial matching from a stable outcome -/

theorem seller_fiber_subsingleton {A : Set (M × W)}
    (hA : mkt.toMarket.IndRational A) (m : M) :
    {w | (m, w) ∈ A}.Subsingleton := by
  intro w hw w' hw'
  have h1 : (m, w) ∈ mkt.toMarket.choiceS m A := by
    rw [hA.2 m]
    exact ⟨hw, rfl⟩
  have h2 : (m, w') ∈ mkt.toMarket.choiceS m A := by
    rw [hA.2 m]
    exact ⟨hw', rfl⟩
  have hp :=
    mkt.unitDemand_inducedChoiceM m A h1 h2
  exact congrArg Prod.snd hp

theorem buyer_fiber_subsingleton {A : Set (M × W)}
    (hA : mkt.toMarket.IndRational A) (w : W) :
    {m | (m, w) ∈ A}.Subsingleton := by
  intro m hm m' hm'
  have h1 : (m, w) ∈ mkt.toMarket.choiceB w A := by
    rw [hA.1 w]
    exact ⟨hm, rfl⟩
  have h2 : (m', w) ∈ mkt.toMarket.choiceB w A := by
    rw [hA.1 w]
    exact ⟨hm', rfl⟩
  have hp :=
    mkt.unitDemand_inducedChoiceW w A h1 h2
  exact congrArg Prod.fst hp

set_option linter.unusedVariables false in
/-- The partner of `m` in outcome `A`, if any.

The market parameter is intentionally explicit even though the partner map
itself does not depend on preferences. This preserves the downstream API
`mkt.partnerMOf A m`. -/
noncomputable def partnerMOf
    (mkt : MarriageMarket M W) (A : Set (M × W)) (m : M) : Option W := by
  classical
  exact if h : ∃ w, (m, w) ∈ A then
    some (Classical.choose h)
  else
    none

set_option linter.unusedVariables false in
/-- The partner of `w` in outcome `A`, if any. See `partnerMOf` regarding the
explicit market parameter. -/
noncomputable def partnerWOf
    (mkt : MarriageMarket M W) (A : Set (M × W)) (w : W) : Option M := by
  classical
  exact if h : ∃ m, (m, w) ∈ A then
    some (Classical.choose h)
  else
    none

omit [Fintype M] in
theorem partnerMOf_eq_some_iff {A : Set (M × W)}
    (hsub : ∀ m, {w | (m, w) ∈ A}.Subsingleton)
    {m : M} {w : W} :
    mkt.partnerMOf A m = some w ↔ (m, w) ∈ A := by
  classical
  unfold partnerMOf
  split_ifs with h
  · constructor
    · intro heq
      have hw : Classical.choose h = w := Option.some.inj heq
      simpa [hw] using Classical.choose_spec h
    · intro hw
      have heq : Classical.choose h = w :=
        hsub m (Classical.choose_spec h) hw
      simp [heq]
  · constructor
    · simp
    · intro hw
      exact (h ⟨w, hw⟩).elim

omit [Fintype W] in
theorem partnerWOf_eq_some_iff {A : Set (M × W)}
    (hsub : ∀ w, {m | (m, w) ∈ A}.Subsingleton)
    {m : M} {w : W} :
    mkt.partnerWOf A w = some m ↔ (m, w) ∈ A := by
  classical
  unfold partnerWOf
  split_ifs with h
  · constructor
    · intro heq
      have hm : Classical.choose h = m := Option.some.inj heq
      simpa [hm] using Classical.choose_spec h
    · intro hm
      have heq : Classical.choose h = m :=
        hsub w (Classical.choose_spec h) hm
      simp [heq]
  · constructor
    · simp
    · intro hm
      exact (h ⟨m, hm⟩).elim

/-- An individually rational unit-demand outcome induces a partial matching. -/
noncomputable def matchingOfIndRational {A : Set (M × W)}
    (hA : mkt.toMarket.IndRational A) : M ≃. W where
  toFun := mkt.partnerMOf A
  invFun := mkt.partnerWOf A
  inv := by
    intro m w
    exact
      (mkt.partnerWOf_eq_some_iff
        (mkt.buyer_fiber_subsingleton hA)).trans
      (mkt.partnerMOf_eq_some_iff
        (mkt.seller_fiber_subsingleton hA)).symm

/-- A stable contracts outcome induces a partial matching. -/
noncomputable def matchingOfStable {A : Set (M × W)}
    (hA : mkt.toMarket.Stable A) : M ≃. W :=
  mkt.matchingOfIndRational hA.1

@[simp] theorem graphOf_matchingOfIndRational {A : Set (M × W)}
    (hA : mkt.toMarket.IndRational A) :
    mkt.graphOf (mkt.matchingOfIndRational hA) = A := by
  ext p
  rcases p with ⟨m, w⟩
  change mkt.partnerMOf A m = some w ↔ (m, w) ∈ A
  exact mkt.partnerMOf_eq_some_iff
    (mkt.seller_fiber_subsingleton hA)

@[simp] theorem graphOf_matchingOfStable {A : Set (M × W)}
    (hA : mkt.toMarket.Stable A) :
    mkt.graphOf (mkt.matchingOfStable hA) = A :=
  mkt.graphOf_matchingOfIndRational hA.1

theorem stable_matchingOfStable {A : Set (M × W)}
    (hA : mkt.toMarket.Stable A) :
    mkt.IsStableMatching (mkt.matchingOfStable hA) := by
  rw [mkt.isStableMatching_iff_stable_graphOf,
    mkt.graphOf_matchingOfStable hA]
  exact hA

@[simp] theorem matchingOfStable_graphOf {μ : M ≃. W}
    (hμ : mkt.IsStableMatching μ) :
    mkt.matchingOfStable ((mkt.isStableMatching_iff_stable_graphOf μ).mp hμ) = μ := by
  apply mkt.graphOf_injective
  exact mkt.graphOf_matchingOfStable _

/-! ## Gale–Shapley existence -/

/-- Existence of a stable marriage matching. -/
theorem exists_stableMatching :
    ∃ μ : M ≃. W, mkt.IsStableMatching μ := by
  let hsub := mkt.substitutable_toMarket
  let hcons := mkt.consistent_toMarket
  obtain ⟨A, hA⟩ := mkt.toMarket.exists_stable hsub hcons
  exact ⟨mkt.matchingOfStable hA, mkt.stable_matchingOfStable hA⟩

/-! ## Pointwise interpretation of seller choice -/

theorem leM_of_sellerChosen_graphOf
    {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRational μ)
    (hν : mkt.IndividuallyRational ν)
    (hchosen :
      mkt.toMarket.SellerChosen (mkt.graphOf μ) (mkt.graphOf ν))
    (m : M) :
    mkt.leM m (ν m) (μ m) := by
  classical
  letI := mkt.prefM m
  cases hμm : μ m with
  | none =>
      cases hνm : ν m with
      | none =>
          exact le_rfl
      | some w =>
          exfalso
          have hle0 : (none : Option W) ≤ some w := by
            have h : mkt.leM m none (ν m) := hν.1 m
            rw [hνm] at h
            exact h
          have hlt : (none : Option W) < some w :=
            lt_of_le_of_ne hle0 (by simp)
          have hwν : (m, w) ∈ mkt.graphOf ν :=
            mkt.mem_graphOf.mpr hνm
          have hwChoice :
              (m, w) ∈ mkt.toMarket.choiceS m
                (mkt.graphOf μ ∪ mkt.graphOf ν) := by
            rw [mkt.toMarket_choiceS, mkt.mem_inducedChoiceM_iff]
            refine ⟨Or.inr hwν, le_of_lt hlt, ?_⟩
            intro w' hw'
            rcases hw' with hwμ | hwν'
            · exfalso
              have hEq : μ m = some w' :=
                mkt.mem_graphOf.mp hwμ
              rw [hμm] at hEq
              cases hEq
            · have hν' : ν m = some w' :=
                mkt.mem_graphOf.mp hwν'
              have hww' : w' = w :=
                Option.some.inj (hν'.symm.trans hνm)
              exact le_of_eq (congrArg Option.some hww')
          have hwSide :
              (m, w) ∈
                mkt.toMarket.sellerSide m (mkt.graphOf μ) := by
            rw [← hchosen m]
            exact hwChoice
          have hwμ : μ m = some w :=
            mkt.mem_graphOf.mp hwSide.1
          rw [hμm] at hwμ
          cases hwμ
  | some w =>
      have hwμ : (m, w) ∈ mkt.graphOf μ :=
        mkt.mem_graphOf.mpr hμm
      have hwSide :
          (m, w) ∈ mkt.toMarket.sellerSide m (mkt.graphOf μ) :=
        ⟨hwμ, rfl⟩
      have hwChoice :
          (m, w) ∈ mkt.toMarket.choiceS m
            (mkt.graphOf μ ∪ mkt.graphOf ν) := by
        rw [hchosen m]
        exact hwSide
      have hmax :=
        (mkt.mem_inducedChoiceM_iff.mp hwChoice).2.2
      cases hνm : ν m with
      | none =>
          have h : mkt.leM m none (μ m) := hμ.1 m
          rw [hμm] at h
          exact h
      | some w' =>
          have hw'ν : (m, w') ∈ mkt.graphOf ν :=
            mkt.mem_graphOf.mpr hνm
          exact hmax w' (Or.inr hw'ν)

/-- Pointwise interpretation of buyer unanimity in the contracts market. -/
theorem leW_of_buyerChosen_graphOf
    {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRational μ)
    (hν : mkt.IndividuallyRational ν)
    (hchosen :
      mkt.toMarket.BuyerChosen (mkt.graphOf μ) (mkt.graphOf ν))
    (w : W) :
    mkt.leW w (ν.symm w) (μ.symm w) := by
  classical
  letI := mkt.prefW w
  cases hμw : μ.symm w with
  | none =>
      cases hνw : ν.symm w with
      | none => exact le_rfl
      | some m =>
          exfalso
          have hle0 : (none : Option M) ≤ some m := by
            have h : mkt.leW w none (ν.symm w) := hν.2 w
            rwa [hνw] at h
          have hmν : (m, w) ∈ mkt.graphOf ν :=
            mkt.mem_graphOf_symm.mpr hνw
          have hmChoice :
              (m, w) ∈ mkt.toMarket.choiceB w
                (mkt.graphOf μ ∪ mkt.graphOf ν) := by
            rw [mkt.toMarket_choiceB, mkt.mem_inducedChoiceW_iff]
            refine ⟨Or.inr hmν, hle0, ?_⟩
            intro m' hm'
            rcases hm' with hmμ | hmν'
            · have hEq : μ.symm w = some m' :=
                mkt.mem_graphOf_symm.mp hmμ
              rw [hμw] at hEq
              cases hEq
            · have hν' : ν.symm w = some m' :=
                mkt.mem_graphOf_symm.mp hmν'
              exact le_of_eq (hν'.symm.trans hνw)
          have hmSide :
              (m, w) ∈ mkt.toMarket.buyerSide w (mkt.graphOf μ) := by
            rw [← hchosen w]
            exact hmChoice
          have hmμ : μ.symm w = some m :=
            mkt.mem_graphOf_symm.mp hmSide.1
          rw [hμw] at hmμ
          cases hmμ
  | some m =>
      have hmμ : (m, w) ∈ mkt.graphOf μ :=
        mkt.mem_graphOf_symm.mpr hμw
      have hmChoice :
          (m, w) ∈ mkt.toMarket.choiceB w
            (mkt.graphOf μ ∪ mkt.graphOf ν) := by
        rw [hchosen w]
        exact ⟨hmμ, rfl⟩
      have hmax := (mkt.mem_inducedChoiceW_iff.mp hmChoice).2.2
      cases hνw : ν.symm w with
      | none =>
          have h : mkt.leW w none (μ.symm w) := hμ.2 w
          rwa [hμw] at h
      | some m' =>
          exact hmax m' (Or.inr (mkt.mem_graphOf_symm.mpr hνw))

/-- Unanimous classical preferences recover the seller-choice relation. -/
theorem sellerChosen_graphOf_of_menWeaklyPrefer {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRational μ) (h : mkt.MenWeaklyPrefer μ ν) :
    mkt.toMarket.SellerChosen (mkt.graphOf μ) (mkt.graphOf ν) := by
  intro m
  letI := mkt.prefM m
  ext p
  rcases p with ⟨m', w⟩
  constructor
  · intro hp
    have hown : m' = m := (mkt.mem_inducedChoiceM.mp hp).1
    subst m'
    obtain ⟨hmem, hnone, hmax⟩ := mkt.mem_inducedChoiceM_iff.mp hp
    have hle : mkt.leM m (some w) (μ m) := by
      rcases hmem with hmem | hmem
      · exact le_of_eq (mkt.mem_graphOf.mp hmem).symm
      · simpa only [mkt.mem_graphOf.mp hmem] using h m
    have hge : mkt.leM m (μ m) (some w) := by
      cases hμm : μ m with
      | none => exact hnone
      | some w' => exact hmax w' (Or.inl (mkt.mem_graphOf.mpr hμm))
    exact ⟨mkt.mem_graphOf.mpr (le_antisymm hge hle), rfl⟩
  · rintro ⟨hp, hown⟩
    obtain rfl : m = m' := hown.symm
    have hμm := mkt.mem_graphOf.mp hp
    rw [mkt.toMarket_choiceS, mkt.mem_inducedChoiceM_iff]
    refine ⟨Or.inl hp, ?_, ?_⟩
    · simpa only [IndividuallyRationalForM, hμm] using hμ.1 m
    · intro w' hw'
      rcases hw' with hw' | hw'
      · exact le_of_eq ((mkt.mem_graphOf.mp hw').symm.trans hμm)
      · simpa only [mkt.mem_graphOf.mp hw', hμm] using h m

/-- Unanimous classical preferences recover the buyer-choice relation. -/
theorem buyerChosen_graphOf_of_womenWeaklyPrefer {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRational μ) (h : mkt.WomenWeaklyPrefer μ ν) :
    mkt.toMarket.BuyerChosen (mkt.graphOf μ) (mkt.graphOf ν) := by
  intro w
  letI := mkt.prefW w
  ext p
  rcases p with ⟨m, w'⟩
  constructor
  · intro hp
    have hown : w' = w := (mkt.mem_inducedChoiceW.mp hp).1
    subst w'
    obtain ⟨hmem, hnone, hmax⟩ := mkt.mem_inducedChoiceW_iff.mp hp
    have hle : mkt.leW w (some m) (μ.symm w) := by
      rcases hmem with hmem | hmem
      · exact le_of_eq (mkt.mem_graphOf_symm.mp hmem).symm
      · simpa only [mkt.mem_graphOf_symm.mp hmem] using h w
    have hge : mkt.leW w (μ.symm w) (some m) := by
      cases hμw : μ.symm w with
      | none => exact hnone
      | some m' => exact hmax m' (Or.inl (mkt.mem_graphOf_symm.mpr hμw))
    exact ⟨mkt.mem_graphOf_symm.mpr (le_antisymm hge hle), rfl⟩
  · rintro ⟨hp, hown⟩
    obtain rfl : w = w' := hown.symm
    have hμw := mkt.mem_graphOf_symm.mp hp
    rw [mkt.toMarket_choiceB, mkt.mem_inducedChoiceW_iff]
    refine ⟨Or.inl hp, ?_, ?_⟩
    · simpa only [IndividuallyRationalForW, hμw] using hμ.2 w
    · intro m' hm'
      rcases hm' with hm' | hm'
      · exact le_of_eq ((mkt.mem_graphOf_symm.mp hm').symm.trans hμw)
      · simpa only [mkt.mem_graphOf_symm.mp hm', hμw] using h w

/-- Exact dictionary between the generalized and classical men's preference orders. -/
theorem sellerChosen_graphOf_iff_menWeaklyPrefer {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRational μ) (hν : mkt.IndividuallyRational ν) :
    mkt.toMarket.SellerChosen (mkt.graphOf μ) (mkt.graphOf ν) ↔
      mkt.MenWeaklyPrefer μ ν :=
  ⟨fun h => mkt.leM_of_sellerChosen_graphOf hμ hν h,
    mkt.sellerChosen_graphOf_of_menWeaklyPrefer hμ⟩

/-- Exact dictionary between the generalized and classical women's preference orders. -/
theorem buyerChosen_graphOf_iff_womenWeaklyPrefer {μ ν : M ≃. W}
    (hμ : mkt.IndividuallyRational μ) (hν : mkt.IndividuallyRational ν) :
    mkt.toMarket.BuyerChosen (mkt.graphOf μ) (mkt.graphOf ν) ↔
      mkt.WomenWeaklyPrefer μ ν :=
  ⟨fun h => mkt.leW_of_buyerChosen_graphOf hμ hν h,
    mkt.buyerChosen_graphOf_of_womenWeaklyPrefer hμ⟩

/-- The contracts proof gives exactly the same opposition statement as the
independent classical blocking-pair proof above. The graph dictionaries
identify the two orders, not merely the optimal outcomes. -/
theorem menWeaklyPrefer_iff_womenWeaklyPrefer_via_contracts {μ ν : M ≃. W}
    (hμ : mkt.IsStableMatching μ) (hν : mkt.IsStableMatching ν) :
    mkt.MenWeaklyPrefer μ ν ↔ mkt.WomenWeaklyPrefer ν μ := by
  rw [← mkt.sellerChosen_graphOf_iff_menWeaklyPrefer hμ.1 hν.1,
    ← mkt.buyerChosen_graphOf_iff_womenWeaklyPrefer hν.1 hμ.1]
  exact mkt.toMarket.sellerChosen_iff_buyerChosen
    mkt.substitutable_toMarket mkt.consistent_toMarket
    ((mkt.isStableMatching_iff_stable_graphOf ν).mp hν)
    ((mkt.isStableMatching_iff_stable_graphOf μ).mp hμ)

/-- The man-optimal contracts outcome, transported to a classical matching. -/
noncomputable def manOptimalMatching : M ≃. W :=
  mkt.matchingOfStable
    (mkt.toMarket.stable_sellerOptimal
      mkt.substitutable_toMarket
      mkt.consistent_toMarket)

@[simp] theorem graphOf_manOptimalMatching :
    mkt.graphOf mkt.manOptimalMatching =
      mkt.toMarket.sellerOptimal mkt.substitutable_toMarket :=
  mkt.graphOf_matchingOfStable
    (mkt.toMarket.stable_sellerOptimal
      mkt.substitutable_toMarket
      mkt.consistent_toMarket)

theorem stable_manOptimalMatching :
    mkt.IsStableMatching mkt.manOptimalMatching :=
  mkt.stable_matchingOfStable
    (mkt.toMarket.stable_sellerOptimal
      mkt.substitutable_toMarket
      mkt.consistent_toMarket)

theorem le_manOptimalMatching
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (ν m) (mkt.manOptimalMatching m) := by
  have hchosen :
      mkt.toMarket.SellerChosen
        (mkt.graphOf mkt.manOptimalMatching)
        (mkt.graphOf ν) := by
    rw [mkt.graphOf_manOptimalMatching]
    exact mkt.toMarket.sellerChosen_sellerOptimal
      mkt.substitutable_toMarket
      mkt.consistent_toMarket
      ((mkt.isStableMatching_iff_stable_graphOf ν).mp hν)
  exact mkt.leM_of_sellerChosen_graphOf
    mkt.stable_manOptimalMatching.1 hν.1 hchosen m

/-- Classical man-optimality. -/
theorem exists_manOptimal_stableMatching :
    ∃ μ : M ≃. W, mkt.IsStableMatching μ ∧
      ∀ ν : M ≃. W, mkt.IsStableMatching ν →
        ∀ m, mkt.leM m (ν m) (μ m) :=
  ⟨mkt.manOptimalMatching,
    mkt.stable_manOptimalMatching,
    fun _ hν m => mkt.le_manOptimalMatching hν m⟩

/-! ### Symmetric extrema and their intrinsic characterizations -/

/-- The woman-optimal contracts outcome, transported to a classical matching. -/
noncomputable def womanOptimalMatching : M ≃. W :=
  mkt.matchingOfStable
    (mkt.toMarket.stable_buyerOptimal
      mkt.substitutable_toMarket mkt.consistent_toMarket)

@[simp] theorem graphOf_womanOptimalMatching :
    mkt.graphOf mkt.womanOptimalMatching =
      mkt.toMarket.buyerOptimal mkt.substitutable_toMarket :=
  mkt.graphOf_matchingOfStable _

theorem stable_womanOptimalMatching :
    mkt.IsStableMatching mkt.womanOptimalMatching :=
  mkt.stable_matchingOfStable _

theorem le_womanOptimalMatching
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (ν.symm w) (mkt.womanOptimalMatching.symm w) := by
  have hchosen :
      mkt.toMarket.BuyerChosen
        (mkt.graphOf mkt.womanOptimalMatching) (mkt.graphOf ν) := by
    rw [mkt.graphOf_womanOptimalMatching]
    exact mkt.toMarket.buyerChosen_buyerOptimal
      mkt.substitutable_toMarket mkt.consistent_toMarket
      ((mkt.isStableMatching_iff_stable_graphOf ν).mp hν)
  exact mkt.leW_of_buyerChosen_graphOf
    mkt.stable_womanOptimalMatching.1 hν.1 hchosen w

/-- The woman-optimal matching is man-pessimal; this also records the
pointwise interpretation of generalized seller-pessimality. -/
theorem womanOptimalMatching_le
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (mkt.womanOptimalMatching m) (ν m) := by
  have hchosen :
      mkt.toMarket.SellerChosen
        (mkt.graphOf ν) (mkt.graphOf mkt.womanOptimalMatching) := by
    rw [mkt.graphOf_womanOptimalMatching]
    exact mkt.toMarket.sellerChosen_buyerOptimal
      mkt.substitutable_toMarket mkt.consistent_toMarket
      ((mkt.isStableMatching_iff_stable_graphOf ν).mp hν)
  exact mkt.leM_of_sellerChosen_graphOf
    hν.1 mkt.stable_womanOptimalMatching.1 hchosen m

/-- The man-optimal matching is woman-pessimal. -/
theorem manOptimalMatching_le
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (mkt.manOptimalMatching.symm w) (ν.symm w) := by
  have hchosen :
      mkt.toMarket.BuyerChosen
        (mkt.graphOf ν) (mkt.graphOf mkt.manOptimalMatching) := by
    rw [mkt.graphOf_manOptimalMatching]
    exact mkt.toMarket.buyerChosen_sellerOptimal
      mkt.substitutable_toMarket mkt.consistent_toMarket
      ((mkt.isStableMatching_iff_stable_graphOf ν).mp hν)
  exact mkt.leW_of_buyerChosen_graphOf
    hν.1 mkt.stable_manOptimalMatching.1 hchosen w

theorem isManOptimal_manOptimalMatching : mkt.IsManOptimal mkt.manOptimalMatching :=
  ⟨mkt.stable_manOptimalMatching, fun _ hν => mkt.le_manOptimalMatching hν⟩

theorem isWomanOptimal_womanOptimalMatching :
    mkt.IsWomanOptimal mkt.womanOptimalMatching :=
  ⟨mkt.stable_womanOptimalMatching, fun _ hν => mkt.le_womanOptimalMatching hν⟩

theorem isManPessimal_womanOptimalMatching :
    mkt.IsManPessimal mkt.womanOptimalMatching :=
  ⟨mkt.stable_womanOptimalMatching, fun _ hν => mkt.womanOptimalMatching_le hν⟩

theorem isWomanPessimal_manOptimalMatching :
    mkt.IsWomanPessimal mkt.manOptimalMatching :=
  ⟨mkt.stable_manOptimalMatching, fun _ hν => mkt.manOptimalMatching_le hν⟩

theorem exists_womanOptimal_stableMatching :
    ∃ μ : M ≃. W, mkt.IsStableMatching μ ∧
      ∀ ν : M ≃. W, mkt.IsStableMatching ν →
        ∀ w, mkt.leW w (ν.symm w) (μ.symm w) :=
  ⟨mkt.womanOptimalMatching, mkt.isWomanOptimal_womanOptimalMatching⟩

theorem exists_manPessimal_stableMatching :
    ∃ μ : M ≃. W, mkt.IsManPessimal μ :=
  ⟨mkt.womanOptimalMatching, mkt.isManPessimal_womanOptimalMatching⟩

theorem exists_womanPessimal_stableMatching :
    ∃ μ : M ≃. W, mkt.IsWomanPessimal μ :=
  ⟨mkt.manOptimalMatching, mkt.isWomanPessimal_manOptimalMatching⟩

/-- The unique stable matching worst for every man. This definition uses
its own preference specification, independently of `womanOptimalMatching`;
their equality is proved below by uniqueness. -/
noncomputable def manPessimalMatching : M ≃. W :=
  Classical.choose mkt.exists_manPessimal_stableMatching

/-- The unique stable matching worst for every woman. -/
noncomputable def womanPessimalMatching : M ≃. W :=
  Classical.choose mkt.exists_womanPessimal_stableMatching

theorem isManPessimal_manPessimalMatching :
    mkt.IsManPessimal mkt.manPessimalMatching :=
  Classical.choose_spec mkt.exists_manPessimal_stableMatching

theorem isWomanPessimal_womanPessimalMatching :
    mkt.IsWomanPessimal mkt.womanPessimalMatching :=
  Classical.choose_spec mkt.exists_womanPessimal_stableMatching

theorem stable_manPessimalMatching : mkt.IsStableMatching mkt.manPessimalMatching :=
  mkt.isManPessimal_manPessimalMatching.1

theorem stable_womanPessimalMatching : mkt.IsStableMatching mkt.womanPessimalMatching :=
  mkt.isWomanPessimal_womanPessimalMatching.1

theorem manPessimalMatching_le {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (mkt.manPessimalMatching m) (ν m) :=
  mkt.isManPessimal_manPessimalMatching.2 ν hν m

theorem womanPessimalMatching_le {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (mkt.womanPessimalMatching.symm w) (ν.symm w) :=
  mkt.isWomanPessimal_womanPessimalMatching.2 ν hν w

/-- Woman-optimality and man-pessimality select the same stable matching. -/
theorem womanOptimalMatching_eq_manPessimalMatching :
    mkt.womanOptimalMatching = mkt.manPessimalMatching :=
  IsManPessimal.unique mkt mkt.isManPessimal_womanOptimalMatching
    mkt.isManPessimal_manPessimalMatching

/-- Man-optimality and woman-pessimality select the same stable matching. -/
theorem manOptimalMatching_eq_womanPessimalMatching :
    mkt.manOptimalMatching = mkt.womanPessimalMatching :=
  IsWomanPessimal.unique mkt mkt.isWomanPessimal_manOptimalMatching
    mkt.isWomanPessimal_womanPessimalMatching

theorem le_manPessimalMatching {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (ν.symm w) (mkt.manPessimalMatching.symm w) := by
  rw [← mkt.womanOptimalMatching_eq_manPessimalMatching]
  exact mkt.le_womanOptimalMatching hν w

theorem le_womanPessimalMatching {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (ν m) (mkt.womanPessimalMatching m) := by
  rw [← mkt.manOptimalMatching_eq_womanPessimalMatching]
  exact mkt.le_manOptimalMatching hν m

theorem isManOptimal_iff_eq_manOptimalMatching (μ : M ≃. W) :
    mkt.IsManOptimal μ ↔ μ = mkt.manOptimalMatching := by
  constructor
  · exact fun h => IsManOptimal.unique mkt h mkt.isManOptimal_manOptimalMatching
  · rintro rfl
    exact mkt.isManOptimal_manOptimalMatching

theorem isWomanOptimal_iff_eq_womanOptimalMatching (μ : M ≃. W) :
    mkt.IsWomanOptimal μ ↔ μ = mkt.womanOptimalMatching := by
  constructor
  · exact fun h => IsWomanOptimal.unique mkt h mkt.isWomanOptimal_womanOptimalMatching
  · rintro rfl
    exact mkt.isWomanOptimal_womanOptimalMatching

theorem isManPessimal_iff_eq_manPessimalMatching (μ : M ≃. W) :
    mkt.IsManPessimal μ ↔ μ = mkt.manPessimalMatching := by
  constructor
  · exact fun h => IsManPessimal.unique mkt h mkt.isManPessimal_manPessimalMatching
  · rintro rfl
    exact mkt.isManPessimal_manPessimalMatching

theorem isWomanPessimal_iff_eq_womanPessimalMatching (μ : M ≃. W) :
    mkt.IsWomanPessimal μ ↔ μ = mkt.womanPessimalMatching := by
  constructor
  · exact fun h => IsWomanPessimal.unique mkt h mkt.isWomanPessimal_womanPessimalMatching
  · rintro rfl
    exact mkt.isWomanPessimal_womanPessimalMatching

/-- Swapping the two sides exchanges the optimal matchings. -/
@[simp] theorem manOptimalMatching_symm :
    mkt.symm.manOptimalMatching = mkt.womanOptimalMatching.symm := by
  apply IsManOptimal.unique mkt.symm mkt.symm.isManOptimal_manOptimalMatching
  refine ⟨(mkt.isStableMatching_symm _).mpr mkt.stable_womanOptimalMatching, ?_⟩
  intro ν hν w
  have hν' : mkt.IsStableMatching ν.symm := by
    simpa using (mkt.isStableMatching_symm ν.symm).mp hν
  simpa using mkt.le_womanOptimalMatching hν' w

@[simp] theorem womanOptimalMatching_symm :
    mkt.symm.womanOptimalMatching = mkt.manOptimalMatching.symm := by
  apply IsWomanOptimal.unique mkt.symm mkt.symm.isWomanOptimal_womanOptimalMatching
  refine ⟨(mkt.isStableMatching_symm _).mpr mkt.stable_manOptimalMatching, ?_⟩
  intro ν hν m
  have hν' : mkt.IsStableMatching ν.symm := by
    simpa using (mkt.isStableMatching_symm ν.symm).mp hν
  simpa using mkt.le_manOptimalMatching hν' m

@[simp] theorem manPessimalMatching_symm :
    mkt.symm.manPessimalMatching = mkt.womanPessimalMatching.symm := by
  rw [← mkt.symm.womanOptimalMatching_eq_manPessimalMatching,
    mkt.womanOptimalMatching_symm,
    mkt.manOptimalMatching_eq_womanPessimalMatching]

@[simp] theorem womanPessimalMatching_symm :
    mkt.symm.womanPessimalMatching = mkt.manPessimalMatching.symm := by
  rw [← mkt.symm.manOptimalMatching_eq_womanPessimalMatching,
    mkt.manOptimalMatching_symm,
    mkt.womanOptimalMatching_eq_manPessimalMatching]

/-! ## Deferred acceptance

The following semantic state sequence iterates the generalized contracts
operator from its top state:

* all man–woman contracts are initially available to men;
* no contracts are initially available to women.

The terminal matching is the matching carried by the greatest fixed point.
-/

set_option linter.unusedVariables false in
/-- Initial state of man-proposing deferred acceptance.

The market parameter is intentionally explicit even though the state itself
does not depend on preferences. This preserves the downstream API
`mkt.manProposingInitialState`. -/
abbrev manProposingInitialState (mkt : MarriageMarket M W) :
    Set (M × W) × (Set (M × W))ᵒᵈ :=
  (Set.univ, toDual (∅ : Set (M × W)))

/-- The state after `n` iterations of the generalized man-proposing operator. -/
noncomputable def deferredAcceptanceState (n : ℕ) :
    Set (M × W) × (Set (M × W))ᵒᵈ :=
  mkt.toMarket.daFun^[n] mkt.manProposingInitialState

/-- The outcome carried by the state after `n` rounds. -/
noncomputable def deferredAcceptanceOutcome (n : ℕ) : Set (M × W) :=
  mkt.toMarket.outcomeOf (mkt.deferredAcceptanceState n)

/-- The generalized DA endpoint. The classical proposal algorithm and its
agreement theorem are provided in `Classical.DeferredAcceptance`. -/
noncomputable def deferredAcceptance : M ≃. W :=
  mkt.manOptimalMatching

theorem deferredAcceptance_eq_manOptimalMatching :
    mkt.deferredAcceptance = mkt.manOptimalMatching :=
  rfl

theorem stable_deferredAcceptance :
    mkt.IsStableMatching mkt.deferredAcceptance :=
  mkt.stable_manOptimalMatching

theorem deferredAcceptance_manOptimal
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (ν m) (mkt.deferredAcceptance m) :=
  mkt.le_manOptimalMatching hν m

/-- The generalized deferred-acceptance state iteration terminates at the
state carrying the man-optimal outcome. -/
theorem exists_deferredAcceptanceState_eq_terminal :
    ∃ n,
      mkt.deferredAcceptanceState n =
        (mkt.toMarket.sellerOptimalOutcome
          mkt.substitutable_toMarket).state := by
  simpa [deferredAcceptanceState, manProposingInitialState] using
    mkt.toMarket.exists_iterate_daFun_top_eq_state
      mkt.substitutable_toMarket

/-- Outcome-level termination of deferred acceptance. -/
theorem exists_deferredAcceptanceOutcome_eq_graph :
    ∃ n,
      mkt.deferredAcceptanceOutcome n =
        mkt.graphOf mkt.deferredAcceptance := by
  obtain ⟨n, hn⟩ :=
    mkt.toMarket.exists_iterate_outcomeOf_eq_sellerOptimal
      mkt.substitutable_toMarket
  refine ⟨n, ?_⟩
  simpa [deferredAcceptanceOutcome, deferredAcceptanceState,
    manProposingInitialState, deferredAcceptance,
    graphOf_manOptimalMatching] using hn

/-- Deferred acceptance computes a stable matching. -/
theorem exists_deferredAcceptanceOutcome_stable :
    ∃ n,
      mkt.deferredAcceptanceOutcome n =
          mkt.graphOf mkt.deferredAcceptance ∧
        mkt.toMarket.Stable (mkt.deferredAcceptanceOutcome n) := by
  obtain ⟨n, hn⟩ := mkt.exists_deferredAcceptanceOutcome_eq_graph
  refine ⟨n, hn, ?_⟩
  rw [hn]
  exact (mkt.isStableMatching_iff_stable_graphOf
    mkt.deferredAcceptance).mp mkt.stable_deferredAcceptance

/-! ### The symmetric generalized iteration

These are set-valued iterates of the contracts operator, with an
existential convergence theorem. The classical proposal implementation is
provided separately in `Classical.DeferredAcceptance`.
-/

set_option linter.unusedVariables false in
/-- Initial state of woman-proposing generalized deferred acceptance. -/
abbrev womanProposingInitialState (mkt : MarriageMarket M W) :
    Set (M × W) × (Set (M × W))ᵒᵈ :=
  (∅, toDual (Set.univ : Set (M × W)))

/-- The `n`th generalized DA state starting from the buyer-proposing end. -/
noncomputable def womanProposingDeferredAcceptanceState (n : ℕ) :
    Set (M × W) × (Set (M × W))ᵒᵈ :=
  mkt.toMarket.daFun^[n] mkt.womanProposingInitialState

/-- The contracts carried by the `n`th woman-proposing generalized state. -/
noncomputable def womanProposingDeferredAcceptanceOutcome (n : ℕ) : Set (M × W) :=
  mkt.toMarket.outcomeOf (mkt.womanProposingDeferredAcceptanceState n)

/-- The woman-proposing generalized DA endpoint, parallel to
`deferredAcceptance`. This is the endpoint specification; the classical
proposal algorithm is provided in `Classical.DeferredAcceptance`. -/
noncomputable def womanProposingDeferredAcceptance : M ≃. W :=
  mkt.womanOptimalMatching

theorem womanProposingDeferredAcceptance_eq_womanOptimalMatching :
    mkt.womanProposingDeferredAcceptance = mkt.womanOptimalMatching := rfl

theorem stable_womanProposingDeferredAcceptance :
    mkt.IsStableMatching mkt.womanProposingDeferredAcceptance :=
  mkt.stable_womanOptimalMatching

theorem womanProposingDeferredAcceptance_womanOptimal
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (ν.symm w) (mkt.womanProposingDeferredAcceptance.symm w) :=
  mkt.le_womanOptimalMatching hν w

theorem womanProposingDeferredAcceptance_manPessimal
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (mkt.womanProposingDeferredAcceptance m) (ν m) :=
  mkt.womanOptimalMatching_le hν m

theorem exists_womanProposingDeferredAcceptanceState_eq_terminal :
    ∃ n, mkt.womanProposingDeferredAcceptanceState n =
      (mkt.toMarket.buyerOptimalOutcome mkt.substitutable_toMarket).state := by
  simpa [womanProposingDeferredAcceptanceState, womanProposingInitialState] using
    mkt.toMarket.exists_iterate_daFun_bot_eq_state mkt.substitutable_toMarket

theorem exists_womanProposingDeferredAcceptanceOutcome_eq_graph :
    ∃ n, mkt.womanProposingDeferredAcceptanceOutcome n =
      mkt.graphOf mkt.womanOptimalMatching := by
  obtain ⟨n, hn⟩ := mkt.toMarket.exists_iterate_outcomeOf_eq_buyerOptimal
    mkt.substitutable_toMarket
  refine ⟨n, ?_⟩
  simpa [womanProposingDeferredAcceptanceOutcome, womanProposingDeferredAcceptanceState,
    womanProposingInitialState, graphOf_womanOptimalMatching] using hn

/-- Finite convergence, with both sides' extremal interpretations. -/
theorem exists_womanProposingDeferredAcceptanceOutcome_stable :
    ∃ n, mkt.womanProposingDeferredAcceptanceOutcome n =
          mkt.graphOf mkt.womanOptimalMatching ∧
      mkt.toMarket.Stable (mkt.womanProposingDeferredAcceptanceOutcome n) ∧
      mkt.IsWomanOptimal mkt.womanOptimalMatching ∧
      mkt.IsManPessimal mkt.womanOptimalMatching := by
  obtain ⟨n, hn⟩ := mkt.exists_womanProposingDeferredAcceptanceOutcome_eq_graph
  refine ⟨n, hn, ?_, mkt.isWomanOptimal_womanOptimalMatching,
    mkt.isManPessimal_womanOptimalMatching⟩
  rw [hn]
  exact (mkt.isStableMatching_iff_stable_graphOf _).mp mkt.stable_womanOptimalMatching

/-! ## Lone wolf -/

theorem sellerSide_graphOf_eq_empty {μ : M ≃. W} {m : M}
    (hμ : μ m = none) :
    mkt.toMarket.sellerSide m (mkt.graphOf μ) = ∅ := by
  ext p
  rcases p with ⟨m', w⟩
  simp only [Market.mem_sellerSide, mem_graphOf, toMarket_seller,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro hp rfl
  rw [hμ] at hp
  contradiction

theorem sellerSide_graphOf_eq_singleton {μ : M ≃. W}
    {m : M} {w : W} (hμ : μ m = some w) :
    mkt.toMarket.sellerSide m (mkt.graphOf μ) = {(m, w)} := by
  ext p
  rcases p with ⟨m', w'⟩
  constructor
  · rintro ⟨hp, hm'⟩
    obtain rfl : m = m' := hm'.symm
    have hpEq : μ m = some w' := mkt.mem_graphOf.mp hp
    have hww' : w = w' := Option.some.inj (hμ.symm.trans hpEq)
    subst hww'
    rfl
  · intro hp
    have hp' : (m', w') = (m, w) := hp
    rw [Prod.mk.injEq] at hp'
    obtain ⟨rfl, rfl⟩ := hp'
    exact ⟨mkt.mem_graphOf.mpr hμ, rfl⟩

theorem ncard_sellerSide_graphOf_eq_zero_iff
    (μ : M ≃. W) (m : M) :
    (mkt.toMarket.sellerSide m (mkt.graphOf μ)).ncard = 0 ↔
      μ m = none := by
  cases hμ : μ m with
  | none =>
      rw [mkt.sellerSide_graphOf_eq_empty hμ]
      simp
  | some w =>
      rw [mkt.sellerSide_graphOf_eq_singleton hμ]
      simp

theorem buyerSide_graphOf_eq_empty {μ : M ≃. W} {w : W}
    (hμ : μ.symm w = none) :
    mkt.toMarket.buyerSide w (mkt.graphOf μ) = ∅ := by
  ext p
  rcases p with ⟨m, w'⟩
  constructor
  · rintro ⟨hp, hw'⟩
    obtain rfl : w = w' := hw'.symm
    have hm : μ.symm w = some m := mkt.mem_graphOf_symm.mp hp
    rw [hμ] at hm
    cases hm
  · intro hp
    exact hp.elim

theorem buyerSide_graphOf_eq_singleton {μ : M ≃. W}
    {m : M} {w : W} (hμ : μ.symm w = some m) :
    mkt.toMarket.buyerSide w (mkt.graphOf μ) = {(m, w)} := by
  ext p
  rcases p with ⟨m', w'⟩
  constructor
  · rintro ⟨hp, hw'⟩
    obtain rfl : w = w' := hw'.symm
    have hpEq : μ.symm w = some m' := mkt.mem_graphOf_symm.mp hp
    have hmm' : m = m' := Option.some.inj (hμ.symm.trans hpEq)
    subst hmm'
    rfl
  · intro hp
    have hp' : (m', w') = (m, w) := hp
    rw [Prod.mk.injEq] at hp'
    obtain ⟨rfl, rfl⟩ := hp'
    exact ⟨mkt.mem_graphOf_symm.mpr hμ, rfl⟩

theorem ncard_buyerSide_graphOf_eq_zero_iff (μ : M ≃. W) (w : W) :
    (mkt.toMarket.buyerSide w (mkt.graphOf μ)).ncard = 0 ↔
      μ.symm w = none := by
  cases hμ : μ.symm w with
  | none =>
      rw [mkt.buyerSide_graphOf_eq_empty hμ]
      simp
  | some m =>
      rw [mkt.buyerSide_graphOf_eq_singleton hμ]
      simp

/-- Lone wolf: a man is matched in one stable matching iff he is matched in
every stable matching. -/
theorem isSome_iff_of_stable {μ ν : M ≃. W}
    (hμ : mkt.IsStableMatching μ)
    (hν : mkt.IsStableMatching ν) (m : M) :
    (μ m).isSome ↔ (ν m).isSome := by
  have hstableμ :
      mkt.toMarket.Stable (mkt.graphOf μ) :=
    (mkt.isStableMatching_iff_stable_graphOf μ).mp hμ
  have hstableν :
      mkt.toMarket.Stable (mkt.graphOf ν) :=
    (mkt.isStableMatching_iff_stable_graphOf ν).mp hν
  have hcard :=
    mkt.toMarket.ncard_sellerSide_eq_of_stable
      mkt.substitutable_toMarket
      mkt.consistent_toMarket
      mkt.sizeMonotone_toMarket
      hstableμ hstableν m
  constructor
  · intro hsome
    cases hνm : ν m with
    | some w =>
        simp
    | none =>
        have hzeroν :
            (mkt.toMarket.sellerSide m (mkt.graphOf ν)).ncard = 0 :=
          (mkt.ncard_sellerSide_graphOf_eq_zero_iff ν m).2 hνm
        have hzeroμ :
            (mkt.toMarket.sellerSide m (mkt.graphOf μ)).ncard = 0 := by
          rw [hcard, hzeroν]
        have hnoneμ :
            μ m = none :=
          (mkt.ncard_sellerSide_graphOf_eq_zero_iff μ m).1 hzeroμ
        simp [hnoneμ] at hsome
  · intro hsome
    cases hμm : μ m with
    | some w =>
        simp
    | none =>
        have hzeroμ :
            (mkt.toMarket.sellerSide m (mkt.graphOf μ)).ncard = 0 :=
          (mkt.ncard_sellerSide_graphOf_eq_zero_iff μ m).2 hμm
        have hzeroν :
            (mkt.toMarket.sellerSide m (mkt.graphOf ν)).ncard = 0 := by
          rw [← hcard, hzeroμ]
        have hnoneν :
            ν m = none :=
          (mkt.ncard_sellerSide_graphOf_eq_zero_iff ν m).1 hzeroν
        simp [hnoneν] at hsome

/-- Lone wolf for women, obtained from the same theorem after side exchange. -/
theorem isSome_symm_iff_of_stable {μ ν : M ≃. W}
    (hμ : mkt.IsStableMatching μ) (hν : mkt.IsStableMatching ν) (w : W) :
    (μ.symm w).isSome ↔ (ν.symm w).isSome :=
  mkt.symm.isSome_iff_of_stable (μ := μ.symm) (ν := ν.symm)
    ((mkt.isStableMatching_symm μ).mpr hμ)
    ((mkt.isStableMatching_symm ν).mpr hν) w

end InducedChoice

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
  unfold IsBlockingPair BlocksM BlocksW
  unfold leM leW ltM ltW
  infer_instance

end Decide

end MarriageMarket
