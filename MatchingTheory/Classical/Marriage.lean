/-
  Matching with contracts ~> classical model instance:
    the Gale–Shapley marriage model.
-/

import MatchingTheory.Contracts.FixedPoint

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

The generalized deferred-acceptance operator is inherited verbatim from
`Market.daFun`. Its iterates from `(univ, ∅)` reach the greatest fixed point,
whose outcome is transported back to the man-optimal classical matching.
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

/-! ## Classical matchings and stability -/

/-- Individual rationality: no agent is matched below the outside option. -/
def IndividuallyRational (μ : M ≃. W) : Prop :=
  (∀ m, mkt.leM m none (μ m)) ∧
    ∀ w, mkt.leW w none (μ.symm w)

/-- `(m,w)` blocks `μ` if both agents strictly prefer one another to their
current assignments. -/
def IsBlockingPair (μ : M ≃. W) (m : M) (w : W) : Prop :=
  mkt.ltM m (μ m) (some w) ∧
    mkt.ltW w (μ.symm w) (some m)

/-- Classical stability. -/
def IsStableMatching (μ : M ≃. W) : Prop :=
  mkt.IndividuallyRational μ ∧
    ∀ m w, ¬mkt.IsBlockingPair μ m w

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

/-! ## Individual rationality translation -/

theorem choiceM_graphOf_eq_side
    {μ : M ≃. W} (hIR : mkt.IndividuallyRational μ) (m : M) :
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
    · have h := hIR.1 m
      rwa [hμ] at h
    · intro w' hw'
      letI := mkt.prefM m
      have hww' : w' = w := mkt.graphOf_rightUnique μ hw' hpY
      exact le_of_eq (congrArg Option.some hww')

theorem choiceW_graphOf_eq_side
    {μ : M ≃. W} (hIR : mkt.IndividuallyRational μ) (w : W) :
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
    · have h := hIR.2 w
      rwa [hμ] at h
    · intro m' hm'
      letI := mkt.prefW w
      have hmm' : m' = m := mkt.graphOf_leftUnique μ hm' hpY
      exact le_of_eq (congrArg Option.some hmm')

theorem individuallyRational_graphOf
    {μ : M ≃. W} (hIR : mkt.IndividuallyRational μ) :
    mkt.toMarket.IndRational (mkt.graphOf μ) :=
  ⟨mkt.choiceW_graphOf_eq_side hIR,
    mkt.choiceM_graphOf_eq_side hIR⟩

theorem individuallyRational_of_graphOf
    {μ : M ≃. W}
    (hIR : mkt.toMarket.IndRational (mkt.graphOf μ)) :
    mkt.IndividuallyRational μ := by
  constructor
  · intro m
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

theorem mem_choiceM_insert_graphOf_iff
    {μ : M ≃. W} (hIR : mkt.IndividuallyRational μ)
    {m : M} {w : W} (hnew : μ m ≠ some w) :
    (m, w) ∈ mkt.toMarket.choiceS m
        (insert (m, w) (mkt.graphOf μ)) ↔
      mkt.ltM m (μ m) (some w) := by
  classical
  letI := mkt.prefM m
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
    · exact le_trans (hIR.1 m) (le_of_lt hlt)
    · intro w' hw'
      rcases Set.mem_insert_iff.mp hw' with hw' | hw'
      · exact le_of_eq (congrArg Option.some (congrArg Prod.snd hw'))
      · have hμ : μ m = some w' := mkt.mem_graphOf.mp hw'
        have h := le_of_lt hlt
        rw [hμ] at h
        exact h

theorem mem_choiceW_insert_graphOf_iff
    {μ : M ≃. W} (hIR : mkt.IndividuallyRational μ)
    {m : M} {w : W} (hnew : μ.symm w ≠ some m) :
    (m, w) ∈ mkt.toMarket.choiceB w
        (insert (m, w) (mkt.graphOf μ)) ↔
      mkt.ltW w (μ.symm w) (some m) := by
  classical
  letI := mkt.prefW w
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
    · exact le_trans (hIR.2 w) (le_of_lt hlt)
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
      (mkt.mem_choiceM_insert_graphOf_iff hIR hnewM).mp hm,
      (mkt.mem_choiceW_insert_graphOf_iff hIR hnewW).mp hw⟩
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
    · exact (mkt.mem_choiceW_insert_graphOf_iff hIR hnewW).mpr hw
    · exact (mkt.mem_choiceM_insert_graphOf_iff hIR hnewM).mpr hm

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
    exact hno m w
  · rintro ⟨hIRg, hno⟩
    have hIR : mkt.IndividuallyRational μ :=
      mkt.individuallyRational_of_graphOf hIRg
    refine ⟨hIR, ?_⟩
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
            have h := hν.1 m
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
          have h := hμ.1 m
          rw [hμm] at h
          exact h
      | some w' =>
          have hw'ν : (m, w') ∈ mkt.graphOf ν :=
            mkt.mem_graphOf.mpr hνm
          exact hmax w' (Or.inr hw'ν)

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

/-! ## Deferred acceptance

The classical state sequence is exactly the generalized contracts operator
started at its top state:

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

/-- The state after `n` rounds of man-proposing deferred acceptance. -/
noncomputable def deferredAcceptanceState (n : ℕ) :
    Set (M × W) × (Set (M × W))ᵒᵈ :=
  mkt.toMarket.daFun^[n] mkt.manProposingInitialState

/-- The outcome carried by the state after `n` rounds. -/
noncomputable def deferredAcceptanceOutcome (n : ℕ) : Set (M × W) :=
  mkt.toMarket.outcomeOf (mkt.deferredAcceptanceState n)

/-- The terminal Gale–Shapley matching. -/
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

end InducedChoice

/-! ## Decidability -/

section Decide

variable [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

instance : DecidablePred mkt.IsStableMatching := by
  intro μ
  unfold IsStableMatching IndividuallyRational IsBlockingPair
  unfold leM leW ltM ltW
  infer_instance

end Decide

end MarriageMarket
