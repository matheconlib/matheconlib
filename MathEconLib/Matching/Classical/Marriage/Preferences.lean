/-
Copyright (c) 2026 Scott Duke Kominers, Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers, Bo Cowgill
-/
module

public import MathEconLib.Choice.Induced
public import Mathlib.Data.Finset.Max
public import MathEconLib.Matching.PartnerComparisons

/-!
# Marriage preferences and their induced choice functions

Each agent has a linear order over possible partners and the outside option
`none`. Larger options are preferred; `none` need not be least preferred.
The preference relations and acceptability conditions are defined first, then
choice on partner pairs is obtained by mapping the general optional-partner
choice function along the corresponding partner embedding.

Unit demand, substitutability, and the law of aggregate demand on finite menus
hold without population finiteness. IRC is proved for finite partner types. On an infinite
menu without a greatest acceptable option, the generic choice is empty, so no
global IRC claim is made on arbitrary partner types. Finite menu maxima give
the realization used by the proposal algorithms.

This module does not depend on the matching-with-contracts model. The
embedding into that model is in `Marriage.ToContracts`.
-/

@[expose] public section

namespace MathEconLib.Matching

open MathEconLib.Choice
open Function OrderDual

universe u v

variable {M : Type u} {W : Type v}

/-- A classical marriage market. Each agent has a linear order over possible
partners together with the outside option `none`; larger options are preferred. -/
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

/-- View classical strict preferences through the shared partner-comparison interface. -/
def toPartnerComparisons : PartnerComparisons M W := ⟨mkt.ltM, mkt.ltW⟩

@[simp] theorem toPartnerComparisons_symm :
    mkt.symm.toPartnerComparisons = mkt.toPartnerComparisons.symm := rfl

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

/-! ## Structural choice on arbitrary partner types -/

/-- Embed a possible partner into man `m`'s contracts. -/
def partnerEmbeddingM (m : M) : W ↪ M × W where
  toFun := fun w => (m, w)
  inj' := fun _ _ h => congrArg Prod.snd h

/-- Embed a possible partner into woman `w`'s contracts. -/
def partnerEmbeddingW (w : W) : M ↪ M × W where
  toFun := fun m => (m, w)
  inj' := fun _ _ h => congrArg Prod.fst h

/-- Optional-partner choice mapped to man `m`'s contracts. -/
def inducedChoiceM (m : M) : ChoiceFunction (M × W) :=
  (ChoiceFunction.ofOptionLinearOrder (mkt.prefM m)).map (partnerEmbeddingM m)

/-- Optional-partner choice mapped to woman `w`'s contracts. -/
def inducedChoiceW (w : W) : ChoiceFunction (M × W) :=
  (ChoiceFunction.ofOptionLinearOrder (mkt.prefW w)).map (partnerEmbeddingW w)

theorem inducedChoiceM_eq_map_ofOptionLinearOrder (m : M) :
    mkt.inducedChoiceM m =
      (ChoiceFunction.ofOptionLinearOrder (mkt.prefM m)).map (partnerEmbeddingM m) := rfl

theorem inducedChoiceW_eq_map_ofOptionLinearOrder (w : W) :
    mkt.inducedChoiceW w =
      (ChoiceFunction.ofOptionLinearOrder (mkt.prefW w)).map (partnerEmbeddingW w) := rfl

/-- Chosen contracts belong to the man making the choice. -/
theorem fst_eq_of_mem_inducedChoiceM {m : M} {p : M × W} {Y : Set (M × W)}
    (hp : p ∈ mkt.inducedChoiceM m Y) : p.1 = m := by
  obtain ⟨w, _, h⟩ := hp
  exact (congrArg Prod.fst h).symm

/-- Chosen contracts belong to the woman making the choice. -/
theorem snd_eq_of_mem_inducedChoiceW {w : W} {p : M × W} {Y : Set (M × W)}
    (hp : p ∈ mkt.inducedChoiceW w Y) : p.2 = w := by
  obtain ⟨m, _, h⟩ := hp
  exact (congrArg Prod.snd h).symm

/-- The order-theoretic choice specification needs no finite enumeration. -/
theorem mem_inducedChoiceM_iff {m : M} {w : W} {Y : Set (M × W)} :
    (m, w) ∈ mkt.inducedChoiceM m Y ↔
      (m, w) ∈ Y ∧ mkt.leM m none (some w) ∧
        ∀ w', (m, w') ∈ Y → mkt.leM m (some w') (some w) :=
  (ChoiceFunction.mem_map _ (partnerEmbeddingM m) (x := w) (Y := Y)).trans
    (ChoiceFunction.mem_ofOptionLinearOrder _)

/-- The symmetric order-theoretic choice specification. -/
theorem mem_inducedChoiceW_iff {m : M} {w : W} {Y : Set (M × W)} :
    (m, w) ∈ mkt.inducedChoiceW w Y ↔
      (m, w) ∈ Y ∧ mkt.leW w none (some m) ∧
        ∀ m', (m', w) ∈ Y → mkt.leW w (some m') (some m) :=
  (ChoiceFunction.mem_map _ (partnerEmbeddingW w) (x := m) (Y := Y)).trans
    (ChoiceFunction.mem_ofOptionLinearOrder _)

theorem unitDemand_inducedChoiceM (m : M) :
    (mkt.inducedChoiceM m).UnitDemand :=
  (ChoiceFunction.unitDemand_ofOptionLinearOrder _).map _

theorem unitDemand_inducedChoiceW (w : W) :
    (mkt.inducedChoiceW w).UnitDemand :=
  (ChoiceFunction.unitDemand_ofOptionLinearOrder _).map _

theorem substitutable_inducedChoiceM (m : M) :
    (mkt.inducedChoiceM m).Substitutable :=
  (ChoiceFunction.substitutable_ofOptionLinearOrder _).map _

theorem substitutable_inducedChoiceW (w : W) :
    (mkt.inducedChoiceW w).Substitutable :=
  (ChoiceFunction.substitutable_ofOptionLinearOrder _).map _

theorem sizeMonotone_inducedChoiceM (m : M) :
    (mkt.inducedChoiceM m).SizeMonotone :=
  (ChoiceFunction.sizeMonotone_ofOptionLinearOrder _).map _

theorem sizeMonotone_inducedChoiceW (w : W) :
    (mkt.inducedChoiceW w).SizeMonotone :=
  (ChoiceFunction.sizeMonotone_ofOptionLinearOrder _).map _

theorem consistent_inducedChoiceM [Finite W] (m : M) :
    (mkt.inducedChoiceM m).Consistent :=
  (ChoiceFunction.consistent_ofOptionLinearOrder _).map _

theorem consistent_inducedChoiceW [Finite M] (w : W) :
    (mkt.inducedChoiceW w).Consistent :=
  (ChoiceFunction.consistent_ofOptionLinearOrder _).map _

/-! ## Finite maximum realization

The internal menu consists of `none` together with the available partners.
These finite maxima support the proposal algorithms; they do not enter the
structural definition of choice. -/

section InducedChoice

variable [Fintype M] [Fintype W]

set_option linter.unusedVariables false in
/-- The shared option menu for the partners available to man `m`. -/
noncomputable def menuM
    (mkt : MarriageMarket M W) (m : M) (Y : Set (M × W)) :
    Finset (Option W) := by
  classical
  exact ChoiceFunction.optionMenu (Finset.univ.filter fun w => (m, w) ∈ Y)

set_option linter.unusedVariables false in
/-- The shared option menu for the partners available to woman `w`. -/
noncomputable def menuW
    (mkt : MarriageMarket M W) (w : W) (Y : Set (M × W)) :
    Finset (Option M) := by
  classical
  exact ChoiceFunction.optionMenu (Finset.univ.filter fun m => (m, w) ∈ Y)

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
  apply ChoiceFunction.optionMenu_mono
  intro w hw
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    hYZ (Finset.mem_filter.mp hw).2

omit [Fintype W] in
theorem menuW_mono {w : W} {Y Z : Set (M × W)}
    (hYZ : Y ⊆ Z) :
    mkt.menuW w Y ⊆ mkt.menuW w Z := by
  classical
  apply ChoiceFunction.optionMenu_mono
  intro m hm
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    hYZ (Finset.mem_filter.mp hm).2

/-- Man `m`'s best option from `Y`, including remaining single. -/
noncomputable def bestM (m : M) (Y : Set (M × W)) : Option W := by
  classical
  exact ChoiceFunction.bestOption (mkt.prefM m)
    (Finset.univ.filter fun w => (m, w) ∈ Y)

/-- Woman `w`'s best option from `Y`, including remaining single. -/
noncomputable def bestW (w : W) (Y : Set (M × W)) : Option M := by
  classical
  exact ChoiceFunction.bestOption (mkt.prefW w)
    (Finset.univ.filter fun m => (m, w) ∈ Y)

omit [Fintype M] in
theorem bestM_mem_menuM (m : M) (Y : Set (M × W)) :
    mkt.bestM m Y ∈ mkt.menuM m Y := by
  classical
  exact ChoiceFunction.bestOption_mem _ _

omit [Fintype W] in
theorem bestW_mem_menuW (w : W) (Y : Set (M × W)) :
    mkt.bestW w Y ∈ mkt.menuW w Y := by
  classical
  exact ChoiceFunction.bestOption_mem _ _

omit [Fintype M] in
theorem none_le_bestM (m : M) (Y : Set (M × W)) :
    mkt.leM m none (mkt.bestM m Y) := by
  classical
  exact ChoiceFunction.le_bestOption _ _ (ChoiceFunction.none_mem_optionMenu _)

omit [Fintype W] in
theorem none_le_bestW (w : W) (Y : Set (M × W)) :
    mkt.leW w none (mkt.bestW w Y) := by
  classical
  exact ChoiceFunction.le_bestOption _ _ (ChoiceFunction.none_mem_optionMenu _)

omit [Fintype M] in
theorem le_bestM_of_mem {m : M} {Y : Set (M × W)} {o : Option W}
    (ho : o ∈ mkt.menuM m Y) :
    mkt.leM m o (mkt.bestM m Y) := by
  classical
  exact ChoiceFunction.le_bestOption _ _ ho

omit [Fintype W] in
theorem le_bestW_of_mem {w : W} {Y : Set (M × W)} {o : Option M}
    (ho : o ∈ mkt.menuW w Y) :
    mkt.leW w o (mkt.bestW w Y) := by
  classical
  exact ChoiceFunction.le_bestOption _ _ ho

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

omit [Fintype M] in
/-- The finite realization inherits the shared selector's specification. -/
theorem bestM_eq_some_iff {m : M} {w : W} {Y : Set (M × W)} :
    mkt.bestM m Y = some w ↔
      (m, w) ∈ Y ∧ mkt.leM m none (some w) ∧
        ∀ w', (m, w') ∈ Y → mkt.leM m (some w') (some w) := by
  classical
  simpa only [bestM, leM, Finset.mem_filter, Finset.mem_univ, true_and] using
    (ChoiceFunction.bestOption_eq_some_iff (mkt.prefM m)
      (Finset.univ.filter fun w => (m, w) ∈ Y) (x := w))

omit [Fintype W] in
/-- The symmetric finite maximum specification. -/
theorem bestW_eq_some_iff {m : M} {w : W} {Y : Set (M × W)} :
    mkt.bestW w Y = some m ↔
      (m, w) ∈ Y ∧ mkt.leW w none (some m) ∧
        ∀ m', (m', w) ∈ Y → mkt.leW w (some m') (some m) := by
  classical
  simpa only [bestW, leW, Finset.mem_filter, Finset.mem_univ, true_and] using
    (ChoiceFunction.bestOption_eq_some_iff (mkt.prefW w)
      (Finset.univ.filter fun m => (m, w) ∈ Y) (x := m))

omit [Fintype M] in
/-- The structural choice agrees with the finite maximum realization. -/
@[simp] theorem mem_inducedChoiceM {m : M} {p : M × W} {Y : Set (M × W)} :
    p ∈ mkt.inducedChoiceM m Y ↔
      p.1 = m ∧ some p.2 = mkt.bestM m Y := by
  rcases p with ⟨m', w⟩
  constructor
  · intro hp
    have hown := mkt.fst_eq_of_mem_inducedChoiceM hp
    dsimp at hown
    subst m'
    exact ⟨rfl, (mkt.bestM_eq_some_iff.mpr (mkt.mem_inducedChoiceM_iff.mp hp)).symm⟩
  · rintro ⟨hown, hbest⟩
    dsimp at hown hbest
    subst m'
    exact mkt.mem_inducedChoiceM_iff.mpr (mkt.bestM_eq_some_iff.mp hbest.symm)

omit [Fintype W] in
/-- The symmetric finite maximum realization. -/
@[simp] theorem mem_inducedChoiceW {w : W} {p : M × W} {Y : Set (M × W)} :
    p ∈ mkt.inducedChoiceW w Y ↔
      p.2 = w ∧ some p.1 = mkt.bestW w Y := by
  rcases p with ⟨m, w'⟩
  constructor
  · intro hp
    have hown := mkt.snd_eq_of_mem_inducedChoiceW hp
    dsimp at hown
    subst w'
    exact ⟨rfl, (mkt.bestW_eq_some_iff.mpr (mkt.mem_inducedChoiceW_iff.mp hp)).symm⟩
  · rintro ⟨hown, hbest⟩
    dsimp at hown hbest
    subst w'
    exact mkt.mem_inducedChoiceW_iff.mpr (mkt.bestW_eq_some_iff.mp hbest.symm)

omit [Fintype M] in
/-- Equality of the generic choice and its original finite maximum formula. -/
theorem inducedChoiceM_apply_eq (m : M) (Y : Set (M × W)) :
    mkt.inducedChoiceM m Y = {p | p.1 = m ∧ some p.2 = mkt.bestM m Y} := by
  ext p
  exact mkt.mem_inducedChoiceM

omit [Fintype W] in
/-- Equality of the generic choice and its symmetric finite maximum formula. -/
theorem inducedChoiceW_apply_eq (w : W) (Y : Set (M × W)) :
    mkt.inducedChoiceW w Y = {p | p.2 = w ∧ some p.1 = mkt.bestW w Y} := by
  ext p
  exact mkt.mem_inducedChoiceW

omit [Fintype M] in
theorem bestM_eq_of_choice_subset {m : M} {Y Z : Set (M × W)}
    (hchoice : mkt.inducedChoiceM m Y ⊆ Z) (hZY : Z ⊆ Y) :
    mkt.bestM m Z = mkt.bestM m Y := by
  classical
  let := mkt.prefM m
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
  let := mkt.prefW w
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

end InducedChoice

end MarriageMarket

end MathEconLib.Matching
