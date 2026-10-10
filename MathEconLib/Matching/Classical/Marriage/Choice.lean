import MathEconLib.Matching.Classical.Marriage.Basic
import MathEconLib.Choice.Induced
import MathEconLib.Matching.Contracts.Basic
import Mathlib.Data.Finset.Max

/-!
# Optional-partner choice as a contracts instance

The contracts model is defined on arbitrary partner types by transporting
`ChoiceFunction.ofLinearOrder` along each agent's partner embedding. Unit demand,
substitutability, and finite-menu aggregate demand follow from the general choice
layer without population finiteness. IRC is proved for finite partner types.

Finite menu maxima provide the algorithm-facing realization, proved equal to
the structural choice; `none` is always available but need not be least preferred.
On an infinite menu without a greatest acceptable option, the generic choice is
empty, so no global IRC claim is made on arbitrary partner types.
-/

namespace MathEconLib.Matching

open MathEconLib.Choice

open Function OrderDual

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}
variable (mkt : MarriageMarket M W)

/-! ## Structural choice on arbitrary partner types -/

/-- Embed a possible partner into man `m`'s contracts. -/
def partnerEmbeddingM (m : M) : W ↪ M × W where
  toFun := fun w => (m, w)
  inj' := fun _ _ h => congrArg Prod.snd h

/-- Embed a possible partner into woman `w`'s contracts. -/
def partnerEmbeddingW (w : W) : M ↪ M × W where
  toFun := fun m => (m, w)
  inj' := fun _ _ h => congrArg Prod.fst h

/-- Optional-partner choice transported to man `m`'s contracts. -/
def inducedChoiceM (m : M) : ChoiceFunction (M × W) :=
  (ChoiceFunction.ofLinearOrder (mkt.prefM m)).map (partnerEmbeddingM m)

/-- Optional-partner choice transported to woman `w`'s contracts. -/
def inducedChoiceW (w : W) : ChoiceFunction (M × W) :=
  (ChoiceFunction.ofLinearOrder (mkt.prefW w)).map (partnerEmbeddingW w)

theorem inducedChoiceM_eq_map_ofLinearOrder (m : M) :
    mkt.inducedChoiceM m =
      (ChoiceFunction.ofLinearOrder (mkt.prefM m)).map (partnerEmbeddingM m) := rfl

theorem inducedChoiceW_eq_map_ofLinearOrder (w : W) :
    mkt.inducedChoiceW w =
      (ChoiceFunction.ofLinearOrder (mkt.prefW w)).map (partnerEmbeddingW w) := rfl

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
    (ChoiceFunction.mem_ofLinearOrder _)

/-- The symmetric order-theoretic choice specification. -/
theorem mem_inducedChoiceW_iff {m : M} {w : W} {Y : Set (M × W)} :
    (m, w) ∈ mkt.inducedChoiceW w Y ↔
      (m, w) ∈ Y ∧ mkt.leW w none (some m) ∧
        ∀ m', (m', w) ∈ Y → mkt.leW w (some m') (some m) :=
  (ChoiceFunction.mem_map _ (partnerEmbeddingW w) (x := m) (Y := Y)).trans
    (ChoiceFunction.mem_ofLinearOrder _)

theorem unitDemand_inducedChoiceM (m : M) :
    (mkt.inducedChoiceM m).UnitDemand :=
  (ChoiceFunction.unitDemand_ofLinearOrder _).map _

theorem unitDemand_inducedChoiceW (w : W) :
    (mkt.inducedChoiceW w).UnitDemand :=
  (ChoiceFunction.unitDemand_ofLinearOrder _).map _

theorem substitutable_inducedChoiceM (m : M) :
    (mkt.inducedChoiceM m).Substitutable :=
  (ChoiceFunction.substitutable_ofLinearOrder _).map _

theorem substitutable_inducedChoiceW (w : W) :
    (mkt.inducedChoiceW w).Substitutable :=
  (ChoiceFunction.substitutable_ofLinearOrder _).map _

theorem sizeMonotone_inducedChoiceM (m : M) :
    (mkt.inducedChoiceM m).SizeMonotone :=
  (ChoiceFunction.sizeMonotone_ofLinearOrder _).map _

theorem sizeMonotone_inducedChoiceW (w : W) :
    (mkt.inducedChoiceW w).SizeMonotone :=
  (ChoiceFunction.sizeMonotone_ofLinearOrder _).map _

theorem consistent_inducedChoiceM [Finite W] (m : M) :
    (mkt.inducedChoiceM m).Consistent :=
  (ChoiceFunction.consistent_ofLinearOrder _).map _

theorem consistent_inducedChoiceW [Finite M] (w : W) :
    (mkt.inducedChoiceW w).Consistent :=
  (ChoiceFunction.consistent_ofLinearOrder _).map _

/-! ## The induced contracts market -/

/-- The structural contracts market, without finiteness assumptions.
Women are buyers and men are sellers. -/
def toMarket : Market W M (M × W) where
  buyer := Prod.snd
  seller := Prod.fst
  choiceB := mkt.inducedChoiceW
  choiceS := mkt.inducedChoiceM
  buyer_eq_of_mem := fun _ _ _ hp => mkt.snd_eq_of_mem_inducedChoiceW hp
  seller_eq_of_mem := fun _ _ _ hp => mkt.fst_eq_of_mem_inducedChoiceM hp

@[simp] theorem toMarket_buyer (p : M × W) :
    mkt.toMarket.buyer p = p.2 := rfl

@[simp] theorem toMarket_seller (p : M × W) :
    mkt.toMarket.seller p = p.1 := rfl

@[simp] theorem toMarket_choiceB (w : W) :
    mkt.toMarket.choiceB w = mkt.inducedChoiceW w := rfl

@[simp] theorem toMarket_choiceS (m : M) :
    mkt.toMarket.choiceS m = mkt.inducedChoiceM m := rfl

/-- Structural optional-partner choice is local on arbitrary partner types.
This uses the transported menu, without finiteness or an IRC hypothesis. -/
theorem local_toMarket : mkt.toMarket.Local := by
  constructor
  · intro w Y
    change (ChoiceFunction.ofLinearOrder (mkt.prefW w)).map (partnerEmbeddingW w)
        (mkt.toMarket.buyerSide w Y) =
      (ChoiceFunction.ofLinearOrder (mkt.prefW w)).map (partnerEmbeddingW w) Y
    have hmenu : (partnerEmbeddingW w) ⁻¹' (mkt.toMarket.buyerSide w Y) =
        (partnerEmbeddingW w) ⁻¹' Y := by
      ext m
      change ((m, w) ∈ Y ∧ w = w) ↔ (m, w) ∈ Y
      exact and_iff_left rfl
    change _ '' _ ((partnerEmbeddingW w) ⁻¹' (mkt.toMarket.buyerSide w Y)) =
      _ '' _ ((partnerEmbeddingW w) ⁻¹' Y)
    rw [hmenu]
  · intro m Y
    change (ChoiceFunction.ofLinearOrder (mkt.prefM m)).map (partnerEmbeddingM m)
        (mkt.toMarket.sellerSide m Y) =
      (ChoiceFunction.ofLinearOrder (mkt.prefM m)).map (partnerEmbeddingM m) Y
    have hmenu : (partnerEmbeddingM m) ⁻¹' (mkt.toMarket.sellerSide m Y) =
        (partnerEmbeddingM m) ⁻¹' Y := by
      ext w
      change ((m, w) ∈ Y ∧ m = m) ↔ (m, w) ∈ Y
      exact and_iff_left rfl
    change _ '' _ ((partnerEmbeddingM m) ⁻¹' (mkt.toMarket.sellerSide m Y)) =
      _ '' _ ((partnerEmbeddingM m) ⁻¹' Y)
    rw [hmenu]

theorem consistent_toMarket [Finite M] [Finite W] : mkt.toMarket.Consistent :=
  ⟨mkt.consistent_inducedChoiceW, mkt.consistent_inducedChoiceM⟩

theorem substitutable_toMarket : mkt.toMarket.Substitutable :=
  ⟨mkt.substitutable_inducedChoiceW, mkt.substitutable_inducedChoiceM⟩

theorem sizeMonotone_toMarket : mkt.toMarket.SizeMonotone :=
  ⟨mkt.sizeMonotone_inducedChoiceW, mkt.sizeMonotone_inducedChoiceM⟩

/-! ## Finite maximum realization

The internal menu consists of `none` together with the available partners.
These finite maxima support the proposal algorithms; they do not enter the
structural definitions of choice or the contracts market. -/

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
  simpa only [bestM, Finset.mem_filter, Finset.mem_univ, true_and] using
    (ChoiceFunction.bestOption_eq_some_iff (mkt.prefM m)
      (Finset.univ.filter fun w => (m, w) ∈ Y) (x := w))

omit [Fintype W] in
/-- The symmetric finite maximum specification. -/
theorem bestW_eq_some_iff {m : M} {w : W} {Y : Set (M × W)} :
    mkt.bestW w Y = some m ↔
      (m, w) ∈ Y ∧ mkt.leW w none (some m) ∧
        ∀ m', (m', w) ∈ Y → mkt.leW w (some m') (some m) := by
  classical
  simpa only [bestW, Finset.mem_filter, Finset.mem_univ, true_and] using
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

end InducedChoice

end MarriageMarket

end MathEconLib.Matching
