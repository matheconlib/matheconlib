/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import MathEconLib.Choice.Basic

/-!
# Conditions on choice functions

This module defines optional conditions on general choice functions and proves
relationships between them. The development is motivated by matching with
contracts, but the definitions require only choices and menus, with no matching
market or map from contracts to agents. Matching terminology is explained beside
the relevant definitions. Conditions that use such a map, including unilateral
and bilateral substitutability and completion, are in
`MathEconLib.Choice.Matching.WeakSubstitutability` and
`MathEconLib.Choice.Matching.Completion`.

The sections cover substitutability and the Chernoff condition, irrelevance of
rejected alternatives, the law of aggregate demand, unit demand, finite-valuedness,
path independence, and relationships among these conditions. In particular:

* Substitutability and the law of aggregate demand imply consistency on finite
  menus, and hence on a finite alternative type.
* Consistent unit-demand choices are substitutable and satisfy the law of
  aggregate demand, without requiring a finite alternative type.
* Path independence is equivalent to substitutability and consistency without
  any finiteness assumption.

## References

Hatfield–Kojima, *Substitutes and stability for matching with contracts*,
Journal of Economic Theory 145 (2010), 1704–1723,
Definitions 2 and 7 (pp. 1708 and 1718), DOI 10.1016/j.jet.2010.01.007.

Hatfield–Kominers, *The theory of matching with contracts*, Chapter 5,
Handbook of the Economics of Matching 2 (2025), 409–487,
DOI 10.1016/bs.hesmat.2025.10.005. See p. 413 and footnote 10 for the
standing IRC assumption; Definition 2.1 and the following rejection-function
discussion, p. 414, for substitutability; Definition 2.2, p. 415, for
the law of aggregate demand; and footnote 16, p. 414, for path independence.
Unit demand is discussed on p. 413. These references use finite domains;
the sections below state the precise scope of each definition and theorem.

Further background: Aizerman–Malishevski (1981); Alkan–Gale consistency;
Aygün–Sönmez (2013); Chambers–Yenmez (2017); Plott (1973).
-/

namespace MathEconLib.Choice

universe u

variable {α : Type u}

namespace ChoiceFunction

/-! ## Substitutability and the Chernoff condition

Substitutability is defined over arbitrary supersets of a menu and is equivalent
to rejection monotonicity and the Chernoff condition (Sen's α). When alternatives
are contracts, this is the same substitutability condition. The single-new-alternative
form of Hatfield–Kojima (2010), Definition 2, p. 1708, is equivalent
on finite alternative types; on infinite types it is strictly weaker than the
arbitrary-superset definition. Weak substitutability conditions using a map from
contracts to agents are in `MathEconLib.Choice.Matching.WeakSubstitutability`.
-/

section Substitutability

variable (C : ChoiceFunction α)

/-- Arbitrary-superset substitutability. On finite types this agrees with
HK2010, Definition 2; see `substitutable_iff_forall_insert_insert`. -/
def Substitutable : Prop :=
  ∀ ⦃x : α⦄ ⦃Y Z : Set α⦄,
    Y ⊆ Z → x ∉ C (insert x Y) → x ∉ C (insert x Z)

/-- The Chernoff condition (Sen's α, "heritage"). -/
def Chernoff : Prop :=
  ∀ ⦃W V : Set α⦄, W ⊆ V → C V ∩ W ⊆ C W

variable {C}

/-- Order-theoretic characterization: substitutability is exactly
monotonicity of the rejection function. -/
theorem substitutable_iff_monotone_rejected :
    C.Substitutable ↔ Monotone C.rejected := by
  constructor
  · -- (⇒) `x ∈ Y` collapses `insert x Y` to `Y`.
    intro hsub Y Z hYZ x hx
    obtain ⟨hxY, hxC⟩ := hx
    refine ⟨hYZ hxY, ?_⟩
    have h1 : x ∉ C (insert x Y) := by
      rwa [Set.insert_eq_of_mem hxY]
    have h2 := hsub hYZ h1
    rwa [Set.insert_eq_of_mem (hYZ hxY)] at h2
  · -- (⇐) apply monotonicity at `insert x Y ⊆ insert x Z`.
    intro hmono x Y Z hYZ hx
    have h1 : x ∈ C.rejected (insert x Y) :=
      ⟨Set.mem_insert _ _, hx⟩
    have h2 : x ∈ C.rejected (insert x Z) :=
      hmono (Set.insert_subset_insert hYZ) h1
    exact h2.2

/-- Substitutability is exactly the Chernoff condition. Finiteness-free. -/
theorem substitutable_iff_chernoff :
    C.Substitutable ↔ C.Chernoff := by
  constructor
  · intro hsub W V hWV x hx
    obtain ⟨hxV, hxW⟩ := hx
    by_contra hxCW
    have h1 : x ∉ C (insert x W) := by
      rwa [Set.insert_eq_of_mem hxW]
    have h2 := hsub hWV h1
    rw [Set.insert_eq_of_mem (hWV hxW)] at h2
    exact h2 hxV
  · intro hch x Y Z hYZ hx hxZ
    exact hx
      (hch (Set.insert_subset_insert hYZ)
        ⟨hxZ, Set.mem_insert _ _⟩)

/-- Under substitutability, chosen-from-more implies chosen-from-less. -/
theorem Substitutable.mem_insert_of_subset
    (hsub : C.Substitutable) {x : α} {Y Z : Set α}
    (hYZ : Y ⊆ Z) (hx : x ∈ C (insert x Z)) :
    x ∈ C (insert x Y) := by
  by_contra h
  exact hsub hYZ h hx

/-- The single-new-alternative form (HK2010, Definition 2, p. 1708). -/
theorem Substitutable.not_mem_insert_insert
    (hsub : C.Substitutable) {x z : α} {Y : Set α}
    (hx : x ∉ C (insert x Y)) :
    x ∉ C (insert x (insert z Y)) :=
  hsub (Set.subset_insert z Y) hx

/-- Conversely, the single-new-alternative form yields the superset
conclusion whenever the difference `Z \ Y` is finite. -/
theorem not_mem_of_forall_insert_insert
    (h : ∀ ⦃x z : α⦄ ⦃Y : Set α⦄,
      x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y)))
    {x : α} {Y Z : Set α} (hYZ : Y ⊆ Z)
    (hfin : (Z \ Y).Finite) (hx : x ∉ C (insert x Y)) :
    x ∉ C (insert x Z) := by
  have key (S : Set α) (hS : S.Finite) :
      x ∉ C (insert x (Y ∪ S)) := by
    induction S, hS using Set.Finite.induction_on with
    | empty =>
        simpa using hx
    | insert _ _ ih =>
        simpa [Set.union_insert] using h ih
  rw [← Set.union_diff_cancel hYZ]
  exact key (Z \ Y) hfin

/-- On a finite domain the single-new-alternative form and `Substitutable`
coincide. -/
theorem substitutable_iff_forall_insert_insert [Finite α] :
    C.Substitutable ↔
      ∀ ⦃x z : α⦄ ⦃Y : Set α⦄,
        x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y)) :=
  ⟨fun hsub _x _z _Y hx => hsub.not_mem_insert_insert hx,
   fun h _x _Y _Z hYZ hx =>
     not_mem_of_forall_insert_insert h hYZ (Set.toFinite _) hx⟩

/-- A chosen alternative remains chosen when the menu contracts around it. -/
theorem Substitutable.mem_of_subset (hsub : C.Substitutable)
    {Y Z : Set α} {x : α} (hYZ : Y ⊆ Z) (hxZ : x ∈ C Z) (hxY : x ∈ Y) :
    x ∈ C Y :=
  (substitutable_iff_chernoff.mp hsub) hYZ ⟨hxZ, hxY⟩

end Substitutability

/-! ## Irrelevance of rejected alternatives

Consistency says that deleting unchosen alternatives leaves the chosen set
unchanged. When alternatives are contracts, it is called irrelevance of rejected
contracts (IRC). The definition and its idempotence consequence require no
finiteness assumption.
-/

section IrrelevanceOfRejectedAlternatives

variable (C : ChoiceFunction α)

/-- Irrelevance of rejected alternatives (IRC / consistency), set form. -/
def Consistent : Prop :=
  ∀ ⦃Y Z : Set α⦄, C Y ⊆ Z → Z ⊆ Y → C Z = C Y

variable {C}

/-- Choosing again from the chosen alternatives does not change an IRC choice. -/
theorem Consistent.idempotent (hcons : C.Consistent) (Y : Set α) :
    C (C Y) = C Y :=
  hcons Set.Subset.rfl (C.choose_subset Y)

end IrrelevanceOfRejectedAlternatives

/-! ## The law of aggregate demand

The law of aggregate demand says that enlarging a finite menu cannot reduce the
number of chosen alternatives (or contracts). Only the larger menu is required
to be finite; the alternative type may be infinite. Since `Set.ncard` is zero
on infinite sets, the definition imposes no condition on infinite menus.
-/

section LawOfAggregateDemand

variable (C : ChoiceFunction α)

/-- The law of aggregate demand on finite menus.

The larger menu is required to be finite: `Set.ncard` is `0` on infinite
sets, so using it on arbitrary menus would incorrectly rule out even the
identity choice function. On a finite contract type this is the usual law
of aggregate demand. No condition on infinite menus is imposed here. -/
def SizeMonotone : Prop :=
  ∀ ⦃Y Z : Set α⦄, Z.Finite → Y ⊆ Z → (C Y).ncard ≤ (C Z).ncard

variable {C}

/-- Apply the law of aggregate demand with an explicitly finite larger menu. -/
theorem SizeMonotone.ncard_le_of_finite (hC : C.SizeMonotone)
    {Y Z : Set α} (hZ : Z.Finite) (hYZ : Y ⊆ Z) :
    (C Y).ncard ≤ (C Z).ncard :=
  hC hZ hYZ

/-- On a finite type, no menu-finiteness argument is needed. -/
theorem SizeMonotone.ncard_le [Finite α] (hC : C.SizeMonotone)
    {Y Z : Set α} (hYZ : Y ⊆ Z) :
    (C Y).ncard ≤ (C Z).ncard :=
  hC (Set.toFinite Z) hYZ

/-- On a finite type, the law of aggregate demand is the usual
unrestricted natural-cardinality inequality. -/
theorem sizeMonotone_iff_ncard [Finite α] :
    C.SizeMonotone ↔
      ∀ ⦃Y Z : Set α⦄, Y ⊆ Z → (C Y).ncard ≤ (C Z).ncard :=
  ⟨fun h _ _ hYZ => h.ncard_le hYZ, fun h _ _ _hZ hYZ => h hYZ⟩

end LawOfAggregateDemand

/-! ## Unit demand

Unit demand requires at most one chosen alternative from each menu, with no
finiteness assumption. In matching with contracts, this means at most one chosen
contract. It is distinct from requiring at most one contract with each matching
partner: a choice can satisfy that feasibility requirement while choosing
contracts with several partners.
-/

section UnitDemand

variable (C : ChoiceFunction α)

/-- Unit demand: at most one alternative is ever chosen. -/
def UnitDemand : Prop :=
  ∀ Y, (C Y).Subsingleton

end UnitDemand

/-! ## Finite-valued choice

Finite-valuedness requires every chosen set to be finite, while menus and the
alternative type may be infinite. In matching with contracts, this is finiteness
of the chosen contract sets. Every choice on a finite alternative type is
finite-valued, and pointwise smaller choices preserve finite-valuedness.
-/

section FiniteValued

variable (C : ChoiceFunction α)

/-- Every choice is finite. This does not require finite menus or a finite
universe of alternatives. -/
def FiniteValued : Prop :=
  ∀ Y, (C Y).Finite

variable {C}

/-- Every choice function on a finite universe is finite-valued. -/
theorem finiteValued_of_finite [Finite α] (C : ChoiceFunction α) :
    C.FiniteValued :=
  fun Y => Set.toFinite (C Y)

/-- Passing to pointwise smaller choices preserves finite-valuedness. -/
theorem FiniteValued.of_le {D : ChoiceFunction α}
    (hD : D.FiniteValued) (hCD : C ≤ D) : C.FiniteValued :=
  fun Y => (hD Y).subset (hCD Y)

end FiniteValued

/-! ## Path independence

Path independence says that choosing from part of a menu before adding the
remaining alternatives does not change the final choice. The definition and
union identities apply to arbitrary types, including contract types, without
finiteness assumptions. The identities require path independence; they do not
hold for every choice function.
-/

section PathIndependence

variable (C : ChoiceFunction α)

/-- Path independence (Plott). -/
def PathIndependent : Prop :=
  ∀ Y Z, C (Y ∪ Z) = C (C Y ∪ Z)

variable {C}

/-- Under path independence, menus with the same choices remain equivalent
after adding the same alternatives. -/
theorem PathIndependent.union_congr_left (hpi : C.PathIndependent)
    {A B : Set α} (hAB : C A = C B) (Z : Set α) :
    C (A ∪ Z) = C (B ∪ Z) := by
  rw [hpi A Z, hpi B Z, hAB]

/-- A menu contributes nothing beyond alternatives whose choices are already
available in the other menu. -/
theorem PathIndependent.union_eq_left_of_choice_subset (hpi : C.PathIndependent)
    {U W : Set α} (hW : C W ⊆ U) :
    C (U ∪ W) = C U := by
  rw [Set.union_comm U W, hpi W U,
    Set.union_eq_self_of_subset_left hW]

end PathIndependence

/-! ## Relationships between conditions
-/

section Relationships

variable (C : ChoiceFunction α)

variable {C}

/-- Substitutability and the law of aggregate demand imply IRC whenever the
original menu is finite. Substitutability gives `C Y ⊆ C Z`, while the law of
aggregate demand gives the reverse cardinality inequality. -/
theorem Substitutable.consistent_on_finite_menu
    (hsub : C.Substitutable) (hload : C.SizeMonotone)
    {Y Z : Set α} (hY : Y.Finite) (hCY : C Y ⊆ Z) (hZY : Z ⊆ Y) :
    C Z = C Y := by
  have hchoice : C Y ⊆ C Z := fun _ hx =>
    (substitutable_iff_chernoff.mp hsub) hZY ⟨hx, hCY hx⟩
  have hcard : (C Z).ncard ≤ (C Y).ncard := hload hY hZY
  have hfin : (C Z).Finite :=
    hY.subset (fun _ hx => hZY (C.choose_subset Z hx))
  exact (Set.eq_of_subset_of_ncard_le hchoice hcard hfin).symm

/-- On a finite universe, substitutability and the law of aggregate demand
already imply consistency (IRC). -/
theorem Substitutable.consistent_of_sizeMonotone [Finite α]
    (hsub : C.Substitutable) (hload : C.SizeMonotone) :
    C.Consistent :=
  fun {_Y _Z} hCY hZY =>
    hsub.consistent_on_finite_menu hload (Set.toFinite _) hCY hZY

/-- Consistent unit-demand choice functions are substitutable. -/
theorem UnitDemand.substitutable
    (hunit : C.UnitDemand) (hcons : C.Consistent) :
    C.Substitutable := by
  intro x Y Z hYZ hx hxZ
  have hsubset : C (insert x Z) ⊆ insert x Y := by
    intro y hy
    have hyx : y = x := hunit _ hy hxZ
    simp [hyx]
  have hEq : C (insert x Y) = C (insert x Z) :=
    hcons hsubset (Set.insert_subset_insert hYZ)
  rw [hEq] at hx
  exact hx hxZ

/-- Consistent unit-demand choice functions satisfy the law of aggregate
demand. -/
theorem UnitDemand.sizeMonotone
    (hunit : C.UnitDemand) (hcons : C.Consistent) :
    C.SizeMonotone := by
  intro Y Z _hZfin hYZ
  rcases Set.eq_empty_or_nonempty (C Y) with hY | ⟨x, hx⟩
  · simp [hY]
  · have hZ : (C Z).Nonempty := by
      rcases Set.eq_empty_or_nonempty (C Z) with hZ | hZ
      · exfalso
        have h0 : C Z ⊆ Y := by
          rw [hZ]
          exact Set.empty_subset _
        have hEq := hcons h0 hYZ
        rw [hEq, hZ] at hx
        exact hx
      · exact hZ
    obtain ⟨z, hz⟩ := hZ
    rw [(hunit Y).eq_singleton_of_mem hx,
      (hunit Z).eq_singleton_of_mem hz]
    simp

/-- Substitutability + consistency imply path independence. Finiteness-free. -/
theorem Substitutable.pathIndependent
    (hsub : C.Substitutable) (hcons : C.Consistent) :
    C.PathIndependent := by
  intro Y Z
  have hch : C.Chernoff :=
    substitutable_iff_chernoff.mp hsub
  apply
    (hcons ?_
      (Set.union_subset_union_left _ (C.choose_subset Y))).symm
  intro x hx
  rcases C.choose_subset _ hx with hxY | hxZ
  · exact Set.mem_union_left _
      (hch Set.subset_union_left ⟨hx, hxY⟩)
  · exact Set.mem_union_right _ hxZ

/-- Path independence implies consistency — even without finiteness. -/
theorem PathIndependent.consistent
    (hpi : C.PathIndependent) :
    C.Consistent := by
  intro Y Z hCY hZY
  have e1 : C Y ∪ Z = Z :=
    Set.union_eq_self_of_subset_left hCY
  have e2 : Y ∪ Z = Y :=
    Set.union_eq_self_of_subset_right hZY
  calc
    C Z = C (C Y ∪ Z) := by rw [e1]
    _ = C (Y ∪ Z) := (hpi Y Z).symm
    _ = C Y := by rw [e2]

/-- Path independence implies substitutability — even without finiteness — via the
Chernoff condition. -/
theorem PathIndependent.substitutable
    (hpi : C.PathIndependent) :
    C.Substitutable := by
  rw [substitutable_iff_chernoff]
  intro W V hWV x hx
  obtain ⟨hxV, hxW⟩ := hx
  have hx :
      x ∈ C (C W ∪ (V \ W)) := by
    rw [← hpi W (V \ W), Set.union_diff_cancel hWV]
    exact hxV
  rcases C.choose_subset _ hx with hxCW | hxDiff
  · exact hxCW
  · exact (hxDiff.2 hxW).elim

/-- Aizerman–Malishevski / Chambers–Yenmez, finiteness-free in set form. -/
theorem pathIndependent_iff_substitutable_and_consistent :
    C.PathIndependent ↔ C.Substitutable ∧ C.Consistent :=
  ⟨fun hpi => ⟨hpi.substitutable, hpi.consistent⟩,
   fun h => h.1.pathIndependent h.2⟩

end Relationships

end ChoiceFunction

end MathEconLib.Choice
