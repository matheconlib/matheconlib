import MathEconLib.Choice.Basic

/-!
# Substitutability of choice functions

Substitutability is defined over arbitrary supersets of a menu. It is
equivalent to monotonicity of the rejection function and to the Chernoff
condition (Sen's α). No matching market or partner map is required.

The single-new-alternative condition of Hatfield–Kojima (2010), Definition 2,
p. 1708, is a corollary and is equivalent on finite alternative types. On
infinite types it is strictly weaker than the arbitrary-superset definition.
The weakened conditions using a partner map are defined in
`MathEconLib.Choice.Conditions.Matching.WeakSubstitutability`.
Relationships with other general conditions are in
`MathEconLib.Choice.Conditions.General.Relationships`.

## References

Hatfield–Kojima, *Substitutes and stability for matching with contracts*,
Journal of Economic Theory 145 (2010), 1704–1723,
DOI 10.1016/j.jet.2010.01.007.

Hatfield–Kominers, *The theory of matching with contracts*, Chapter 5,
Handbook of the Economics of Matching 2 (2025), 409–487,
DOI 10.1016/bs.hesmat.2025.10.005, Definition 2.1 and the following
rejection-function discussion, p. 414. The chapter's domains are finite;
the arbitrary-superset definition here applies to arbitrary types.
-/

namespace MathEconLib.Choice

universe u

variable {α : Type u}

namespace ChoiceFunction

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

end ChoiceFunction

end MathEconLib.Choice
