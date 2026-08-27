/-
Matching with contracts, Layer 0: abstract choice functions.
-/
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Card

/-!
# Abstract choice functions

The market-free revealed-preference layer of the library. A *choice function*
on a type `α` selects a subset of any available set of alternatives. No agents,
no contracts, no sides: substitutability, consistency (IRC), the law of
aggregate demand, unit demand, and path independence are all properties of a
single such map, and everything downstream (two-sided markets now, trading
networks later) reuses this layer unchanged.

## Main definitions

* `ChoiceFunction α` — a map `Set α → Set α` choosing a subset of its input.
* `ChoiceFunction.rejected` — available-but-not-chosen alternatives.
* `ChoiceFunction.Consistent` — irrelevance of rejected alternatives (IRC),
  in *set form* (Aygün–Sönmez 2013; Alkan–Gale consistency).
* `ChoiceFunction.Substitutable` — no newly available alternative rescues a
  rejected one (survey Definition 2.1, superset form); rejection-function
  monotonicity is the *derived* characterization.
* `ChoiceFunction.SizeMonotone` — the law of aggregate demand (Definition 2.2).
* `ChoiceFunction.UnitDemand`, `ChoiceFunction.PathIndependent`.

## Design notes

* Substitutability is *defined* in choice language over arbitrary supersets
  (`Y ⊆ Z`), with `Monotone rejected` as the derived characterization
  (`substitutable_iff_monotone_rejected`). Rationale: the weakened conditions
  of survey §6 are choice-language statements with restricted quantifiers
  (see `Matching.Contracts.WeakSubstitutes`), so the strong definition
  anchors that family and `Substitutable → Unilateral → Bilateral` becomes
  quantifier bookkeeping. The survey's printed one-new-contract form is the
  corollary `Substitutable.not_mem_insert_insert` — the exact shape §6
  mirrors — and is strictly weaker on infinite types.
* IRC is taken in set form so that agent locality and the fixed-point
  development need no finiteness anywhere (SPEC §3, D2).

## References

Hatfield–Kominers, *The theory of matching with contracts*, §§2.1–2.2;
Aizerman–Malishevski (1981); Chambers–Yenmez (2017); Plott (1973).
-/

universe u

variable {α : Type u}

/-- A choice function on `α`: from any available set of alternatives it
selects a subset. -/
structure ChoiceFunction (α : Type u) where
  /-- The underlying selection map. -/
  toFun : Set α → Set α
  /-- Only available alternatives are chosen. -/
  choose_subset' : ∀ Y, toFun Y ⊆ Y

namespace ChoiceFunction

instance : FunLike (ChoiceFunction α) (Set α) (Set α) where
  coe := toFun
  coe_injective' := by rintro ⟨f, _⟩ ⟨g, _⟩ h; simpa using h

@[ext]
lemma ext {C D : ChoiceFunction α} (h : ∀ Y, C Y = D Y) : C = D :=
  DFunLike.ext _ _ h

variable (C : ChoiceFunction α)

lemma choose_subset (Y : Set α) : C Y ⊆ Y := C.choose_subset' Y

/-- The rejection function: available but not chosen. -/
def rejected : Set α → Set α := fun Y => Y \ C Y

@[simp]
lemma mem_rejected {Y : Set α} {x : α} :
    x ∈ C.rejected Y ↔ x ∈ Y ∧ x ∉ C Y :=
  Iff.rfl

lemma choose_union_rejected (Y : Set α) : C Y ∪ C.rejected Y = Y :=
  Set.union_diff_cancel (C.choose_subset Y)

/-! ### The four key regularity conditions -/

/-- Irrelevance of rejected alternatives (IRC / consistency), set form. -/
def Consistent : Prop :=
  ∀ ⦃Y Z : Set α⦄, C Y ⊆ Z → Z ⊆ Y → C Z = C Y

/-- Substitutability (survey Definition 2.1, superset form). -/
def Substitutable : Prop :=
  ∀ ⦃x : α⦄ ⦃Y Z : Set α⦄, Y ⊆ Z → x ∉ C (insert x Y) → x ∉ C (insert x Z)

/-- The law of aggregate demand (size monotonicity). -/
def SizeMonotone : Prop :=
  ∀ ⦃Y Z : Set α⦄, Y ⊆ Z → (C Y).ncard ≤ (C Z).ncard

/-- Unit demand: at most one alternative is ever chosen. -/
def UnitDemand : Prop :=
  ∀ Y, (C Y).Subsingleton

/-- Path independence (Plott). -/
def PathIndependent : Prop :=
  ∀ Y Z, C (Y ∪ Z) = C (C Y ∪ Z)

/-- The Chernoff condition (Sen's α, "heritage"). -/
def Chernoff : Prop :=
  ∀ ⦃W V : Set α⦄, W ⊆ V → C V ∩ W ⊆ C W

/-! ### Characterizations of substitutability -/

variable {C}

/-- Order-theoretic characterization: substitutability is exactly
monotonicity of the rejection function. -/
theorem substitutable_iff_monotone_rejected :
    C.Substitutable ↔ Monotone C.rejected := by
  constructor
  · -- (⇒) `x ∈ Y` collapses `insert x Y` to `Y`.
    intro h Y Z hYZ x hx
    obtain ⟨hxY, hxC⟩ := hx
    refine ⟨hYZ hxY, ?_⟩
    have h1 : x ∉ C (insert x Y) := by rwa [Set.insert_eq_of_mem hxY]
    have h2 := h hYZ h1
    rwa [Set.insert_eq_of_mem (hYZ hxY)] at h2
  · -- (⇐) apply monotonicity at `insert x Y ⊆ insert x Z`.
    intro h x Y Z hYZ hx
    have h1 : x ∈ C.rejected (insert x Y) := ⟨Set.mem_insert _ _, hx⟩
    have h2 : x ∈ C.rejected (insert x Z) := h (Set.insert_subset_insert hYZ) h1
    exact h2.2

/-- Substitutability is exactly the Chernoff condition. Finiteness-free. -/
theorem substitutable_iff_chernoff : C.Substitutable ↔ C.Chernoff := by
  constructor
  · intro h W V hWV x hx
    obtain ⟨hxV, hxW⟩ := hx
    by_contra hxCW
    have h1 : x ∉ C (insert x W) := by rwa [Set.insert_eq_of_mem hxW]
    have h2 := h hWV h1
    rw [Set.insert_eq_of_mem (hWV hxW)] at h2
    exact h2 hxV
  · intro h x Y Z hYZ hx hxZ
    exact hx (h (Set.insert_subset_insert hYZ) ⟨hxZ, Set.mem_insert _ _⟩)

/-- Chosen-from-more implies chosen-from-less. -/
theorem Substitutable.mem_insert_of_subset (hC : C.Substitutable) {x : α}
    {Y Z : Set α} (hYZ : Y ⊆ Z) (hx : x ∈ C (insert x Z)) :
    x ∈ C (insert x Y) := by
  by_contra h
  exact hC hYZ h hx

/-- The single-new-alternative form (survey Definition 2.1 as printed). -/
theorem Substitutable.not_mem_insert_insert (hC : C.Substitutable) {x z : α}
    {Y : Set α} (hx : x ∉ C (insert x Y)) :
    x ∉ C (insert x (insert z Y)) :=
  hC (Set.subset_insert z Y) hx

/-- Conversely, the single-new-alternative form yields the superset
conclusion whenever the difference `Z \ Y` is finite. -/
theorem not_mem_of_forall_insert_insert
    (h : ∀ ⦃x z : α⦄ ⦃Y : Set α⦄,
      x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y)))
    {x : α} {Y Z : Set α} (hYZ : Y ⊆ Z) (hfin : (Z \ Y).Finite)
    (hx : x ∉ C (insert x Y)) :
    x ∉ C (insert x Z) := by
  classical
  -- One application of `h` per element of an enumeration of `Z \ Y`.
  have key : ∀ l : List α, x ∉ C (insert x (Y ∪ {y | y ∈ l})) := by
    intro l
    induction l with
    | nil =>
        have e : {y | y ∈ ([] : List α)} = (∅ : Set α) := by ext y; simp
        rw [e, Set.union_empty]
        exact hx
    | cons a l ih =>
        have e : {y | y ∈ a :: l} = insert a {y | y ∈ l} := by ext y; simp
        rw [e, Set.union_insert]
        exact h ih
  have hlist : {y | y ∈ hfin.toFinset.toList} = Z \ Y := by
    ext y; simp
  have hZ : Z = Y ∪ {y | y ∈ hfin.toFinset.toList} := by
    rw [hlist, Set.union_diff_cancel hYZ]
  rw [hZ]
  exact key hfin.toFinset.toList

/-- On a finite type the single-new-alternative form and `Substitutable`
coincide. -/
theorem substitutable_iff_forall_insert_insert [Finite α] :
    C.Substitutable ↔
      ∀ ⦃x z : α⦄ ⦃Y : Set α⦄,
        x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y)) :=
  ⟨fun hC _x _z _Y hx => hC.not_mem_insert_insert hx,
   fun h _x _Y _Z hYZ hx =>
     not_mem_of_forall_insert_insert h hYZ (Set.toFinite _) hx⟩

/-! ### Unit demand -/

/-- Consistent unit-demand choice functions are substitutable. -/
theorem UnitDemand.substitutable (h₁ : C.UnitDemand) (h₂ : C.Consistent) :
    C.Substitutable := by
  intro x Y Z hYZ hx hxZ
  -- Unit demand pins `C (insert x Z) = {x} ⊆ insert x Y`; then IRC.
  have hsub : C (insert x Z) ⊆ insert x Y := by
    intro y hy
    have hyx : y = x := h₁ (insert x Z) hy hxZ
    exact hyx ▸ Set.mem_insert _ _
  have hIns : insert x Y ⊆ insert x Z := Set.insert_subset_insert hYZ
  have hEq := h₂ hsub hIns
  rw [hEq] at hx
  exact hx hxZ

/-- Consistent unit-demand choice functions satisfy the law of aggregate
demand. -/
theorem UnitDemand.sizeMonotone (h₁ : C.UnitDemand) (h₂ : C.Consistent) :
    C.SizeMonotone := by
  intro Y Z hYZ
  rcases Set.eq_empty_or_nonempty (C Y) with hY | ⟨x, hx⟩
  · simp [hY]
  · have hZ : (C Z).Nonempty := by
      rcases Set.eq_empty_or_nonempty (C Z) with hZ | hZ
      · exfalso
        have h0 : C Z ⊆ Y := by rw [hZ]; exact Set.empty_subset _
        have hEq := h₂ h0 hYZ
        rw [hEq, hZ] at hx
        exact hx
      · exact hZ
    obtain ⟨z, hz⟩ := hZ
    rw [(h₁ Y).eq_singleton_of_mem hx, (h₁ Z).eq_singleton_of_mem hz]
    simp

/-! ### Path independence -/

/-- Substitutability + consistency imply path independence. Finiteness-free. -/
theorem Substitutable.pathIndependent
    (h₁ : C.Substitutable) (h₂ : C.Consistent) : C.PathIndependent := by
  intro Y Z
  have hch : C.Chernoff := substitutable_iff_chernoff.mp h₁
  have h3 : C (Y ∪ Z) ⊆ C Y ∪ Z := by
    intro x hx
    by_cases hz : x ∈ Z
    · exact Set.mem_union_right _ hz
    · have hxY : x ∈ Y := by
        rcases C.choose_subset _ hx with hxY | hxZ
        · exact hxY
        · exact absurd hxZ hz
      exact Set.mem_union_left _
        (hch (fun y hy => Set.mem_union_left Z hy) ⟨hx, hxY⟩)
  have h4 : C Y ∪ Z ⊆ Y ∪ Z :=
    Set.union_subset_union_left _ (C.choose_subset Y)
  exact (h₂ h3 h4).symm

/-- Path independence implies consistency — with no finiteness. -/
theorem PathIndependent.consistent (h : C.PathIndependent) : C.Consistent := by
  intro Y Z hCY hZY
  have e1 : C Y ∪ Z = Z := Set.union_eq_self_of_subset_left hCY
  have e2 : Y ∪ Z = Y := Set.union_eq_self_of_subset_right hZY
  calc C Z = C (C Y ∪ Z) := by rw [e1]
    _ = C (Y ∪ Z) := (h Y Z).symm
    _ = C Y := by rw [e2]

/-- Path independence implies substitutability — with no finiteness — via the
Chernoff condition. -/
theorem PathIndependent.substitutable (h : C.PathIndependent) :
    C.Substitutable := by
  rw [substitutable_iff_chernoff]
  intro W V hWV x hx
  obtain ⟨hxV, hxW⟩ := hx
  have e : W ∪ (V \ W) = V := Set.union_diff_cancel hWV
  have h1 : C V ⊆ C W ∪ (V \ W) := by
    have hpi := h W (V \ W)
    rw [e] at hpi
    rw [hpi]
    exact C.choose_subset _
  rcases h1 hxV with hc | hd
  · exact hc
  · exact absurd hxW hd.2

/-- Aizerman–Malishevski / Chambers–Yenmez, finiteness-free in set form. -/
theorem pathIndependent_iff_substitutable_and_consistent :
    C.PathIndependent ↔ C.Substitutable ∧ C.Consistent :=
  ⟨fun h => ⟨h.substitutable, h.consistent⟩,
   fun h => h.1.pathIndependent h.2⟩

end ChoiceFunction
