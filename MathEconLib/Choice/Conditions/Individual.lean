import MathEconLib.Choice.Basic

/-!
# Conditions on an individual choice function

These optional conditions describe a single choice function using only its
choices and menus. They are separate from the definition of `ChoiceFunction`
and make sense in general choice theory, independently of a matching market.
Here “individual” distinguishes conditions requiring no additional data from
conditions that also identify the matching partner associated with each
alternative; it does not impose an individual-agent model.

The current development uses these conditions in matching with contracts.
That application motivates the terminology and references, but does not
restrict the alternatives to contracts or require agents or market sides.

## Main definitions

* `ChoiceFunction.Consistent` — irrelevance of rejected alternatives (IRC),
  in *set form* (Aygün–Sönmez 2013; Alkan–Gale consistency).
* `ChoiceFunction.Substitutable` — no newly available alternative rescues a
  rejected one (arbitrary-superset extension of HK2010, Definition 2);
  rejection-function monotonicity is the derived characterization.
* `ChoiceFunction.SizeMonotone` — the law of aggregate demand on finite menus
  (HK2010, Definition 7, p. 1718, on finite types).
* `ChoiceFunction.UnitDemand` — at most one alternative is chosen.
* `ChoiceFunction.FiniteValued` — every chosen set is finite, even when the
  menu or the universe of alternatives is infinite.
* `ChoiceFunction.PathIndependent` and `ChoiceFunction.Chernoff`.

## Design notes

* Substitutability is defined in choice language over arbitrary supersets
  (`Y ⊆ Z`), with `Monotone rejected` as the derived characterization
  (`substitutable_iff_monotone_rejected`). The weakened conditions in HK2010
  restrict the quantifiers using matching-partner data; see
  `MathEconLib.Choice.Conditions.WithPartners.Basic`. The single-new-alternative form in
  HK2010 is the corollary `Substitutable.not_mem_insert_insert`; this form is
  strictly weaker on infinite types.
* IRC is taken in set form. The definition and the path-independence
  characterization require no finiteness assumption.
* The final choice-algebra lemmas use these conditions explicitly; they are
  not properties of every choice function.

## References

HK2010: Hatfield–Kojima, *Substitutes and stability for matching with
contracts*, Journal of Economic Theory 145 (2010), 1704–1723,
Definitions 2 and 7 (pp. 1708 and 1718), DOI 10.1016/j.jet.2010.01.007.

HKSurvey2025: Hatfield–Kominers, *The theory of matching with contracts*,
Chapter 5, Handbook of the Economics of Matching 2 (2025), 409–487,
DOI 10.1016/bs.hesmat.2025.10.005. See p. 413 and footnote 10 for the
standing IRC assumption; Definition 2.1 and the following rejection-function
discussion, p. 414, for substitutability; Definition 2.2, p. 415, for
the law of aggregate demand; and footnote 16, p. 414, for path independence. Unit demand
is discussed on p. 413. The chapter's domains are finite, whereas the
definitions here have the scope stated above.

Further background: Aizerman–Malishevski (1981); Chambers–Yenmez (2017);
Plott (1973).
-/

namespace MathEconLib.Choice

universe u

variable {α : Type u}

namespace ChoiceFunction

variable (C : ChoiceFunction α)

/-! ### Choice properties -/

/-- Irrelevance of rejected alternatives (IRC / consistency), set form. -/
def Consistent : Prop :=
  ∀ ⦃Y Z : Set α⦄, C Y ⊆ Z → Z ⊆ Y → C Z = C Y

/-- Arbitrary-superset substitutability. On finite types this agrees with
HK2010, Definition 2; see `substitutable_iff_forall_insert_insert`. -/
def Substitutable : Prop :=
  ∀ ⦃x : α⦄ ⦃Y Z : Set α⦄,
    Y ⊆ Z → x ∉ C (insert x Y) → x ∉ C (insert x Z)

/-- The law of aggregate demand on finite menus.

The larger menu is required to be finite: `Set.ncard` is `0` on infinite
sets, so using it on arbitrary menus would incorrectly rule out even the
identity choice function. On a finite contract type this is the usual law
of aggregate demand. No condition on infinite menus is imposed here. -/
def SizeMonotone : Prop :=
  ∀ ⦃Y Z : Set α⦄, Z.Finite → Y ⊆ Z → (C Y).ncard ≤ (C Z).ncard

/-- Unit demand: at most one alternative is ever chosen. -/
def UnitDemand : Prop :=
  ∀ Y, (C Y).Subsingleton

/-- Every choice is finite. This does not require finite menus or a finite
universe of alternatives. -/
def FiniteValued : Prop :=
  ∀ Y, (C Y).Finite

/-- Path independence (Plott). -/
def PathIndependent : Prop :=
  ∀ Y Z, C (Y ∪ Z) = C (C Y ∪ Z)

/-- The Chernoff condition (Sen's α, "heritage"). -/
def Chernoff : Prop :=
  ∀ ⦃W V : Set α⦄, W ⊆ V → C V ∩ W ⊆ C W

/-! ### Characterizations of substitutability -/

variable {C}

/-- Every choice function on a finite universe is finite-valued. -/
theorem finiteValued_of_finite [Finite α] (C : ChoiceFunction α) :
    C.FiniteValued :=
  fun Y => Set.toFinite (C Y)

/-- Passing to pointwise smaller choices preserves finite-valuedness. -/
theorem FiniteValued.of_le {D : ChoiceFunction α}
    (hD : D.FiniteValued) (hCD : C ≤ D) : C.FiniteValued :=
  fun Y => (hD Y).subset (hCD Y)

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

/-! ### Unit demand -/

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

/-! ### Path independence -/

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

/-! ### Choice algebra -/

/-- Choosing again from the chosen alternatives does not change an IRC choice. -/
theorem Consistent.idempotent (hcons : C.Consistent) (Y : Set α) :
    C (C Y) = C Y :=
  hcons Set.Subset.rfl (C.choose_subset Y)

/-- A chosen alternative remains chosen when the menu contracts around it. -/
theorem Substitutable.mem_of_subset (hsub : C.Substitutable)
    {Y Z : Set α} {x : α} (hYZ : Y ⊆ Z) (hxZ : x ∈ C Z) (hxY : x ∈ Y) :
    x ∈ C Y :=
  (substitutable_iff_chernoff.mp hsub) hYZ ⟨hxZ, hxY⟩

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

end ChoiceFunction

end MathEconLib.Choice
