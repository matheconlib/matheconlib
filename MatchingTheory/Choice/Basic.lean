/-
Matching with contracts, Layer 0: abstract choice functions.

DRAFT — design signatures only. Not yet elaborated against mathlib; all
mathlib identifiers are provisional and all `sorry`s are
intentional. Paper proofs for the short lemmas are recorded in comments.
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

/-- A **choice function** on `α`: from any available set of alternatives it
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

/-- The **rejection function**: available but not chosen. -/
def rejected : Set α → Set α := fun Y => Y \ C Y

@[simp]
lemma mem_rejected {Y : Set α} {x : α} :
    x ∈ C.rejected Y ↔ x ∈ Y ∧ x ∉ C Y :=
  Iff.rfl

lemma choose_union_rejected (Y : Set α) : C Y ∪ C.rejected Y = Y := by
  sorry -- `Set.union_diff_cancel (C.choose_subset Y)` modulo name drift

/-! ### The four conditions -/

/-- **Irrelevance of rejected alternatives** (IRC / consistency), set form:
shrinking the available set without removing anything chosen leaves the choice
unchanged. The survey's one-element form (`x ∉ C Y → C (Y \ {x}) = C Y`) is a
special case, and equivalent to this under `Set.Finite`. -/
def Consistent : Prop :=
  ∀ ⦃Y Z : Set α⦄, C Y ⊆ Z → Z ⊆ Y → C Z = C Y

/-- **Substitutability** (survey Definition 2.1, superset form): an
alternative rejected from `insert x Y` stays rejected from `insert x Z`
whenever `Y ⊆ Z`. Defined in choice language so that the weakened variants
of survey §6 (`Matching.Contracts.WeakSubstitutes`) are literally this
statement with restricted quantifiers; `substitutable_iff_monotone_rejected`
recovers the order-theoretic form. -/
def Substitutable : Prop :=
  ∀ ⦃x : α⦄ ⦃Y Z : Set α⦄, Y ⊆ Z → x ∉ C (insert x Y) → x ∉ C (insert x Z)

/-- The **law of aggregate demand** (size monotonicity): more availability
never means fewer choices. Stated with `Set.ncard`; the intended use is
finite `α`, and theorems carry the finiteness. -/
def SizeMonotone : Prop :=
  ∀ ⦃Y Z : Set α⦄, Y ⊆ Z → (C Y).ncard ≤ (C Z).ncard

/-- **Unit demand**: at most one alternative is ever chosen. -/
def UnitDemand : Prop :=
  ∀ Y, (C Y).Subsingleton

/-- **Path independence** (Plott): the choice from a union may be computed by
first contracting one part to its choice. -/
def PathIndependent : Prop :=
  ∀ Y Z, C (Y ∪ Z) = C (C Y ∪ Z)

/-- The **Chernoff condition** (Sen's α, "heritage"): anything chosen from a
larger menu is still chosen from any smaller menu containing it. Equivalent
to substitutability (`substitutable_iff_chernoff`), and the engine of the
finiteness-free `PathIndependent → Substitutable` proof. -/
def Chernoff : Prop :=
  ∀ ⦃W V : Set α⦄, W ⊆ V → C V ∩ W ⊆ C W

/-! ### Characterizations of substitutability -/

/- For the theorems below the choice function is implicit, so that dot
notation on hypotheses (`hC.not_mem_insert_insert`, `h.substitutable`, …)
elaborates. -/
variable {C}

/-- Order-theoretic characterization: substitutability is exactly
monotonicity of the rejection function (the "isotone rejection" of the
literature, survey §2.1.2). Derived, not primary — see the design notes.

Paper proof. (⇐) apply monotonicity to `insert x Y ⊆ insert x Z`.
(⇒) given `Y ⊆ Z` and `x ∈ Y \ C Y`: since `x ∈ Y`, `insert x Y = Y`, so
`x ∉ C (insert x Y)`; the definition with `Y ⊆ Z` gives `x ∉ C (insert x Z)`,
and `insert x Z = Z` since `x ∈ Z`; with `x ∈ Z` this puts `x ∈ rejected Z`. -/
theorem substitutable_iff_monotone_rejected :
    C.Substitutable ↔ Monotone C.rejected := by
  sorry

/-- Substitutability is exactly the Chernoff condition — elementwise, the
contrapositive of rejection monotonicity. Finiteness-free.

Paper proof. Chernoff ⇒ monotone rejection: for `Y ⊆ Z` and `x ∈ Y \ C Y`,
if `x ∈ C Z` then Chernoff (with `W := Y`, `V := Z`) puts `x ∈ C Y` —
contradiction. Monotone rejection ⇒ Chernoff: for `x ∈ C V ∩ W` with
`W ⊆ V`, if `x ∉ C W` then `x ∈ rejected W ⊆ rejected V`, contradicting
`x ∈ C V`. -/
theorem substitutable_iff_chernoff : C.Substitutable ↔ C.Chernoff := by
  sorry

/-- Chosen-from-more implies chosen-from-less: the contrapositive of the
definition, in the form consumed by monotonicity of the deferred-acceptance
operator. -/
theorem Substitutable.mem_insert_of_subset (hC : C.Substitutable) {x : α}
    {Y Z : Set α} (hYZ : Y ⊆ Z) (hx : x ∈ C (insert x Z)) :
    x ∈ C (insert x Y) := by
  sorry

/-- The single-new-alternative form (survey Definition 2.1 as printed): the
exact shape mirrored by the weakened conditions of §6
(`Matching.Contracts.WeakSubstitutes`). **Strictly weaker** than
`Substitutable` in general — even together with `Consistent` — witnessed by
`ChoiceFunction.Counterexamples.infiniteOrEmpty`; equivalent under
finiteness via `not_mem_of_forall_insert_insert`. (Resolves SPEC Q9.) -/
theorem Substitutable.not_mem_insert_insert (hC : C.Substitutable) {x z : α}
    {Y : Set α} (hx : x ∉ C (insert x Y)) :
    x ∉ C (insert x (insert z Y)) :=
  hC (Set.subset_insert z Y) hx

/-- Conversely, the single-new-alternative form yields the superset
conclusion whenever the difference `Z \ Y` is finite.

Paper proof. Induct on the finite set `F := Z \ Y`
(`Set.Finite.induction_on`), showing `x ∉ C (insert x (Y ∪ F))` for every
finite `F`: the base case is the hypothesis, and the step is one application
of the single form; conclude by `Z = Y ∪ (Z \ Y)`. -/
theorem not_mem_of_forall_insert_insert
    (h : ∀ ⦃x z : α⦄ ⦃Y : Set α⦄,
      x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y)))
    {x : α} {Y Z : Set α} (hYZ : Y ⊆ Z) (hfin : (Z \ Y).Finite)
    (hx : x ∉ C (insert x Y)) :
    x ∉ C (insert x Z) := by
  sorry

/-- On a finite type the single-new-alternative form and `Substitutable`
coincide (SPEC Q9, resolved); `Counterexamples.infiniteOrEmpty` shows the
finiteness cannot be dropped. -/
theorem substitutable_iff_forall_insert_insert [Finite α] :
    C.Substitutable ↔
      ∀ ⦃x z : α⦄ ⦃Y : Set α⦄,
        x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y)) :=
  ⟨fun hC _x _z _Y hx => hC.not_mem_insert_insert hx,
    fun h _x _Y _Z hYZ hx =>
      not_mem_of_forall_insert_insert h hYZ (Set.toFinite _) hx⟩

/-! ### Unit demand -/

/-- Consistent unit-demand choice functions are substitutable (survey §2.1.2).

Paper proof (finiteness-free). Take `Y ⊆ Z` with `x ∉ C (insert x Y)`;
suppose `x ∈ C (insert x Z)`. Unit demand gives `C (insert x Z) = {x}`, so
`C (insert x Z) ⊆ insert x Y ⊆ insert x Z`, and consistency yields
`C (insert x Y) = {x} ∋ x`, a contradiction. -/
theorem UnitDemand.substitutable (h₁ : C.UnitDemand) (h₂ : C.Consistent) :
    C.Substitutable := by
  sorry

/-- Consistent unit-demand choice functions satisfy the law of aggregate
demand.

Paper proof. `C Y` and `C Z` are subsingletons, so it suffices that
`C Y ≠ ∅ → C Z ≠ ∅` for `Y ⊆ Z`; if `C Z = ∅` then `C Z ⊆ Y ⊆ Z` and
consistency forces `C Y = C Z = ∅`. -/
theorem UnitDemand.sizeMonotone (h₁ : C.UnitDemand) (h₂ : C.Consistent) :
    C.SizeMonotone := by
  sorry

/-! ### Path independence -/

/-- Substitutability + consistency imply path independence. Finiteness-free.

Paper proof. If `x ∈ C (Y ∪ Z)` with `x ∈ Y \ C Y`: since `x ∈ Y`,
`insert x Y = Y` and `insert x (Y ∪ Z) = Y ∪ Z`, so substitutability (with
`Y ⊆ Y ∪ Z`) turns `x ∉ C Y` into `x ∉ C (Y ∪ Z)` — contradiction; so
`C (Y ∪ Z) ⊆ C Y ∪ Z ⊆ Y ∪ Z` and consistency closes it. -/
theorem Substitutable.pathIndependent
    (h₁ : C.Substitutable) (h₂ : C.Consistent) : C.PathIndependent := by
  sorry

/-- Path independence implies consistency — **with no finiteness** (SPEC Q2,
resolved).

Paper proof. Given `C Y ⊆ Z ⊆ Y`, two rewrites and one instance of path
independence at the pair `(Y, Z)` suffice:
`C Z = C (C Y ∪ Z)` (as `C Y ⊆ Z`) `= C (Y ∪ Z)` (path independence)
`= C Y` (as `Z ⊆ Y`). -/
theorem PathIndependent.consistent (h : C.PathIndependent) : C.Consistent := by
  sorry

/-- Path independence implies substitutability — **with no finiteness**
(SPEC Q2, resolved) — via the Chernoff condition.

Paper proof. For `W ⊆ V`, path independence at the pair `(W, V \ W)` gives
`C V = C (W ∪ (V \ W)) = C (C W ∪ (V \ W)) ⊆ C W ∪ (V \ W)`; hence any
`x ∈ C V ∩ W` lies in `C W` (it cannot lie in `V \ W`). That is Chernoff;
conclude by `substitutable_iff_chernoff`. -/
theorem PathIndependent.substitutable (h : C.PathIndependent) :
    C.Substitutable := by
  sorry

/-- Aizerman–Malishevski / Chambers–Yenmez (survey fn. 16), **finiteness-free
in set form** (SPEC Q2, resolved — cross-checked by exhaustive enumeration on
a 3-element universe and structured sampling on 4–5 elements): path
independence is equivalent to substitutability together with consistency. -/
theorem pathIndependent_iff_substitutable_and_consistent :
    C.PathIndependent ↔ C.Substitutable ∧ C.Consistent :=
  ⟨fun h => ⟨h.substitutable, h.consistent⟩,
    fun h => h.1.pathIndependent h.2⟩

end ChoiceFunction
