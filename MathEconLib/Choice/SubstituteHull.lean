/-
The least substitutable enlargement of a choice function.
-/
import MathEconLib.Choice.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Closure

/-!
# The substitute hull

`ChoiceFunction.substituteHull` retains an available alternative whenever
the original choice selects it from some larger menu. This is the classical
hereditary upper approximation (Litvakov, 1985, Theorem 5, table row H,
p. 127 of the Russian original), here defined on the full power set.

The hull is the minimal substitutable pointwise enlargement of any choice
function. `substituteHullClosure` bundles it as a closure operator whose
closed elements are exactly the substitutable choice functions. It also
preserves consistency (IRC),
so an IRC choice function has a minimal path-independent enlargement.

All results in this module hold for arbitrary types. Neither finiteness nor
a counterparty map is needed. The matching-specific question of when this
enlargement is a completion is treated separately in
`MathEconLib.Choice.UnilateralSubstitutabilityImpliesSubstitutableCompletability`.
An enlargement and a completion are different notions: a completion need
not contain the original choices pointwise.

Monjardet–Raderanirina (2004), §§3.1–3.2, Definitions 10–11 and
Propositions 1–3, pp. 355–357, provide finite lattice background for the
pointwise inclusion order and hereditary choices. The arbitrary-type hull,
closure, and IRC-preservation results below are proved independently.

## References

* Litvakov, B. M. (1985), *Approximation of choice functions with a bounded
  set of presentations*, Avtomatika i Telemekhanika, no. 2, 124–129
  (Russian original), Theorem 5, table row H, p. 127.
  Publication record: https://www.mathnet.ru/eng/at6893.
  English translation: Automation and Remote Control 46, 248–252;
  the English-page locator has not been checked.
* Monjardet, B. and Raderanirina, V. (2004), *Lattices of choice functions
  and consensus problems*, Social Choice and Welfare 23, 349–382,
  DOI 10.1007/s00355-003-0251-9.
-/

namespace MathEconLib.Choice

namespace ChoiceFunction

variable {α : Type*}

/-- An available alternative belongs to the substitute hull when it is
chosen from some larger menu. -/
def substituteHull (C : ChoiceFunction α) : ChoiceFunction α where
  toFun Y := {x | x ∈ Y ∧ ∃ Z, Y ⊆ Z ∧ x ∈ C Z}
  choose_subset := fun _ _ hx => hx.1

@[simp] theorem mem_substituteHull
    (C : ChoiceFunction α) {Y : Set α} {x : α} :
    x ∈ C.substituteHull Y ↔
      x ∈ Y ∧ ∃ Z, Y ⊆ Z ∧ x ∈ C Z :=
  Iff.rfl

/-- The substitute hull contains the original choices at every menu. -/
theorem le_substituteHull (C : ChoiceFunction α) : C ≤ C.substituteHull := by
  intro Y x hx
  exact ⟨C.choose_subset Y hx, Y, Set.Subset.rfl, hx⟩

/-- Set-level form of `le_substituteHull`. -/
theorem subset_substituteHull (C : ChoiceFunction α) (Y : Set α) :
    C Y ⊆ C.substituteHull Y :=
  le_substituteHull C Y

/-- The substitute hull satisfies substitutability without assumptions
on the original choice function. -/
theorem substituteHull_substitutable (C : ChoiceFunction α) :
    C.substituteHull.Substitutable := by
  apply substitutable_iff_chernoff.mpr
  intro Y Z hYZ x hx
  rcases hx with ⟨⟨_hxZ, W, hZW, hxW⟩, hxY⟩
  exact ⟨hxY, W, fun y hy => hZW (hYZ hy), hxW⟩

/-- Every substitutable enlargement contains the substitute hull. -/
theorem substituteHull_le {C D : ChoiceFunction α}
    (hD : D.Substitutable) (hCD : C ≤ D) :
    C.substituteHull ≤ D := by
  intro Y x hx
  rcases hx with ⟨hxY, Z, hYZ, hxZ⟩
  exact (substitutable_iff_chernoff.mp hD) hYZ ⟨hCD Z hxZ, hxY⟩

/-- The substitute hull as a closure operator on choice functions ordered
by pointwise inclusion. Its closedness predicate is substitutability. -/
def substituteHullClosure : ClosureOperator (ChoiceFunction α) :=
  ClosureOperator.ofPred substituteHull Substitutable le_substituteHull
    substituteHull_substitutable (fun _ _ hCD hD => substituteHull_le hD hCD)

@[simp] theorem substituteHullClosure_apply (C : ChoiceFunction α) :
    substituteHullClosure C = C.substituteHull := rfl

@[simp] theorem substituteHullClosure_isClosed (C : ChoiceFunction α) :
    substituteHullClosure.IsClosed C ↔ C.Substitutable := Iff.rfl

/-- For a substitutable upper bound, bounding the hull is equivalent to
bounding the original choice function. -/
theorem substituteHull_le_iff {C D : ChoiceFunction α}
    (hD : D.Substitutable) :
    C.substituteHull ≤ D ↔ C ≤ D :=
  (show substituteHullClosure.IsClosed D from hD).closure_le_iff

/-- The hull is the least substitutable pointwise enlargement. -/
theorem isLeast_substituteHull (C : ChoiceFunction α) :
    IsLeast {D : ChoiceFunction α | C ≤ D ∧ D.Substitutable}
      C.substituteHull :=
  ⟨⟨le_substituteHull C, substituteHull_substitutable C⟩,
    fun _ hD => substituteHull_le hD.2 hD.1⟩

/-- The hull operator is monotone for pointwise inclusion. -/
theorem monotone_substituteHull :
    Monotone (substituteHull : ChoiceFunction α → ChoiceFunction α) :=
  substituteHullClosure.monotone

/-- A second application of the hull adds nothing. -/
@[simp] theorem substituteHull_idem (C : ChoiceFunction α) :
    C.substituteHull.substituteHull = C.substituteHull :=
  substituteHullClosure.idempotent C

/-- The fixed points of the hull are exactly the substitutable choice
functions. -/
theorem substituteHull_eq_self_iff (C : ChoiceFunction α) :
    C.substituteHull = C ↔ C.Substitutable :=
  substituteHullClosure.isClosed_iff.symm

/-- The substitute hull preserves IRC, without finiteness assumptions.

For a witness menu `W`, compare it with `W ∪ Y`. Every choice from the
union that belongs to `Y` belongs to the hull at `Y`, and hence to the
retained menu `Z`. The choice from the union therefore lies in `W`,
allowing IRC for the original choice function to be applied. -/
theorem substituteHull_consistent {C : ChoiceFunction α}
    (hIRC : C.Consistent) : C.substituteHull.Consistent := by
  intro Y Z hchoice hZY
  ext x
  constructor
  · rintro ⟨hxZ, W, hZW, hxW⟩
    have hCW : C (W ∪ Y) ⊆ W := by
      intro y hy
      rcases C.choose_subset (W ∪ Y) hy with hyW | hyY
      · exact hyW
      · exact hZW
          (hchoice ⟨hyY, W ∪ Y, Set.subset_union_right, hy⟩)
    have heq : C W = C (W ∪ Y) :=
      hIRC hCW Set.subset_union_left
    refine ⟨hZY hxZ, W ∪ Y, Set.subset_union_right, ?_⟩
    rw [← heq]
    exact hxW
  · intro hx
    exact (substitutable_iff_chernoff.mp (substituteHull_substitutable C))
      hZY ⟨hx, hchoice hx⟩

/-- For an IRC choice function, the substitute hull is path independent. -/
theorem substituteHull_pathIndependent {C : ChoiceFunction α}
    (hIRC : C.Consistent) : C.substituteHull.PathIndependent :=
  (substituteHull_substitutable C).pathIndependent
    (substituteHull_consistent hIRC)

/-- Every path-independent enlargement contains the substitute hull. -/
theorem substituteHull_le_of_pathIndependent {C D : ChoiceFunction α}
    (hD : D.PathIndependent) (hCD : C ≤ D) : C.substituteHull ≤ D :=
  substituteHull_le hD.substitutable hCD

/-- An IRC choice function has a least path-independent pointwise
enlargement, namely its substitute hull. -/
theorem isLeast_pathIndependent_substituteHull {C : ChoiceFunction α}
    (hIRC : C.Consistent) :
    IsLeast {D : ChoiceFunction α | C ≤ D ∧ D.PathIndependent}
      C.substituteHull :=
  ⟨⟨le_substituteHull C, substituteHull_pathIndependent hIRC⟩,
    fun _ hD => substituteHull_le_of_pathIndependent hD.2 hD.1⟩

end ChoiceFunction

end MathEconLib.Choice
