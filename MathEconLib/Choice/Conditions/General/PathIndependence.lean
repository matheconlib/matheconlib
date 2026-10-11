import MathEconLib.Choice.Basic

/-!
# Path independence of choice functions

`ChoiceFunction.PathIndependent` says that choosing from part of a menu
before adding the remaining alternatives does not change the final choice.
The definition and its elementary union identities here apply to arbitrary
types. They require the path-independence hypothesis and are not properties
of every choice function.

Path independence is equivalent to substitutability and IRC; the equivalence
is in `MathEconLib.Choice.Conditions.General.Relationships`.

## References

Plott (1973); Aizerman–Malishevski (1981); Chambers–Yenmez (2017).

Hatfield–Kominers, *The theory of matching with contracts*, Chapter 5,
Handbook of the Economics of Matching 2 (2025), 409–487,
DOI 10.1016/bs.hesmat.2025.10.005, footnote 16, p. 414. The chapter's domains
are finite; the definition here applies to arbitrary types.
-/

namespace MathEconLib.Choice

universe u

variable {α : Type u}

namespace ChoiceFunction

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

end ChoiceFunction

end MathEconLib.Choice
