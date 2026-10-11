import MathEconLib.Choice.Basic

/-!
# Finite-valued choice functions

`ChoiceFunction.FiniteValued` requires every chosen set to be finite.
Menus and the universe of alternatives may be infinite. Every choice
function on a finite universe is finite-valued, and pointwise smaller
choices preserve finite-valuedness. No matching structure is required.
-/

namespace MathEconLib.Choice

universe u

variable {α : Type u}

namespace ChoiceFunction

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

end ChoiceFunction

end MathEconLib.Choice
