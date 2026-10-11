import MathEconLib.Choice.Basic

/-!
# The law of aggregate demand

`ChoiceFunction.SizeMonotone` states the law of aggregate demand on finite
menus: enlarging the menu cannot reduce the number of chosen alternatives.
Only the larger menu is required to be finite. Because `Set.ncard` is zero
on infinite sets, the definition imposes no condition on infinite menus.
It requires no matching market or partner map.

On a finite alternative type, the menu-finiteness argument can be omitted.
The implication from substitutability and the law of aggregate demand to
IRC is in `MathEconLib.Choice.Conditions.General.Relationships`.

## References

Hatfield–Kojima, *Substitutes and stability for matching with contracts*,
Journal of Economic Theory 145 (2010), 1704–1723, Definition 7, p. 1718,
DOI 10.1016/j.jet.2010.01.007.

Hatfield–Kominers, *The theory of matching with contracts*, Chapter 5,
Handbook of the Economics of Matching 2 (2025), 409–487,
DOI 10.1016/bs.hesmat.2025.10.005, Definition 2.2, p. 415. Both references
use finite domains; the definition here has the scope stated above.
-/

namespace MathEconLib.Choice

universe u

variable {α : Type u}

namespace ChoiceFunction

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

end ChoiceFunction

end MathEconLib.Choice
