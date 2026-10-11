import MathEconLib.Choice.Basic

/-!
# Unit demand

`ChoiceFunction.UnitDemand` requires at most one chosen alternative from
every menu. It makes sense independently of matching, and does not require
finite menus or a finite universe of alternatives. Together with IRC, it
implies substitutability and the law of aggregate demand; those implications
are in `MathEconLib.Choice.Conditions.General.Relationships`.

## References

Hatfield–Kominers, *The theory of matching with contracts*, Chapter 5,
Handbook of the Economics of Matching 2 (2025), 409–487,
DOI 10.1016/bs.hesmat.2025.10.005, p. 413. The chapter's domains are finite;
the definition here applies to arbitrary types.
-/

namespace MathEconLib.Choice

universe u

variable {α : Type u}

namespace ChoiceFunction

variable (C : ChoiceFunction α)

/-- Unit demand: at most one alternative is ever chosen. -/
def UnitDemand : Prop :=
  ∀ Y, (C Y).Subsingleton

end ChoiceFunction

end MathEconLib.Choice
