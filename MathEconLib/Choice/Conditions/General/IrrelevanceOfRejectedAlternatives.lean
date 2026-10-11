import MathEconLib.Choice.Basic

/-!
# Irrelevance of rejected alternatives

`ChoiceFunction.Consistent` states irrelevance of rejected alternatives
(IRC / consistency) in set form: deleting unchosen alternatives leaves the
chosen set unchanged. It is a condition on a general choice function and
requires no finiteness assumption. Its elementary consequence here is
idempotence. The characterization through path independence and
substitutability is in
`MathEconLib.Choice.Conditions.General.Relationships`.

When alternatives are contracts, this is irrelevance of rejected contracts;
see `MathEconLib.Choice.Conditions.Matching.IrrelevanceOfRejectedContracts`.

## References

Aygün–Sönmez (2013); Alkan–Gale consistency.

Hatfield–Kominers, *The theory of matching with contracts*, Chapter 5,
Handbook of the Economics of Matching 2 (2025), 409–487,
DOI 10.1016/bs.hesmat.2025.10.005, p. 413 and footnote 10, for the standing
IRC assumption. The chapter's domains are finite; the definition here is not.
-/

namespace MathEconLib.Choice

universe u

variable {α : Type u}

namespace ChoiceFunction

variable (C : ChoiceFunction α)

/-- Irrelevance of rejected alternatives (IRC / consistency), set form. -/
def Consistent : Prop :=
  ∀ ⦃Y Z : Set α⦄, C Y ⊆ Z → Z ⊆ Y → C Z = C Y

variable {C}

/-- Choosing again from the chosen alternatives does not change an IRC choice. -/
theorem Consistent.idempotent (hcons : C.Consistent) (Y : Set α) :
    C (C Y) = C Y :=
  hcons Set.Subset.rfl (C.choose_subset Y)

end ChoiceFunction

end MathEconLib.Choice
