import MathEconLib.Choice.Conditions.General.FiniteValued

/-!
# Finite chosen sets for matching choice

`ChoiceFunction.FiniteValued` says that every chosen set is finite. In
matching with contracts, it requires finite sets of chosen contracts while
allowing both the menus and the contract type to be infinite.

This topic entrypoint imports the canonical definition and its elementary
lemmas from `MathEconLib.Choice.Conditions.General.FiniteValued`.
Completion results using this hypothesis are in
`MathEconLib.Choice.Conditions.Matching.Relationships`.
-/
