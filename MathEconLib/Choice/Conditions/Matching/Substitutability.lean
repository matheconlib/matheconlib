import MathEconLib.Choice.Conditions.General.Substitutability

/-!
# Substitutability for matching choice

`ChoiceFunction.Substitutable` is the general arbitrary-superset condition
on a choice function. In matching with contracts, the alternatives are
contracts and the same condition is called substitutability.

This topic entrypoint imports the canonical definition and its elementary
lemmas from `MathEconLib.Choice.Conditions.General.Substitutability`.
It introduces no separate matching predicate. The weaker unilateral and
bilateral conditions, which use a map identifying each contract's matching
partner, are in `MathEconLib.Choice.Conditions.Matching.WeakSubstitutability`.
-/
