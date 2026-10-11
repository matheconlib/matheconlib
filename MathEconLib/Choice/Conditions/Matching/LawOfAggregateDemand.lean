import MathEconLib.Choice.Conditions.General.LawOfAggregateDemand

/-!
# The law of aggregate demand for matching choice

`ChoiceFunction.SizeMonotone` states the law of aggregate demand on finite
menus. For contracts, enlarging a finite menu cannot decrease the number of
chosen contracts. The underlying contract type need not be finite.

This topic entrypoint imports the canonical definition and its cardinality
lemmas from `MathEconLib.Choice.Conditions.General.LawOfAggregateDemand`.
It introduces no separate matching predicate. Implications involving the law
of aggregate demand and other general choice conditions are in
`MathEconLib.Choice.Conditions.General.Relationships`.
-/
