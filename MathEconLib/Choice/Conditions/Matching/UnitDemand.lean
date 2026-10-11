import MathEconLib.Choice.Conditions.General.UnitDemand

/-!
# Unit demand for matching choice

`ChoiceFunction.UnitDemand` says that at most one alternative is chosen
from each menu. In matching with contracts, this says that an agent chooses
at most one contract.

This topic entrypoint imports the canonical definition from
`MathEconLib.Choice.Conditions.General.UnitDemand`. Unit demand is distinct
from the feasibility requirement that each matching partner be represented
by at most one chosen contract: a choice can satisfy that requirement while
choosing contracts with several partners.
-/
