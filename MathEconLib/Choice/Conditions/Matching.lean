import MathEconLib.Choice.Conditions.Matching.Completion
import MathEconLib.Choice.Conditions.Matching.FiniteValued
import MathEconLib.Choice.Conditions.Matching.IrrelevanceOfRejectedContracts
import MathEconLib.Choice.Conditions.Matching.LawOfAggregateDemand
import MathEconLib.Choice.Conditions.Matching.PathIndependence
import MathEconLib.Choice.Conditions.Matching.Preferences
import MathEconLib.Choice.Conditions.Matching.Relationships
import MathEconLib.Choice.Conditions.Matching.Substitutability
import MathEconLib.Choice.Conditions.Matching.UnitDemand
import MathEconLib.Choice.Conditions.Matching.WeakSubstitutability

/-!
# Choice conditions in matching

This umbrella organizes choice conditions by their terminology and use in
matching with contracts. The conditions remain in `MathEconLib.Choice`:
no matching market or specified market sides are required.

## Topic modules

* `Matching.Substitutability` — the general substitutability condition for
  choice over contracts.
* `Matching.WeakSubstitutability` — unilateral and bilateral substitutability,
  using a map identifying the matching partner associated with each contract.
* `Matching.IrrelevanceOfRejectedContracts` — irrelevance of rejected contracts
  (IRC), the matching interpretation of general set-form consistency.
* `Matching.LawOfAggregateDemand` — the law of aggregate demand on finite menus.
* `Matching.UnitDemand` — at most one chosen contract from each menu.
* `Matching.FiniteValued` — finite chosen sets, allowing infinite menus.
* `Matching.PathIndependence` — path independence for choice over contracts.
* `Matching.Completion` — completion, substitutable completability, and the
  stronger existence of a completion satisfying both substitutability and IRC.
* `Matching.Relationships` — implications involving weak substitutability,
  completion, feasibility, and the substitute hull.
* `Matching.Preferences` — completion results for preference-induced choice.

Substitutability, IRC, the law of aggregate demand, unit demand,
finite-valuedness, and path independence are defined once in the corresponding
`MathEconLib.Choice.Conditions.General` topic modules. Their matching
entrypoints import those same definitions and explain their interpretation
for contracts. General implications among them are in
`MathEconLib.Choice.Conditions.General.Relationships`.

Weak substitutability and completion additionally use a map identifying the
agent associated with each alternative. They do not require the full market
structure supplied later by `MathEconLib.Matching.Contracts`.
-/
