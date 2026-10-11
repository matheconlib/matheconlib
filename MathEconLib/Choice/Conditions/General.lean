import MathEconLib.Choice.Conditions.General.FiniteValued
import MathEconLib.Choice.Conditions.General.IrrelevanceOfRejectedAlternatives
import MathEconLib.Choice.Conditions.General.LawOfAggregateDemand
import MathEconLib.Choice.Conditions.General.PathIndependence
import MathEconLib.Choice.Conditions.General.Relationships
import MathEconLib.Choice.Conditions.General.Substitutability
import MathEconLib.Choice.Conditions.General.UnitDemand

/-!
# General conditions on choice functions

These optional conditions use only a choice function's choices and menus.
They are independent of matching markets, agents, and partner maps.
The current development is motivated by matching with contracts, but that
application does not restrict their domains.

## Topic modules

* `General.Substitutability` — arbitrary-superset substitutability, rejection
  monotonicity, and the Chernoff condition.
* `General.IrrelevanceOfRejectedAlternatives` — set-form consistency (IRC).
* `General.LawOfAggregateDemand` — the law of aggregate demand on finite menus.
* `General.UnitDemand` — at most one chosen alternative from each menu.
* `General.FiniteValued` — finite chosen sets, allowing infinite menus.
* `General.PathIndependence` — path independence and its union identities.
* `General.Relationships` — implications involving several conditions.

`MathEconLib.Choice.Conditions.Matching` organizes matching terminology and
conditions such as weak substitutability and completion that require a map
identifying the agent associated with an alternative. Its topic entrypoints
for the general conditions import the same definitions used here.

## References

Hatfield–Kojima, *Substitutes and stability for matching with contracts*,
Journal of Economic Theory 145 (2010), 1704–1723,
Definitions 2 and 7 (pp. 1708 and 1718), DOI 10.1016/j.jet.2010.01.007.

Hatfield–Kominers, *The theory of matching with contracts*, Chapter 5,
Handbook of the Economics of Matching 2 (2025), 409–487,
DOI 10.1016/bs.hesmat.2025.10.005. See p. 413 and footnote 10 for the
standing IRC assumption; Definition 2.1 and the following rejection-function
discussion, p. 414, for substitutability; Definition 2.2, p. 415, for
the law of aggregate demand; and footnote 16, p. 414, for path independence.
Unit demand is discussed on p. 413. These references use finite domains;
the topic modules state the precise scope of each definition and theorem.

Further background: Aizerman–Malishevski (1981); Alkan–Gale consistency;
Aygün–Sönmez (2013); Chambers–Yenmez (2017); Plott (1973).
-/
