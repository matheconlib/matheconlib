# Lean namespace migration

MathEconLib has one Lean library with topic-based modules. Its import root and
the root namespace of its project-owned declarations are both `MathEconLib`.
An import path alone does not determine a declaration's name: for example,
`import MathEconLib.Auction.Basic` exposes the structure
`MathEconLib.Auction`, not a global `Auction`.

| Earlier name | Public name |
| --- | --- |
| `Mechanism`, `Mechanism.*` | `MathEconLib.Mechanism`, `MathEconLib.Mechanism.*` |
| `Auction`, `Auction.*` | `MathEconLib.Auction`, `MathEconLib.Auction.*` |
| `Auction.Affiliation.*` | `MathEconLib.Auction.Affiliation.*` |
| `BidderProblem`, `BidderProblem.*` | `MathEconLib.BidderProblem`, `MathEconLib.BidderProblem.*` |
| `SingleParameterProblem`, `SingleParameterProblem.*` | `MathEconLib.SingleParameterProblem`, `MathEconLib.SingleParameterProblem.*` |
| `ValueDistribution`, `ValueDistribution.*` | `MathEconLib.ValueDistribution`, `MathEconLib.ValueDistribution.*` |
| `GameTheory.*` | `MathEconLib.GameTheory.*` |
| `AllPurchase.*` | `MathEconLib.AllPurchase.*` |
| `LinearScarcityAuction`, `QuadraticCostProblem`, `LinearCostProblem`, `InteriorRegimeProblem` and their members | The same names under `MathEconLib` |
| `orderStatistics`, `OrderStatisticsSetup` and their members | The same names under `MathEconLib` |

The same `MathEconLib` prefix applies to other project-owned declarations in
these modules, including their nested topic namespaces. The source files and
`ApiStability.lean` give the exact names and pinned theorem statements.

Use fully qualified names in public API checks:

```lean
import MathEconLib

#check MathEconLib.Auction
#check MathEconLib.BidderProblem.integral_rep
#check MathEconLib.GameTheory.Game
```

Within a file, `open MathEconLib` permits shorter references such as
`Auction` and `BidderProblem.integral_rep`; it does not create old-name aliases.

## Intentional exception and compatibility

Declarations in `MathEconLib/ForMathlib/` retain their existing Mathlib-style
namespaces or global names. They are general mathematical results intended for
upstreaming, rather than economics-specific API. The import path still begins
with `MathEconLib.ForMathlib` while those declarations are in this repository.

No compatibility aliases for the former global economics names are provided.
This is a pre-public-launch API migration: downstream code should add the
`MathEconLib.` prefix or explicitly `open MathEconLib`. The mathematical
statements of the pinned theorems have not otherwise changed in this migration.
