# Lean namespace migration

MathEconLib has one Lean library with topic-based modules. Its import root and
the root namespace of its project-owned declarations are both `MathEconLib`.
An import path alone does not determine a declaration's name: for example,
`import MathEconLib.Auction.Basic` exposes the structure
`MathEconLib.Auction`, not a global `Auction`.

| Earlier name | Public name |
| --- | --- |
| `Auctionlib.Mechanism`, `Auctionlib.Mechanism.*` | `MathEconLib.Mechanism`, `MathEconLib.Mechanism.*` |
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

The package/import migration in #90 already moves the mechanism core from its
existing `Auctionlib` namespace to `MathEconLib`. This follow-up moves the
remaining global economics declarations, including the revelation principle
and interval-uniform pricing results, under that same root. It retains the
current mechanism's agent, action, and outcome parameters: `Mechanism I A O`.

Use fully qualified names in public API checks:

```lean
import MathEconLib

#check MathEconLib.Auction
#check MathEconLib.BidderProblem.integral_rep
#check MathEconLib.GameTheory.Game
```

Within a file, `open MathEconLib` permits shorter references such as
`Auction` and `BidderProblem.integral_rep`; it does not create old-name aliases.

`MathEconLibTest/Namespace.lean` checks the compiled environment for declarations
from every module imported by the generated `MathEconLib` root. Declarations from
project modules must use the `MathEconLib` namespace, except for Lean's internal
and reserved generated names and the `ForMathlib` modules described below. The
default `lake build` and CI run this check, so a new imported file that omits the
namespace wrapper fails the build.
CI also checks the namespace target after regenerating root imports, before
committing any generated changes.

## Intentional exception and compatibility

Declarations in `MathEconLib/ForMathlib/` retain their existing Mathlib-style
namespaces or global names. They are general mathematical results that may be
suitable for voluntary upstream contribution. The import path still begins
with `MathEconLib.ForMathlib` while those declarations are in this repository.

No compatibility aliases for the former global economics names are provided.
This is a pre-public-launch API migration: downstream code should add the
`MathEconLib.` prefix or explicitly `open MathEconLib`. The mathematical
statements of the pinned theorems have not otherwise changed in this migration.
