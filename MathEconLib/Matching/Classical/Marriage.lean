import MathEconLib.Matching.Classical.Marriage.GeneralizedDA
import MathEconLib.Matching.Classical.Marriage.LoneWolf
import MathEconLib.Matching.Classical.StableOrder

/-!
# The classical marriage market

Public entry point for the marriage model, realized as an instance
in the matching with contracts framework. Men are sellers, women are buyers,
and contracts are pairs `M × W`. Preferences are orders on optional partners,
with `none` representing the outside option. No global preference order is
installed on bare `PEquiv`.

The components separate basic economic definitions and direct classical facts,
generic induced choice, contracts translation, the symmetric extrema,
generalized DA convergence, lone wolf results, and the stable-matching lattice.
`Classical.DeferredAcceptance` adds
the direct proposal algorithm and its comparison with generalized DA;
`Classical.DeferredAcceptanceFinite` supplies executable algorithms.
-/

namespace MathEconLib.Matching

end MathEconLib.Matching
