import MathEconLib
import Lean

/-!
Compile-time checks for the intended public namespace.

The environment check covers declarations from the imported `MathEconLib` modules, including
future modules added to the generated root import. Lean's internal and reserved generated names
are excluded, and `ForMathlib` declarations retain their Mathlib-style names. The explicit checks
below also pin representative public names.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for moduleIdx in [:env.header.modules.size] do
    let moduleName := env.header.modules[moduleIdx]!.module
    if moduleName.getRoot != `MathEconLib ||
        (`MathEconLib.ForMathlib).isPrefixOf moduleName then
      continue
    for name in env.header.moduleData[moduleIdx]!.constNames do
      unless name.isInternal || isReservedName env name || name.getRoot == `MathEconLib do
        logError m!"Declaration {name} from {moduleName} must be in the MathEconLib namespace."

#check MathEconLib.Mechanism
#check MathEconLib.Mechanism.DirectMechanism
#check MathEconLib.Mechanism.Auctions.AllPurchaseSpec
#check MathEconLib.Auction
#check MathEconLib.Auction.Affiliation.Affiliated
#check MathEconLib.BidderProblem
#check MathEconLib.SingleParameterProblem
#check MathEconLib.SingleParameterProblem.revelation_principle
#check MathEconLib.ValueDistribution
#check MathEconLib.ValueDistribution.uniformInterval
#check MathEconLib.ValueDistribution.uniformOptimalPrice
#check MathEconLib.GameTheory.Game
#check MathEconLib.AllPurchase.welfare_decomposition
#check MathEconLib.LinearScarcityAuction
#check MathEconLib.QuadraticCostProblem
#check MathEconLib.LinearCostProblem
#check MathEconLib.InteriorRegimeProblem
#check MathEconLib.orderStatistics
#check MathEconLib.OrderStatisticsSetup
