import MathEconLib

/-!
Client checks through the full public root, including both executable
algorithms and their optimal matching endpoints.
-/

namespace MathEconLibTest.Matching

open MathEconLib.Choice MathEconLib.Matching

#check MathEconLib.Auction
#check MathEconLib.Choice.ChoiceFunction
#check MathEconLib.Matching.Market
#check MathEconLib.Matching.MarriageMarket

section Marriage

variable {M W : Type*} (mkt : MarriageMarket M W)

variable [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

example : mkt.galeShapleyComputable = mkt.manOptimalMatching :=
  mkt.galeShapleyComputable_eq_manOptimalMatching

example : mkt.womanGaleShapleyComputable = mkt.womanOptimalMatching :=
  mkt.womanGaleShapleyComputable_eq_womanOptimalMatching

example : mkt.IsStableMatching mkt.galeShapleyComputable :=
  mkt.stable_galeShapleyComputable_via_contracts

example : mkt.IsStableMatching mkt.womanGaleShapleyComputable :=
  mkt.stable_womanGaleShapleyComputable_via_contracts

end Marriage

end MathEconLibTest.Matching
