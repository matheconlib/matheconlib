/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLibExamples.GeneralEquilibrium.PureExchange.ZeroIncome

/-!
# Zero-income demand regression

Import the canonical counterexample and retain the exact parameter range, zero-wealth
boundary, and failure of the graph to be closed on normalized nonnegative prices.
-/

set_option linter.privateModule false

open MathEconLib.RevealedPreference MathEconLib.GeneralEquilibrium.PureExchange
open MathEconLib.GeneralEquilibrium.PureExchange.Examples.ZeroIncome

example {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    endowment ∈ Internal.cappedDemand Examples.Linear.sumPreference endowment cap (price ε) :=
  endowment_mem_cappedDemand hε hε'

example : dot (price 0) endowment = 0 ∧
    endowment ∉ Internal.cappedDemand Examples.Linear.sumPreference endowment cap (price 0) :=
  ⟨wealth 0, endowment_not_mem_cappedDemand_zero⟩

example : ¬ ∀ k, 0 < endowment k := endowment_not_strictly_positive

example : ¬ IsClosed {z : Bundle 2 × Bundle 2 |
    z.1 ∈ Internal.priceSimplex ∧
      z.2 ∈ Internal.cappedDemand Examples.Linear.sumPreference endowment cap z.1} :=
  cappedDemand_graph_not_isClosed
