/-
Copyright (c) 2026 Ayan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayan
-/
module

import MathEconLibExamples.Matching.Improvements

/-! Regression checks reusing the fixed-menu choice examples. Generic public-import checks
live in `MathEconLibTest.Matching.PublicImport`. -/

open MathEconLib.Matching MarriageMarket
open MathEconLibExamples.Matching.Improvements

/-! A rival becomes newly acceptable and the selection is preserved. -/

example : ¬ (market NewlyAcceptable.oldOrder).AcceptableW () false ∧
    (market NewlyAcceptable.newOrder).AcceptableW () false ∧
    (true, ()) ∈ (market NewlyAcceptable.newOrder).inducedChoiceW () Set.univ :=
  ⟨NewlyAcceptable.not_acceptableW_old, NewlyAcceptable.acceptableW_new,
    NewlyAcceptable.mem_inducedChoiceW_new⟩

example : (market NewlyAcceptable.newOrder).bestW () Set.univ = some true :=
  NewlyAcceptable.bestW_new

/-! The first clause cannot be dropped from the fixed-menu result. -/

example : (true, ()) ∈ (market BelowOutside.oldOrder).inducedChoiceW () Set.univ ∧
    (true, ()) ∉ (market BelowOutside.newOrder).inducedChoiceW () Set.univ :=
  ⟨BelowOutside.mem_inducedChoiceW_old, BelowOutside.not_mem_inducedChoiceW_new⟩

example : (true, ()) ∈ (market Overtaken.oldOrder).inducedChoiceW () Set.univ ∧
    (true, ()) ∉ (market Overtaken.newOrder).inducedChoiceW () Set.univ :=
  ⟨Overtaken.mem_inducedChoiceW_old, Overtaken.not_mem_inducedChoiceW_new⟩
