/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

import MathEconLib
import MathEconLibExamples.Matching.DistributiveMarriage

/-! Public import and concrete regression checks for the distributive lattice. -/

open MathEconLib.Matching MarriageMarket
open MathEconLibExamples.Matching.DistributiveMarriage

example : (womenBest ⊔ menBest).matching 0 = some 0 := join_first_man

example : (womenBest ⊓ menBest).matching 0 = some 1 := meet_first_man

example : StableMatching.lowerSetSupIrred market womenBest ≠
    StableMatching.lowerSetSupIrred market menBest := represented_outcomes_ne

example : (StableMatching.lowerSetSupIrred market).symm
    (StableMatching.lowerSetSupIrred market womenBest) = womenBest := womenBest_roundtrip
