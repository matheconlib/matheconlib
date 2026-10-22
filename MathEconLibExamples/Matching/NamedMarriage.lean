/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib

/-!
# A stable outcome with named participants

The enumerable two-by-two rank profile supplies preferences and a stable DA outcome.
Relabeling carries both to named applicants and positions. Stability follows from the shared
transport theorem, while the two assignments below are checked by computation.
This transports the outcome; it does not assert a correspondence of DA execution states.
-/
namespace MathEconLibExamples.Matching.NamedMarriage
open MathEconLib.Matching.MarriageMarket
inductive Applicant | ada | ben deriving DecidableEq
inductive Position | north | south deriving DecidableEq
def applicants : Fin 2 ≃ Applicant where
  toFun i := if i = 0 then .ada else .ben
  invFun a := match a with | .ada => 0 | .ben => 1
  left_inv i := by fin_cases i <;> rfl
  right_inv a := by cases a <;> rfl
def positions : Fin 2 ≃ Position where
  toFun i := if i = 0 then .north else .south
  invFun w := match w with | .north => 0 | .south => 1
  left_inv i := by fin_cases i <;> rfl
  right_inv w := by cases w <;> rfl
def profile : RankProfile 2 2 := default
def market := profile.toMarriageMarket.relabel applicants positions
def outcome := profile.toMarriageMarket.galeShapleyComputable.relabel applicants positions
theorem outcome_stable : market.IsStableMatching outcome :=
  (profile.toMarriageMarket.isStableMatching_relabel _ applicants positions).mpr
    profile.toMarriageMarket.stable_galeShapleyComputable
example : outcome .ada = some .north := by decide +kernel
example : outcome .ben = some .south := by decide +kernel
end MathEconLibExamples.Matching.NamedMarriage
