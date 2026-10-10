import MathEconLib.Choice
import Lean

/-!
Public choice interfaces must remain usable without importing matching theory.
The environment check catches a transitive dependency on the matching layer.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for entry in env.header.modules do
    if (`MathEconLib.Matching).isPrefixOf entry.module then
      logError m!"Choice imports the matching layer through {entry.module}."

namespace MathEconLibTest.Choice

open MathEconLib.Choice

#check ChoiceFunction
#check ChoiceFunction.Substitutable
#check ChoiceFunction.Consistent

example {α : Type*} (C : ChoiceFunction α) :
    ChoiceFunction.substituteHullClosure C = C.substituteHull := rfl

example {α : Type*} (C : ChoiceFunction α) :
    ChoiceFunction.substituteHullClosure.IsClosed C ↔ C.Substitutable := Iff.rfl

end MathEconLibTest.Choice
