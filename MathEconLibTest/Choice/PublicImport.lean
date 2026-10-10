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

example {α : Type*} (C : ChoiceFunction α) :
    ChoiceFunction.substituteHullClosure C = C.substituteHull := rfl

example {α : Type*} (C : ChoiceFunction α) :
    ChoiceFunction.substituteHullClosure.IsClosed C ↔ C.Substitutable := Iff.rfl

example {α β : Type*} (e : α ↪ β) :
    ChoiceFunction α ↪o ChoiceFunction β := ChoiceFunction.mapOrderEmbedding e

example {α : Type*} [DecidableEq α] (pref : LinearOrder (Option α)) (A : Finset α) :
    letI := pref
    IsGreatest (ChoiceFunction.optionMenu A : Set (Option α))
      (ChoiceFunction.bestOption pref A) :=
  ChoiceFunction.isGreatest_bestOption pref A

end MathEconLibTest.Choice
