/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

import MathEconLib.SingleParameter
import MathEconLib.Mechanism

/-!
# Public IC and welfare bridges

Import only the two public umbrellas. Examples and implementation imports cannot supply a
missing export. The signatures keep arbitrary action and outcome spaces and dependent types.
-/

open MathEconLib MathEconLib.Choice MathEconLib.SingleParameterProblem
open MathEconLib.Mechanism

example {Action : Type*} (P : SingleParameterProblem Action) (S : Set Action) :
    P.HasUniversalIC S ↔ ∀ v ∈ P.typeInterval,
      P.strategy v ∈ maximizers (Preorder.lift (P.payoff v)) S :=
  hasUniversalIC_iff_mem_maximizers P S

example {Action : Type*} {P : SingleParameterProblem Action} {S : Set Action}
    (h : P.HasUniversalIC S) (s : ℝ → Action)
    (hs : ∀ v ∈ P.typeInterval, s v ∈ S)
    (heq : ∀ v ∈ P.typeInterval, P.payoff v (s v) = P.payoff v (P.strategy v)) :
    (P.withStrategy s).HasUniversalIC S :=
  h.withStrategy s hs heq

example {I : Type*} {T : I → Type*} {O : Type*} [Fintype I]
    (E : QuasilinearEnvironment I T O) (M : DirectMechanism I T O) :
    DirectMechanism.IsEfficient E M ↔ ∀ θ,
      M.outcome θ ∈ maximizers (Preorder.lift (E.totalValue θ)) Set.univ :=
  DirectMechanism.isEfficient_iff_mem_maximizers E M
