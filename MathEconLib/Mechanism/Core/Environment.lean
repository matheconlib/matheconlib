/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.Mechanism.Core.Mechanism

/-!
# Quasilinear environments

`QuasilinearEnvironment.value` gives each agent's value for an outcome at the full true type
profile, allowing values to depend on other agents' types. `IsPrivateValues` requires each agent's
value to depend only on that agent's own type and the outcome; `ofPrivate` constructs an
environment from such valuations.

`utility` adds the signed transfer received from a mechanism to the agent's value for the chosen
outcome. For finitely many agents, `totalValue` sums their values for an outcome, and `welfareExcl`
sums the values of all agents except a specified agent. These welfare quantities exclude transfers.

## Main definitions

* `QuasilinearEnvironment`: agents' valuations over true type profiles and outcomes.
* `QuasilinearEnvironment.IsPrivateValues`: each agent's value depends only on its own type and the
  outcome.
* `QuasilinearEnvironment.ofPrivate`: an environment specified by own-type valuation functions.
* `QuasilinearEnvironment.utility`: value of the chosen outcome plus the signed transfer received.
* `QuasilinearEnvironment.totalValue`: the sum of all agents' values for an outcome.
* `QuasilinearEnvironment.welfareExcl`: the sum of all other agents' values for an outcome.

## Main statements

* `QuasilinearEnvironment.isPrivateValues_ofPrivate`: own-type valuations satisfy private values.
* `QuasilinearEnvironment.value_add_welfareExcl`: social value splits into one agent's value and
  everyone else's value.
* `QuasilinearEnvironment.welfareExcl_update`: under private values, changing an agent's type
  leaves everyone else's total value unchanged at a fixed outcome.

## Tags

mechanism design, quasilinear utility, interdependent values, private values, social welfare
-/

@[expose] public section

universe uI uΘ uA uO

namespace MathEconLib.Mechanism

/-- A quasilinear valuation environment for agents `I`, where `Θ i` is agent `i`'s type space and
`O` is the outcome space.

`value i θ o` is agent `i`'s value for outcome `o` at the full true type profile `θ`. Values may
depend on other agents' types. Quasilinear utility adds the signed transfer received to this
value.

The environment specifies valuations only; it does not include a mechanism or a distribution over
types. -/
structure QuasilinearEnvironment (I : Type uI) (Θ : I → Type uΘ) (O : Type uO) where
  /-- `value i θ o` is agent `i`'s value for outcome `o` at the full true type profile `θ`. -/
  value : (i : I) → Profile Θ → O → ℝ

namespace QuasilinearEnvironment

variable {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {O : Type uO}

/-- Every agent's value is unchanged when other agents' types change, holding that agent's own type
and the outcome fixed. -/
def IsPrivateValues (E : QuasilinearEnvironment I Θ O) : Prop :=
  ∀ i θ θ', θ i = θ' i → E.value i θ = E.value i θ'

/-- Construct an environment from agents' own-type valuation functions. -/
def ofPrivate (v : (i : I) → Θ i → O → ℝ) : QuasilinearEnvironment I Θ O where
  value i θ := v i (θ i)

/-- In the environment specified by `v`, agent `i` values outcome `o` at `v i (θ i) o`. -/
@[simp] theorem value_ofPrivate (v : (i : I) → Θ i → O → ℝ)
    (i : I) (θ : Profile Θ) (o : O) :
    (ofPrivate v).value i θ o = v i (θ i) o := rfl

/-- Valuations specified as functions of each agent's own type satisfy private values. -/
@[simp] theorem isPrivateValues_ofPrivate (v : (i : I) → Θ i → O → ℝ) :
    (ofPrivate v).IsPrivateValues := by
  intro i θ θ' h
  change v i (θ i) = v i (θ' i)
  rw [h]

variable (E : QuasilinearEnvironment I Θ O)

/-- Agent `i`'s utility at true type profile `θ` when action profile `a` is played in mechanism
`M`. The outcome and signed transfer received are determined by `a`; the value of that outcome is
evaluated at `θ`. -/
def utility (M : Mechanism I A O) (i : I) (θ : Profile Θ) (a : Profile A) : ℝ :=
  E.value i θ (M.outcome a) + M.transfer i a

/-- Utility is the value of the chosen outcome at the true type profile plus the signed transfer
received. -/
@[simp] theorem utility_eq_value_add_transfer (M : Mechanism I A O)
    (i : I) (θ : Profile Θ) (a : Profile A) :
    E.utility M i θ a = E.value i θ (M.outcome a) + M.transfer i a := rfl

/-- Utility is value net of the payment charged to the agent. -/
theorem utility_eq_value_sub_payment (M : Mechanism I A O)
    (i : I) (θ : Profile Θ) (a : Profile A) :
    E.utility M i θ a = E.value i θ (M.outcome a) - M.payment i a := by
  simp [utility, Mechanism.payment]

/-- Utilitarian social value of an outcome at the true type profile. -/
def totalValue [Fintype I] (θ : Profile Θ) (o : O) : ℝ := ∑ i, E.value i θ o

/-- Social value is the sum of agents' values for the outcome at the true type profile. -/
@[simp] theorem totalValue_eq_sum [Fintype I] (θ : Profile Θ) (o : O) :
    E.totalValue θ o = ∑ i, E.value i θ o := rfl

/-- Total value of an outcome excluding agent `i`. -/
def welfareExcl [Fintype I] [DecidableEq I] (i : I) (θ : Profile Θ) (o : O) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, E.value j θ o

/-- Welfare excluding agent `i` is the sum of the other agents' values for the outcome. -/
@[simp] theorem welfareExcl_eq_sum_erase [Fintype I] [DecidableEq I]
    (i : I) (θ : Profile Θ) (o : O) :
    E.welfareExcl i θ o = ∑ j ∈ Finset.univ.erase i, E.value j θ o := rfl

/-- Social value splits into agent `i`'s value and the value accruing to everyone else. -/
theorem value_add_welfareExcl [Fintype I] [DecidableEq I]
    (i : I) (θ : Profile Θ) (o : O) :
    E.value i θ o + E.welfareExcl i θ o = E.totalValue θ o :=
  Finset.add_sum_erase Finset.univ (fun j => E.value j θ o) (Finset.mem_univ i)

/-- Under private values, changing `i`'s type does not change others' total value at a fixed
outcome. -/
theorem welfareExcl_update [Fintype I] [DecidableEq I] (hpriv : E.IsPrivateValues)
    (i : I) (θ : Profile Θ) (x : Θ i) (o : O) :
    E.welfareExcl i (Function.update θ i x) o = E.welfareExcl i θ o := by
  refine Finset.sum_congr rfl fun j hj => ?_
  exact congrFun (hpriv j _ _ (Function.update_of_ne (Finset.ne_of_mem_erase hj) x θ)) o

end QuasilinearEnvironment

end MathEconLib.Mechanism

end
