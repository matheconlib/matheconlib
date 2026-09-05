/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Mechanism.Core.Mechanism

/-!
# Mechanisms induced by report maps

Each agent's report can be mapped to an action in a mechanism. The induced mechanism assigns each
report profile the outcome and transfers of the resulting action profile. When reports are types,
these maps are strategies, and the induced mechanism is a direct mechanism on the type spaces.

## Main definitions

* `Auctionlib.Mechanism.Mechanism.comap`: the mechanism induced by maps from reports to actions.

## Main statements

* `Auctionlib.Mechanism.Mechanism.comap_id`: identity report maps induce the original mechanism.
* `Auctionlib.Mechanism.Mechanism.comap_comp`: successive report maps compose pointwise.

## Tags

mechanism design, direct mechanisms, strategy profiles, report maps
-/

@[expose] public section

-- Operations on the carrier retain the enclosing `Auctionlib.Mechanism` namespace.
set_option linter.dupNamespace false

universe uI uA uB uC uO

namespace Auctionlib.Mechanism.Mechanism

variable {I : Type uI} {A : I → Type uA} {B : I → Type uB} {C : I → Type uC}
  {O : Type uO} (M : Mechanism I A O)

/-- The mechanism induced from `M` by maps `σ i` from new reports or actions in `B i` to the
original actions in `A i`. At a profile `b`, it gives the outcome and transfers that `M` assigns to
the action profile `fun i => σ i (b i)`. If `B i` is agent `i`'s type space, `σ` is a strategy
profile and `M.comap σ` is the direct mechanism it induces. -/
def comap (σ : ∀ i, B i → A i) : Mechanism I B O where
  outcome b := M.outcome (fun i => σ i (b i))
  transfer i b := M.transfer i (fun j => σ j (b j))

/-- The outcome at a report profile is `M`'s outcome at the action profile prescribed by `σ`. -/
@[simp] theorem outcome_comap (σ : ∀ i, B i → A i) (b : Profile B) :
    (M.comap σ).outcome b = M.outcome (fun i => σ i (b i)) := rfl

/-- Agent `i`'s transfer at a report profile is their transfer in `M` at the action profile
prescribed by `σ`. -/
@[simp] theorem transfer_comap (σ : ∀ i, B i → A i) (i : I) (b : Profile B) :
    (M.comap σ).transfer i b = M.transfer i (fun j => σ j (b j)) := rfl

/-- Agent `i`'s payment at a report profile is their payment in `M` at the action profile
prescribed by `σ`. -/
@[simp] theorem payment_comap (σ : ∀ i, B i → A i) (i : I) (b : Profile B) :
    (M.comap σ).payment i b = M.payment i (fun j => σ j (b j)) := rfl

/-- With finitely many agents, revenue at a report profile equals `M`'s revenue at the action
profile prescribed by `σ`. -/
@[simp] theorem revenue_comap [Fintype I] (σ : ∀ i, B i → A i) (b : Profile B) :
    (M.comap σ).revenue b = M.revenue (fun i => σ i (b i)) := rfl

/-- Identity report maps induce the original mechanism. -/
@[simp] theorem comap_id : M.comap (fun _ => id) = M := rfl

/-- Successive changes of input representation compose pointwise. -/
theorem comap_comp (σ : ∀ i, B i → A i) (τ : ∀ i, C i → B i) :
    (M.comap σ).comap τ = M.comap (fun i => σ i ∘ τ i) := rfl

end Auctionlib.Mechanism.Mechanism

end
