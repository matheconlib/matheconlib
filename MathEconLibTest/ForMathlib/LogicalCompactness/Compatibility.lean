/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLib.ForMathlib.LogicalCompactness

/-!
# Independent logical-compactness API pins

The finite-valued, Boolean, and scaling contracts are checked through the logical
compactness module alone, without any economic application or worked example.
Variable and constraint types remain arbitrary, and the finite value type need
not be nonempty: finite feasibility includes the empty subfamily.
-/

set_option autoImplicit false
set_option linter.privateModule false

open MathEconLib.LogicalCompactness

universe u v w z

example {Value : Type z} [Finite Value]
    {V : Type u} {I : Type v} {Key : I → Type w} [∀ i, Finite (Key i)]
    (vars : (i : I) → Key i → V)
    (allowed : (i : I) → (Key i → Value) → Prop)
    (hfinite : ∀ s : Finset I, ∃ a : V → Value,
      ∀ i ∈ s, allowed i (fun k => a (vars i k))) :
    ∃ a : V → Value, ∀ i, allowed i (fun k => a (vars i k)) :=
  finite_local_compactness vars allowed hfinite

example {Value : Type z} [Finite Value]
    {V : Type u} {I : Type v} {Key : I → Type w} [∀ i, Finite (Key i)]
    (vars : (i : I) → Key i → V)
    (allowed : (i : I) → (Key i → Value) → Prop) :
    (∃ a : V → Value, ∀ i, allowed i (fun k => a (vars i k))) ↔
      ∀ s : Finset I, ∃ a : V → Value,
        ∀ i ∈ s, allowed i (fun k => a (vars i k)) :=
  finite_local_compactness_iff vars allowed

example {V : Type u} {I : Type v} {Key : I → Type w} [∀ i, Finite (Key i)]
    (vars : (i : I) → Key i → V)
    (allowed : (i : I) → (Key i → Bool) → Prop)
    (hfinite : ∀ s : Finset I, ∃ a : V → Bool,
      ∀ i ∈ s, allowed i (fun k => a (vars i k))) :
    ∃ a : V → Bool, ∀ i, allowed i (fun k => a (vars i k)) :=
  finite_local_bool_compactness vars allowed hfinite

example {V : Type u} {I : Type v} {Key : I → Type w} [∀ i, Finite (Key i)]
    (vars : (i : I) → Key i → V)
    (allowed : (i : I) → (Key i → Bool) → Prop) :
    (∃ a : V → Bool, ∀ i, allowed i (fun k => a (vars i k))) ↔
      ∀ s : Finset I, ∃ a : V → Bool,
        ∀ i ∈ s, allowed i (fun k => a (vars i k)) :=
  finite_local_bool_compactness_iff vars allowed

example {Problem : Type*} {V : Type u} {I : Type v} {Key : I → Type w}
    [∀ i, Finite (Key i)]
    (solution : Problem → Prop)
    (vars : (i : I) → Key i → V)
    (allowed : Problem → (i : I) → (Key i → Bool) → Prop)
    (description : ∀ p, solution p ↔
      ∃ a : V → Bool, ∀ i, allowed p i (fun k => a (vars i k)))
    (p : Problem)
    (finite_subset_property : ∀ s : Finset I, ∃ q,
      solution q ∧ ∀ a : V → Bool,
        (∀ i, allowed q i (fun k => a (vars i k))) →
          ∀ i ∈ s, allowed p i (fun k => a (vars i k))) :
    solution p :=
  scaling_of_finite_local_description solution vars allowed description p finite_subset_property

#print axioms finite_local_compactness
#print axioms finite_local_compactness_iff
#print axioms finite_local_bool_compactness
#print axioms finite_local_bool_compactness_iff
#print axioms scaling_of_finite_local_description
