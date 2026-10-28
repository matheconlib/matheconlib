/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/

module

import MathEconLib.Preferences

/-!
# Public Preference Interfaces

These compile-time checks pin the signatures of the preference API through the umbrella import
`MathEconLib.Preferences`, and print the axioms of each public theorem.

## Checks

* Preferences — the `IsPreorder` instance, the notation, conversions to and from preorders,
  `Preference.comap` and its laws, and the strict-preference lemmas.
* Complete preferences — coercion, totality, the constructors from total preorders and linear
  orders, `CompletePreference.comap`, `CompletePreference.toLinearOrder`, and trichotomy.
* Ordinal utility — `Preference.IsRepresentedBy`, `Preference.ofUtility`,
  `CompletePreference.ofUtility`, and the characterization of greatest alternatives by utility
  maximization.
* Finite alternatives — natural-number representations of complete preferences.

## Tags

preference, public api, ordinal utility, finite representation
-/

set_option linter.privateModule false

namespace MathEconLib.Preferences.Tests

open scoped MathEconLib.Preferences

section Preference

variable {X Y Z : Type*} (R : Preference X) (S : Preference Y) (T : Preference Z)

example : IsPreorder X R.le := inferInstance

example (x y : X) : x ≺[R] y ↔ x ≼[R] y ∧ ¬y ≼[R] x := Iff.rfl

example (x y : X) : x ~[R] y ↔ x ≼[R] y ∧ y ≼[R] x := Iff.rfl

example {R S : Preference X} (h : ∀ x y, x ≼[R] y ↔ x ≼[S] y) : R = S :=
  Preference.ext h

example (x : X) : x ≼[R] x := R.le_refl x

example {x : X} : x ≼[R] x := R.le_rfl

example {x y z : X} (hxy : x ≼[R] y) (hyz : y ≼[R] z) : x ≼[R] z :=
  R.le_trans hxy hyz

example : Preorder X := R.toPreorder

example (x y : X) : R.toPreorder.le x y ↔ x ≼[R] y := R.toPreorder_le x y

example (x y : X) : R.toPreorder.lt x y ↔ x ≺[R] y := R.toPreorder_lt x y

example (p : Preorder X) : Preference X := Preference.ofPreorder p

example (p : Preorder X) : (Preference.ofPreorder p).toPreorder = p :=
  Preference.toPreorder_ofPreorder p

example : Preference.ofPreorder R.toPreorder = R := R.ofPreorder_toPreorder

example (f : X → Y) : Preference X := S.comap f

example (f : X → Y) (x y : X) : x ≼[S.comap f] y ↔ f x ≼[S] f y :=
  S.comap_le f x y

example : R.comap id = R := R.comap_id

example (f : Y → Z) (g : X → Y) : (T.comap f).comap g = T.comap (f ∘ g) :=
  T.comap_comp f g

example (f : X → Y) : (S.comap f).toPreorder = @Preorder.lift X Y S.toPreorder f :=
  S.toPreorder_comap f

example {f : X → Y} (hf : Function.Injective f) [Std.Antisymm S.le] :
    Std.Antisymm (S.comap f).le := S.antisymm_comap hf

example (x : X) : ¬x ≺[R] x := R.lt_irrefl x

example {x y : X} (hxy : x ≺[R] y) : ¬y ≺[R] x := R.lt_asymm hxy

example {x y z : X} (hxy : x ≺[R] y) (hyz : y ≺[R] z) : x ≺[R] z :=
  R.lt_trans hxy hyz

example {x y z : X} (hxy : x ≼[R] y) (hyz : y ≺[R] z) : x ≺[R] z :=
  R.lt_of_le_of_lt hxy hyz

example {x y z : X} (hxy : x ≺[R] y) (hyz : y ≼[R] z) : x ≺[R] z :=
  R.lt_of_lt_of_le hxy hyz

example {x y : X} (hxy : x ≺[R] y) : x ≼[R] y := R.le_of_lt hxy

end Preference

section CompletePreference

variable {X Y : Type*} (R : CompletePreference X)

example : Preference X := R

example : Std.Total R.le := inferInstance

example : IsPreorder X R.le := inferInstance

example (x y : X) : x ≼[R] y ∨ y ≼[R] x := R.total x y

example (p : Preorder X) (h : Std.Total p.le) : CompletePreference X :=
  CompletePreference.ofPreorder p h

example (L : LinearOrder X) : CompletePreference X := CompletePreference.ofLinearOrder L

example (p : Preorder X) (h : Std.Total p.le) :
    (CompletePreference.ofPreorder p h).toPreference.toPreorder = p :=
  CompletePreference.toPreorder_ofPreorder p h

example : CompletePreference.ofPreorder R.toPreference.toPreorder R.isTotal = R :=
  R.ofPreorder_toPreorder

example (L : LinearOrder X) :
    (CompletePreference.ofLinearOrder L).toPreference.toPreorder = L.toPreorder :=
  CompletePreference.toPreorder_ofLinearOrder L

example (S : CompletePreference Y) (f : X → Y) : CompletePreference X := S.comap f

example (S : CompletePreference Y) (f : X → Y) :
    (S.comap f).toPreference = S.toPreference.comap f := S.toPreference_comap f

example (L : LinearOrder X) : Std.Antisymm (CompletePreference.ofLinearOrder L).le :=
  inferInstance

example [Std.Antisymm R.le] : IsLinearOrder X R.le := inferInstance

noncomputable example [Std.Antisymm R.le] : LinearOrder X := R.toLinearOrder

example [Std.Antisymm R.le] : CompletePreference.ofLinearOrder R.toLinearOrder = R :=
  R.ofLinearOrder_toLinearOrder

example {x y : X} : ¬x ≼[R] y ↔ y ≺[R] x := R.not_le

example (x y : X) : x ≺[R] y ∨ x ~[R] y ∨ y ≺[R] x :=
  R.lt_or_antisymmRel_or_gt x y

end CompletePreference

section Representation

variable {X Y U : Type*} [Preorder U] (R : Preference X) (u : X → U)

example : R.IsRepresentedBy u ↔ ∀ x y, x ≼[R] y ↔ u x ≤ u y := Iff.rfl

example : R.IsRepresentedBy u ↔ R.toPreorder = Preorder.lift u :=
  R.isRepresentedBy_iff_toPreorder_eq_lift u

example : R.IsRepresentedBy u ↔ R = Preference.ofUtility u :=
  R.isRepresentedBy_iff_eq_ofUtility u

example : Preference X := Preference.ofUtility u

example (x y : X) : x ≼[Preference.ofUtility u] y ↔ u x ≤ u y :=
  Preference.ofUtility_le_iff u x y

example (x y : X) : x ≺[Preference.ofUtility u] y ↔ u x < u y :=
  Preference.ofUtility_lt_iff u x y

example : (Preference.ofUtility u).IsRepresentedBy u :=
  Preference.isRepresentedBy_ofUtility u

example (hu : R.IsRepresentedBy u) (f : Y → X) :
    (R.comap f).IsRepresentedBy (u ∘ f) := hu.comap f

example (hu : R.IsRepresentedBy u) {S : Set X} {a : X} :
    (∀ x ∈ S, x ≼[R] a) ↔ IsMaxOn u S a := hu.forall_le_iff_isMaxOn

example [Std.Total (α := U) (· ≤ ·)] : CompletePreference X :=
  CompletePreference.ofUtility u

example [Std.Total (α := U) (· ≤ ·)] :
    (CompletePreference.ofUtility u).toPreference = Preference.ofUtility u :=
  CompletePreference.toPreference_ofUtility u

end Representation

example {X U : Type*} [PartialOrder U] (u : X → U) (x y : X) :
    x ~[Preference.ofUtility u] y ↔ u x = u y :=
  Preference.ofUtility_antisymmRel_iff u x y

example {X : Type*} [Finite X] (R : CompletePreference X) :
    ∃ u : X → ℕ, R.IsRepresentedBy u := R.exists_isRepresentedBy_nat

example {X : Type*} [Finite X] (R : CompletePreference X) :
    ∃ u : X → ℕ, ∀ (S : Set X) (a : X),
      (∀ x ∈ S, x ≼[R] a) ↔ IsMaxOn u S a := R.exists_nat_utility_isMaxOn

end MathEconLib.Preferences.Tests
