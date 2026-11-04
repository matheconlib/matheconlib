/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Preferences.Complete

/-!
# Preference relations read from the better alternative

Social choice and choice under risk write `R x y` for "`x` is at least as good as `y`", the
reverse of `Preference.le`. This file states that unbundled form as properties of a relation
`R : X → X → Prop`, and bridges it to `Preference` and `CompletePreference`.

## Main definitions

* `IsComplete`, `IsTransitive`, `IsPreferenceRelation`, `IsLinearPreference`: properties of `R`.
* `StrictPart R`, `Indiff R`: strict preference `x ≻ y` and indifference `x ∼ y`.
* `Preference.ge`, `CompletePreference.ofGE`: the bridges between the two orientations.

## Main statements

* `isPreferenceRelation_iff_exists_ge`: preference relations are the `S.ge` of complete preferences.

## References

* Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, Section 1.1.
-/

@[expose] public section

namespace MathEconLib.Preferences

variable {X : Type*} {R : X → X → Prop} {x y z : X}

/-- `R` is complete: any two alternatives are related in some direction (`Std.Total R`). -/
def IsComplete (R : X → X → Prop) : Prop := Std.Total R

/-- `R` is reflexive (`Std.Refl R`). -/
def IsReflexive (R : X → X → Prop) : Prop := Std.Refl R

/-- `R` is transitive (`IsTrans X R`). -/
def IsTransitive (R : X → X → Prop) : Prop := IsTrans X R

/-- `R` is antisymmetric (`Std.Antisymm R`). -/
def IsAntisymmetric (R : X → X → Prop) : Prop := Std.Antisymm R

/-- `R` is a preference relation: it is complete and transitive. -/
def IsPreferenceRelation (R : X → X → Prop) : Prop := IsComplete R ∧ IsTransitive R

/-- `R` is a linear preference: an antisymmetric preference relation. -/
def IsLinearPreference (R : X → X → Prop) : Prop := IsPreferenceRelation R ∧ IsAntisymmetric R

/-- Strict preference `x ≻ y`: `R x y` holds and `R y x` fails. -/
def StrictPart (R : X → X → Prop) (x y : X) : Prop := R x y ∧ ¬R y x

/-- Indifference `x ∼ y`: `R x y` and `R y x` (Mathlib's `AntisymmRel R`). -/
abbrev Indiff (R : X → X → Prop) : X → X → Prop := AntisymmRel R

instance [DecidableRel R] : DecidableRel (StrictPart R) :=
  fun x y => inferInstanceAs (Decidable (R x y ∧ ¬R y x))

instance : IsNonstrictStrictOrder X R (StrictPart R) := ⟨fun _ _ => Iff.rfl⟩

instance : Std.Asymm (StrictPart R) := ⟨fun _ _ h h' => h.2 h'.1⟩

theorem isComplete_iff : IsComplete R ↔ ∀ x y, R x y ∨ R y x := ⟨fun h => h.total, fun h => ⟨h⟩⟩

theorem isTransitive_iff : IsTransitive R ↔ ∀ x y z, R x y → R y z → R x z :=
  ⟨fun h => h.trans, fun h => ⟨h⟩⟩

theorem isAntisymmetric_iff : IsAntisymmetric R ↔ ∀ x y, R x y → R y x → x = y :=
  ⟨fun h => h.antisymm, fun h => ⟨h⟩⟩

theorem strictPart_iff : StrictPart R x y ↔ R x y ∧ ¬R y x := Iff.rfl

theorem indiff_iff : Indiff R x y ↔ R x y ∧ R y x := Iff.rfl

theorem IsComplete.total (h : IsComplete R) (x y : X) : R x y ∨ R y x :=
  Std.Total.total (self := h) x y

theorem IsReflexive.refl (h : IsReflexive R) (x : X) : R x x := Std.Refl.refl (self := h) x

theorem IsTransitive.trans (h : IsTransitive R) (hxy : R x y) (hyz : R y z) : R x z :=
  IsTrans.trans (self := h) x y z hxy hyz

theorem IsAntisymmetric.antisymm (h : IsAntisymmetric R) (hxy : R x y) (hyx : R y x) : x = y :=
  Std.Antisymm.antisymm (self := h) x y hxy hyx

theorem IsComplete.toTotal (h : IsComplete R) : Std.Total R := h

theorem IsTransitive.toIsTrans (h : IsTransitive R) : IsTrans X R := h

theorem isComplete_of_total [h : Std.Total R] : IsComplete R := h

theorem isTransitive_of_isTrans [h : IsTrans X R] : IsTransitive R := h

/-- A complete relation is reflexive. -/
theorem IsComplete.isReflexive (h : IsComplete R) : IsReflexive R :=
  ⟨fun x => (h.total x x).elim id id⟩

theorem IsPreferenceRelation.isComplete (h : IsPreferenceRelation R) : IsComplete R := h.1

theorem IsPreferenceRelation.isTransitive (h : IsPreferenceRelation R) : IsTransitive R := h.2

theorem IsPreferenceRelation.isReflexive (h : IsPreferenceRelation R) : IsReflexive R :=
  h.1.isReflexive

theorem IsPreferenceRelation.total (h : IsPreferenceRelation R) (x y : X) : R x y ∨ R y x :=
  h.1.total x y

theorem IsPreferenceRelation.refl (h : IsPreferenceRelation R) (x : X) : R x x :=
  h.isReflexive.refl x

theorem IsPreferenceRelation.trans (h : IsPreferenceRelation R) (hxy : R x y) (hyz : R y z) :
    R x z :=
  h.2.trans hxy hyz

theorem IsLinearPreference.isPreferenceRelation (h : IsLinearPreference R) :
    IsPreferenceRelation R := h.1

theorem IsLinearPreference.isAntisymmetric (h : IsLinearPreference R) : IsAntisymmetric R := h.2

@[simp] theorem strictPart_irrefl (R : X → X → Prop) (x : X) : ¬StrictPart R x x :=
  fun h => h.2 h.1

theorem StrictPart.asymm (h : StrictPart R x y) : ¬StrictPart R y x := fun h' => h.2 h'.1

theorem StrictPart.ne (h : StrictPart R x y) : x ≠ y := by
  rintro rfl
  exact strictPart_irrefl R x h

/-- The strict part of a transitive relation is transitive. -/
theorem IsTransitive.strictPart (h : IsTransitive R) : IsTransitive (StrictPart R) :=
  isTransitive_iff.2 fun _ _ _ hxy hyz =>
    ⟨h.trans hxy.1 hyz.1, fun hzx => hxy.2 (h.trans hyz.1 hzx)⟩

/-- Indifference derived from a transitive relation is transitive. -/
theorem IsTransitive.indiff (h : IsTransitive R) : IsTransitive (Indiff R) :=
  have := h.toIsTrans
  isTransitive_of_isTrans

theorem IsTransitive.strictPart_of_rel_of_strictPart (h : IsTransitive R) (hxy : R x y)
    (hyz : StrictPart R y z) : StrictPart R x z :=
  ⟨h.trans hxy hyz.1, fun hzx => hyz.2 (h.trans hzx hxy)⟩

theorem IsTransitive.strictPart_of_strictPart_of_rel (h : IsTransitive R)
    (hxy : StrictPart R x y) (hyz : R y z) : StrictPart R x z :=
  ⟨h.trans hxy.1 hyz, fun hzx => hxy.2 (h.trans hyz hzx)⟩

/-- For a complete relation, `R y x` fails exactly when `x ≻ y`. -/
theorem IsComplete.not_rel_iff (h : IsComplete R) : ¬R y x ↔ StrictPart R x y :=
  ⟨fun hn => ⟨(h.total x y).resolve_right hn, hn⟩, fun hs => hs.2⟩

theorem IsComplete.rel_iff_not_strictPart (h : IsComplete R) : R x y ↔ ¬StrictPart R y x := by
  rw [← h.not_rel_iff, not_not]

/-- For a complete antisymmetric relation, distinct alternatives are strictly ranked. -/
theorem IsComplete.strictPart_or_strictPart (hC : IsComplete R) (hA : IsAntisymmetric R)
    (hxy : x ≠ y) : StrictPart R x y ∨ StrictPart R y x := by
  rcases hC.total x y with h | h
  · exact Or.inl ⟨h, fun h' => hxy (hA.antisymm h h')⟩
  · exact Or.inr ⟨h, fun h' => hxy (hA.antisymm h' h)⟩

/-- For a complete antisymmetric relation, `x ≿ y` if and only if `x = y` or `x ≻ y`. -/
theorem IsComplete.rel_iff_eq_or_strictPart (hC : IsComplete R) (hA : IsAntisymmetric R) :
    R x y ↔ x = y ∨ StrictPart R x y := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases h' : R y x
    · exact Or.inl (hA.antisymm h h')
    · exact Or.inr ⟨h, h'⟩
  · rintro (rfl | h)
    · exact hC.isReflexive.refl x
    · exact h.1

/-! ### Bridges to `Preference` and `CompletePreference` -/

namespace Preference

/-- The comparison of `S` read from the better alternative: `S.ge x y` iff `y ≼[S] x`. -/
def ge (S : Preference X) (x y : X) : Prop := y ≼[S] x

@[simp] theorem ge_iff (S : Preference X) : S.ge x y ↔ y ≼[S] x := Iff.rfl

/-- Strict preference in the reversed orientation: `x ≻ y` for `S.ge` is `y ≺[S] x`. -/
@[simp] theorem strictPart_ge (S : Preference X) : StrictPart S.ge x y ↔ y ≺[S] x := Iff.rfl

@[simp] theorem indiff_ge (S : Preference X) : Indiff S.ge x y ↔ x ~[S] y := and_comm

theorem isReflexive_ge (S : Preference X) : IsReflexive S.ge := ⟨S.le_refl⟩

theorem isTransitive_ge (S : Preference X) : IsTransitive S.ge :=
  ⟨fun _ _ _ hxy hyz => S.le_trans hyz hxy⟩

/-- The preference whose reversed comparison is a reflexive, transitive relation `R`. -/
def ofGE (R : X → X → Prop) (hr : IsReflexive R) (ht : IsTransitive R) : Preference X where
  le x y := R y x
  isPreorder := { refl := hr.refl, trans := fun _ _ _ hxy hyz => ht.trans hyz hxy }

@[simp] theorem ofGE_le (hr : IsReflexive R) (ht : IsTransitive R) :
    x ≼[ofGE R hr ht] y ↔ R y x := Iff.rfl

@[simp] theorem ge_ofGE (hr : IsReflexive R) (ht : IsTransitive R) : (ofGE R hr ht).ge = R := rfl

@[simp] theorem ofGE_ge (S : Preference X) : ofGE S.ge S.isReflexive_ge S.isTransitive_ge = S :=
  rfl

end Preference

namespace CompletePreference

theorem isPreferenceRelation_ge (S : CompletePreference X) : IsPreferenceRelation S.ge :=
  ⟨⟨fun x y => S.total y x⟩, S.isTransitive_ge⟩

theorem isLinearPreference_ge (S : CompletePreference X) [Std.Antisymm S.le] :
    IsLinearPreference S.ge :=
  ⟨S.isPreferenceRelation_ge, ⟨fun _ _ hxy hyx => antisymm hyx hxy⟩⟩

/-- The complete preference whose reversed comparison is the preference relation `R`. -/
def ofGE (R : X → X → Prop) (h : IsPreferenceRelation R) : CompletePreference X where
  toPreference := Preference.ofGE R h.isReflexive h.isTransitive
  isTotal := ⟨fun x y => h.total y x⟩

@[simp] theorem toPreference_ofGE (h : IsPreferenceRelation R) :
    (ofGE R h).toPreference = Preference.ofGE R h.isReflexive h.isTransitive := rfl

@[simp] theorem ge_ofGE (h : IsPreferenceRelation R) : (ofGE R h).ge = R := rfl

@[simp] theorem ofGE_ge (S : CompletePreference X) : ofGE S.ge S.isPreferenceRelation_ge = S := rfl

end CompletePreference

/-- `R` is a preference relation iff it is `S.ge` for a complete preference `S`. -/
theorem isPreferenceRelation_iff_exists_ge :
    IsPreferenceRelation R ↔ ∃ S : CompletePreference X, S.ge = R :=
  ⟨fun h => ⟨.ofGE R h, rfl⟩, by rintro ⟨S, rfl⟩; exact S.isPreferenceRelation_ge⟩

end MathEconLib.Preferences

end
