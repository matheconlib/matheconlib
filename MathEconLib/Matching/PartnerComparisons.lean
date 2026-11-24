/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Preferences.Basic
public import Mathlib.Data.Option.Basic

/-!
# Partner comparisons and bilateral blocking

The two sides supply strict comparisons over partners and the outside option `none`.
This is comparison data only: no order laws, utility representation, population measure or
matching algorithm is imposed. Classical linear preferences and partner utilities supply
adapters to the same bilateral blocking rule. This does not develop choice correspondences.
-/

@[expose] public section

namespace MathEconLib.Matching

/-- Comparisons of current and proposed assignments on each side; `none` means unmatched. -/
@[ext] structure PartnerComparisons (A B : Type*) where
  /-- The left agent strictly prefers the second assignment to the first. -/
  left : A → Option B → Option B → Prop
  /-- The right agent strictly prefers the second assignment to the first. -/
  right : B → Option A → Option A → Prop

namespace PartnerComparisons

variable {A B : Type*}

/-- Use each agent's strict preference over partners and the outside option.
The supplied preferences may be incomplete; the comparison interface itself imposes no laws. -/
def ofPreferences (left : A → Preferences.Preference (Option B))
    (right : B → Preferences.Preference (Option A)) : PartnerComparisons A B :=
  ⟨fun a ↦ (left a).lt, fun b ↦ (right b).lt⟩

@[simp] theorem ofPreferences_left (left : A → Preferences.Preference (Option B))
    (right : B → Preferences.Preference (Option A)) (a : A) (x y : Option B) :
    (ofPreferences left right).left a x y ↔ (left a).lt x y := Iff.rfl

@[simp] theorem ofPreferences_right (left : A → Preferences.Preference (Option B))
    (right : B → Preferences.Preference (Option A)) (b : B) (x y : Option A) :
    (ofPreferences left right).right b x y ↔ (right b).lt x y := Iff.rfl

/-- Exchange the two sides' comparisons. -/
def symm (p : PartnerComparisons A B) : PartnerComparisons B A := ⟨p.right, p.left⟩

@[simp] theorem symm_symm (p : PartnerComparisons A B) : p.symm.symm = p := rfl

@[simp] theorem ofPreferences_symm (left : A → Preferences.Preference (Option B))
    (right : B → Preferences.Preference (Option A)) :
    (ofPreferences left right).symm = ofPreferences right left := rfl

/-- Both agents strictly prefer matching to each other over their supplied current assignments. -/
def Blocks (p : PartnerComparisons A B) (a : A) (b : B)
    (currentLeft : Option B) (currentRight : Option A) : Prop :=
  p.left a currentLeft (some b) ∧ p.right b currentRight (some a)

@[simp] theorem blocks_symm (p : PartnerComparisons A B) (a : A) (b : B)
    (currentLeft : Option B) (currentRight : Option A) :
    p.symm.Blocks b a currentRight currentLeft ↔ p.Blocks a b currentLeft currentRight :=
  and_comm

end PartnerComparisons
end MathEconLib.Matching
