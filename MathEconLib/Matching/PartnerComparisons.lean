/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

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

/-- Exchange the two sides' comparisons. -/
def symm (p : PartnerComparisons A B) : PartnerComparisons B A := ⟨p.right, p.left⟩

@[simp] theorem symm_symm (p : PartnerComparisons A B) : p.symm.symm = p := rfl

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
