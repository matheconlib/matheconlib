import MathEconLib.Choice.Conditions.Matching.Substitutability

/-!
# Weak substitutability for matching choice

These conditions use a map assigning each alternative to a matching partner.
The map is the only additional data: no market or specified market sides are
required. The binder `counterparty` denotes this map throughout.
`MathEconLib.Matching.Contracts.WeakSubstitutes` supplies the market
specialization.

`UnilaterallySubstitutable` and `BilaterallySubstitutable` use the
single-new-contract formulations of Hatfield–Kojima, *Substitutes and
Stability for Matching with Contracts* (2010), Definitions 5 and 3
(pp. 1715 and 1709), respectively. The unilateral restriction
is on the rejected contract; the bilateral restriction is on both contracts.
No assumption that their matching partners are distinct is added.

The predicates make sense on arbitrary types and quantify over one added
contract. For unilateral substitutability, finiteness alone does not imply
`x ∉ C (insert x Y) → x ∉ C (insert x Z)` for `Y ⊆ Z` and
`Fresh counterparty x Y`. This implication follows with IRC, at most one
chosen contract per partner, and finite chosen sets.

The definitions of completion and substitutable completability are in
`MathEconLib.Choice.Conditions.Matching.Completion`. Relationships between
weak substitutability, completion, and the substitute hull are in
`MathEconLib.Choice.Conditions.Matching.Relationships`.
-/

namespace MathEconLib.Choice

namespace ChoiceFunction

variable {A : Type*} {X : Type*}

section Defs

variable (counterparty : X → A) (C : ChoiceFunction X)

/-- No contract in `Y` shares its counterparty with `x` — the literature's
`d(x) ∉ d(Y)` (Hatfield–Kojima 2010, `d` the doctor map; sellers, in the
market dictionary). -/
def Fresh (x : X) (Y : Set X) : Prop :=
  ∀ y ∈ Y, counterparty y ≠ counterparty x

/-- **Unilateral substitutability** (Hatfield–Kojima 2010, Definition 5, p. 1715):
the substitutability implication is required only when the *rejected* contract's
counterparty has no other contract on the menu. -/
def UnilaterallySubstitutable : Prop :=
  ∀ ⦃x z : X⦄ ⦃Y : Set X⦄, Fresh counterparty x Y →
    x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y))

/-- **Bilateral substitutability** (Hatfield–Kojima 2010, Definition 3, p. 1709):
the implication is
required only when *both* the rejected contract's and the newly available
contract's counterparties have no contract on the menu. -/
def BilaterallySubstitutable : Prop :=
  ∀ ⦃x z : X⦄ ⦃Y : Set X⦄,
    Fresh counterparty x Y → Fresh counterparty z Y →
      x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y))

end Defs

/-- Freshness is absence from the image of the counterparty map. -/
theorem fresh_iff_not_mem_image {counterparty : X → A} {x : X} {Y : Set X} :
    Fresh counterparty x Y ↔ counterparty x ∉ counterparty '' Y := by
  constructor
  · intro h ⟨y, hy, heq⟩
    exact h y hy heq
  · intro h y hy heq
    exact h ⟨y, hy, heq⟩

/-- Freshness is preserved by restricting the menu. -/
theorem Fresh.mono {counterparty : X → A} {x : X} {Y Z : Set X}
    (hfresh : Fresh counterparty x Z) (hYZ : Y ⊆ Z) :
    Fresh counterparty x Y :=
  fun y hy => hfresh y (hYZ hy)

/-- Substitutability implies unilateral substitutability, for any
counterparty map: discard the side condition and apply the
single-new-contract form. -/
theorem Substitutable.unilaterallySubstitutable {C : ChoiceFunction X}
    (hC : C.Substitutable) (counterparty : X → A) :
    C.UnilaterallySubstitutable counterparty :=
  fun _x _z _Y _hfresh hx => hC.not_mem_insert_insert hx

/-- Unilateral substitutability implies bilateral substitutability:
strengthen the hypotheses. -/
theorem UnilaterallySubstitutable.bilaterallySubstitutable
    {counterparty : X → A} {C : ChoiceFunction X}
    (hC : C.UnilaterallySubstitutable counterparty) :
    C.BilaterallySubstitutable counterparty :=
  fun _x _z _Y hfx _hfz hx => hC hfx hx

end ChoiceFunction

end MathEconLib.Choice
