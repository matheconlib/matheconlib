import MathEconLib.Choice.Induced

/-!
# Choice from preferences over bundles with distinct matching partners

A map assigns each alternative to a matching partner. `FeasibleBundle`
restricts bundles to at most one alternative per partner;
`ofFeasibleBundleOrder` specializes `ofBundleOrder` to preferences over
these bundles. The only extra data is the map: the construction does not
require a matching market or weak-substitutability or completion conditions.

This restriction on admissible bundles is distinct from availability at a
menu: an admissible bundle is available when it is contained in that menu.
If no greatest available bundle exists, the choice is empty. The chosen
bundle satisfies the partner restriction on arbitrary types, and preference
maximization supplies consistency on finite alternative types.

The binder `counterparty` denotes the matching-partner map. Conditions and
completion results using this additional data are developed separately in
`MathEconLib.Choice.Conditions.Matching.Completion` and
`MathEconLib.Choice.Conditions.Matching.Preferences`.
-/

namespace MathEconLib.Choice

universe u v

namespace ChoiceFunction

variable {α : Type u} {β : Type v}

section CounterpartyFeasibility

variable {A : Type*}

/-- If every represented bundle is counterparty-feasible, then the
preference-induced choice is counterparty-feasible.

No finiteness assumption is needed. -/
theorem injOn_ofBundleOrder
    {counterparty : α → A}
    (pref : LinearOrder β)
    (bundle : β ↪ Set α)
    (hbundle : ∀ b, Set.InjOn counterparty (bundle b))
    (Y : Set α) :
    Set.InjOn counterparty (ofBundleOrder pref bundle Y) := by
  intro x hx y hy hxy
  obtain ⟨b, hb, hxb, hmax⟩ :=
    (mem_ofBundleOrder pref bundle).mp hx
  have hchoice : ofBundleOrder pref bundle Y = bundle b :=
    ofBundleOrder_eq_of_max pref bundle hb hmax
  have hyb : y ∈ bundle b := by
    rw [← hchoice]
    exact hy
  exact hbundle b hxb hyb hxy

/-- Bundles containing at most one alternative per counterparty. -/
abbrev FeasibleBundle (counterparty : α → A) :=
  {S : Set α // Set.InjOn counterparty S}

/-- Represent a counterparty-feasible bundle by its underlying set. -/
def feasibleBundleEmbedding (counterparty : α → A) :
    FeasibleBundle counterparty ↪ Set α where
  toFun := fun S => S.val
  inj' := by
    intro S T h
    exact Subtype.ext h

/-- Choice induced by preferences over counterparty-feasible bundles.

A represented bundle is available at a menu when it is contained in
that menu. If no greatest available bundle exists, the choice is empty,
as in `ofBundleOrder`. -/
def ofFeasibleBundleOrder
    (counterparty : α → A)
    (pref : LinearOrder (FeasibleBundle counterparty)) :
    ChoiceFunction α :=
  ofBundleOrder pref (feasibleBundleEmbedding counterparty)

@[simp] theorem mem_ofFeasibleBundleOrder
    (counterparty : α → A)
    (pref : LinearOrder (FeasibleBundle counterparty))
    {Y : Set α} {x : α} :
    x ∈ ofFeasibleBundleOrder counterparty pref Y ↔
      ∃ b : FeasibleBundle counterparty,
        b.val ⊆ Y ∧
        x ∈ b.val ∧
        ∀ c : FeasibleBundle counterparty,
          c.val ⊆ Y → pref.le c b := by
  exact mem_ofBundleOrder
    pref (feasibleBundleEmbedding counterparty)

/-- Counterparty feasibility is built into the represented family. -/
theorem injOn_ofFeasibleBundleOrder
    (counterparty : α → A)
    (pref : LinearOrder (FeasibleBundle counterparty))
    (Y : Set α) :
    Set.InjOn counterparty
      (ofFeasibleBundleOrder counterparty pref Y) := by
  exact injOn_ofBundleOrder
    (counterparty := counterparty)
    pref
    (feasibleBundleEmbedding counterparty)
    (fun b => b.property)
    Y

/-- On a finite contract type, preference maximization supplies IRC. -/
theorem consistent_ofFeasibleBundleOrder
    [Finite α]
    (counterparty : α → A)
    (pref : LinearOrder (FeasibleBundle counterparty)) :
    (ofFeasibleBundleOrder counterparty pref).Consistent := by
  exact consistent_ofBundleOrder
    pref (feasibleBundleEmbedding counterparty)

end CounterpartyFeasibility

end ChoiceFunction

end MathEconLib.Choice
