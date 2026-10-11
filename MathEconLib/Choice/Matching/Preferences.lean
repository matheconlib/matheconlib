import MathEconLib.Choice.Induced
import MathEconLib.Choice.Matching.Relationships

/-!
# Choice from matching preferences and its completions

A map assigns each alternative to a matching partner. `FeasibleBundle`
restricts bundles to at most one alternative per partner;
`ofFeasibleBundleOrder` specializes `ofBundleOrder` to preferences over
these bundles. The only extra data is the map: the construction does not
require a matching market or weak-substitutability or completion conditions.
The binder `counterparty` denotes this matching-partner map throughout.

This restriction on admissible bundles is distinct from availability at a
menu: an admissible bundle is available when it is contained in that menu.
If no greatest available bundle exists, the choice is empty. The chosen
bundle satisfies the partner restriction on arbitrary types, and preference
maximization supplies consistency on finite alternative types.

The completion corollaries connect preference-induced choice with the
conditions in `MathEconLib.Choice.Matching.Completion`.
Singleton-or-empty preferences admit the identity completion. For choices
over more general bundles, unilateral substitutability and feasibility give
a completion through the substitute hull. These finite-alternative results
obtain IRC from preference maximization; they construct a completed choice
function, not a completed linear preference order. The general hull
relationships are in `MathEconLib.Choice.Matching.Relationships`.
-/

/-! ## Feasible bundles and induced choice -/

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

namespace MathEconLib.Choice

namespace ChoiceFunction

variable {A : Type*} {X : Type*}

/-! ## Identity completions for singleton preferences -/

/-- Singleton-or-empty preferences admit the identity completion,
for every counterparty map. -/
theorem hasConsistentSubstitutableCompletion_ofOptionLinearOrder
    [Finite X]
    (counterparty : X → A)
    (pref : LinearOrder (Option X)) :
    ChoiceFunction.HasConsistentSubstitutableCompletion
      counterparty (ofOptionLinearOrder pref) := by
  refine ⟨ofOptionLinearOrder pref, ?_, ?_, ?_⟩
  · exact isCompletionOf_refl counterparty (ofOptionLinearOrder pref)
  · exact substitutable_ofOptionLinearOrder pref
  · exact consistent_ofOptionLinearOrder pref

/-- The singleton restriction of set preferences admits the identity
completion, for every counterparty map. -/
theorem hasConsistentSubstitutableCompletion_ofSingletonSetLinearOrder
    [Finite X]
    (counterparty : X → A)
    (pref : LinearOrder (Set X)) :
    ChoiceFunction.HasConsistentSubstitutableCompletion
      counterparty (ofSingletonSetLinearOrder pref) := by
  refine ⟨ofSingletonSetLinearOrder pref, ?_, ?_, ?_⟩
  · exact isCompletionOf_refl counterparty
      (ofSingletonSetLinearOrder pref)
  · exact substitutable_ofSingletonSetLinearOrder pref
  · exact consistent_ofSingletonSetLinearOrder pref

/-! ## Preference-induced choice -/

/-- The unilateral-substitutability completion implication for preferences
over represented many-to-one-feasible bundles.

IRC follows from preference maximization on a finite contract type.
Feasibility follows from feasibility of every represented bundle. -/
theorem hasConsistentSubstitutableCompletion_ofBundleOrder
    [Finite X] {β : Type*}
    (counterparty : X → A)
    (pref : LinearOrder β)
    (bundle : β ↪ Set X)
    (hbundle : ∀ b, Set.InjOn counterparty (bundle b))
    (hUS :
      (ofBundleOrder pref bundle).UnilaterallySubstitutable
        counterparty) :
    (ofBundleOrder pref bundle).HasConsistentSubstitutableCompletion
      counterparty := by
  apply hUS.hasConsistentSubstitutableCompletion
  · exact consistent_ofBundleOrder pref bundle
  · exact injOn_ofBundleOrder pref bundle hbundle

/-! ## Preference-induced completions

These corollaries use the finite unilateral-substitutability completion
theorem in `MathEconLib.Choice.Matching.Relationships`.

The original choice is induced by preferences. The completion witness
is the substitute hull; no completed linear preference order is
constructed.
-/

/-- For preferences over counterparty-feasible bundles, neither
feasibility nor IRC needs to be supplied separately. -/
theorem hasConsistentSubstitutableCompletion_ofFeasibleBundleOrder
    [Finite X]
    (counterparty : X → A)
    (pref : LinearOrder (FeasibleBundle counterparty))
    (hUS :
      UnilaterallySubstitutable counterparty
        (ofFeasibleBundleOrder counterparty pref)) :
    HasConsistentSubstitutableCompletion counterparty
      (ofFeasibleBundleOrder counterparty pref) := by
  exact UnilaterallySubstitutable.hasConsistentSubstitutableCompletion
    hUS
    (consistent_ofFeasibleBundleOrder counterparty pref)
    (injOn_ofFeasibleBundleOrder counterparty pref)

/-- For unrestricted set preferences, counterparty feasibility of the
actual choices must be supplied separately.

IRC follows from preference maximization on a finite contract type. -/
theorem hasConsistentSubstitutableCompletion_ofSetLinearOrder
    [Finite X]
    (counterparty : X → A)
    (pref : LinearOrder (Set X))
    (hfeasible :
      ∀ Y, Set.InjOn counterparty (ofSetLinearOrder pref Y))
    (hUS :
      (ofSetLinearOrder pref).UnilaterallySubstitutable counterparty) :
    (ofSetLinearOrder pref).HasConsistentSubstitutableCompletion
      counterparty := by
  exact hUS.hasConsistentSubstitutableCompletion
    (consistent_ofSetLinearOrder pref)
    hfeasible

end ChoiceFunction

end MathEconLib.Choice
