import MathEconLib.Choice.Conditions.WithPartners.Relationships
import MathEconLib.Choice.Induced.FeasibleBundles

/-!
# Completions of preference-induced choice

These corollaries connect preference-induced choice with the conditions in
`MathEconLib.Choice.Conditions.WithPartners.Basic`. A map identifies the
matching partner of each alternative, without requiring a market.

Singleton-or-empty preferences admit the identity completion. For choices
over more general bundles, unilateral substitutability and feasibility give
a completion through the substitute hull. These finite-alternative results
obtain IRC from preference maximization; they construct a completed choice
function, not a completed linear preference order.

Partner-feasible bundle constructors are defined in
`MathEconLib.Choice.Induced.FeasibleBundles`; the general hull relationships
are in `MathEconLib.Choice.Conditions.WithPartners.Relationships`.
-/

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
theorem in `MathEconLib.Choice.Conditions.WithPartners.Relationships`.

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
