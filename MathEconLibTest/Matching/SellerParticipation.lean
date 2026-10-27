/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLibExamples.Matching.SellerParticipation

/-!
# Seller participation regressions

Import the canonical two-seller examples. Empty choice alone cannot characterize a preference
for remaining unmatched; attained and unattained empty choices have different certificates.
Finite and empty menus retain the guarded interpretation, even with an infinite contract carrier.
-/

namespace MathEconLibTest.Matching.SellerParticipation

open MathEconLib.Matching MathEconLibExamples.Matching.SellerParticipation

/-- The same empty choice can have opposite attainment and nonparticipation certificates. -/
theorem empty_causes_are_distinct (s : Bool) :
    increasingMarket.choiceS s Set.univ = ∅ ∧
      decliningMarket.choiceS s Set.univ = ∅ ∧
      ¬ Market.HasSellerOptimum seller increasing s Set.univ ∧
      ¬ Market.Declines seller increasing s Set.univ ∧
      Market.HasSellerOptimum seller outsideFirst s Set.univ ∧
      Market.Declines seller outsideFirst s Set.univ :=
  ⟨increasing_empty s, outside_empty s Set.univ, increasing_unattained s,
    increasing_not_declines s, outside_attains s Set.univ, outside_declines s Set.univ⟩

/-- Omitting attainment would make the proposed nonparticipation equivalence false. -/
theorem unguarded_nonparticipation_iff_fails (s : Bool) :
    ¬ (increasingMarket.choiceS s Set.univ = ∅ ↔
      Market.Declines seller increasing s Set.univ) :=
  fun h ↦ increasing_not_declines s (h.mp (increasing_empty s))

/-- Infinite global availability need not prevent attainment on a finite own-contract menu. -/
theorem own_menu_filters_other_sellers : mixedMenu.Infinite ∧
    Market.HasSellerOptimum seller increasing false mixedMenu ∧
    increasingMarket.choiceS false mixedMenu = {(false, 0)} :=
  ⟨mixed_infinite, mixed_attains, mixed_choice_eq⟩

/-- A menu of foreign contracts yields an attained outside option and empty choice. -/
theorem foreign_contracts_are_ignored (s : Bool) :
    Market.HasSellerOptimum seller increasing s {x | seller x ≠ s} ∧
      Market.Declines seller increasing s {x | seller x ≠ s} ∧
      increasingMarket.choiceS s {x | seller x ≠ s} = ∅ :=
  ⟨(foreign_declines s).hasSellerOptimum, foreign_declines s, foreign_empty s⟩

theorem finite_menu_attains (pref : ∀ s, LinearOrder (Option (OwnContract s)))
    (s : Bool) (A : Finset Contract) : Market.HasSellerOptimum seller pref s (A : Set Contract) :=
  Market.hasSellerOptimum_of_finite seller pref s A.finite_toSet

/-- Finite-menu empty choice has the guarded nonparticipation interpretation. -/
theorem finite_menu_nonparticipation (pref : ∀ s, LinearOrder (Option (OwnContract s)))
    (s : Bool) (A : Finset Contract) :
    (market pref).choiceS s (A : Set Contract) = ∅ ↔
      Market.Declines seller pref s (A : Set Contract) :=
  Market.choiceS_ofSellerPreferences_eq_empty_iff_of_hasSellerOptimum
    buyer seller buyerChoice buyerSupport pref s (finite_menu_attains pref s A)

theorem empty_menu_declines (pref : ∀ s, LinearOrder (Option (OwnContract s))) (s : Bool) :
    Market.Declines seller pref s ∅ := fun _ hx ↦ hx.elim

theorem empty_menu_attains (pref : ∀ s, LinearOrder (Option (OwnContract s))) (s : Bool) :
    Market.HasSellerOptimum seller pref s ∅ := (empty_menu_declines pref s).hasSellerOptimum

theorem empty_menu_choice (pref : ∀ s, LinearOrder (Option (OwnContract s))) (s : Bool) :
    (market pref).choiceS s ∅ = ∅ :=
  Market.choiceS_ofSellerPreferences_eq_empty_iff_of_hasSellerOptimum
    buyer seller buyerChoice buyerSupport pref s (empty_menu_attains pref s) |>.mpr
      (empty_menu_declines pref s)

end MathEconLibTest.Matching.SellerParticipation
