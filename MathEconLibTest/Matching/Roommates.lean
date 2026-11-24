/-
Copyright (c) 2026 Frederik Glitzner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederik Glitzner
-/
module

public import MathEconLib.Matching.Classical.Roommates

/-!
# Roommates API checks

Client checks through the public roommates entry point. The statements pin the
stability interface, including the definitions of stability and blocking pairs,
the decidability instance, and the non-existence result. A two-agent market in
which each agent accepts the other exercises the decidability instance: matching
the two agents is stable, while leaving both unmatched is blocked by them. A
second two-agent market, in which only one agent finds the other acceptable,
checks that individual rationality is part of stability.

Further checks pin the bridge to the shared preference API: each agent's
preference is a complete preference without ties, and acceptability,
individual rationality, and blocking agree with their shared-preference
formulations. In the two-agent markets, comparisons decided in the roommates
model transfer to the shared preferences.
-/

@[expose] public section

namespace MathEconLibTest.Matching.Roommates

open MathEconLib.Matching MathEconLib.Preferences

section Interface

variable {A : Type*} (mkt : RoommatesMarket A)

example (μ : RoommatesMatching A) (a : A) : μ (μ a) = a := μ.apply_apply a

example {μ ν : RoommatesMatching A} (h : ∀ a, μ a = ν a) : μ = ν :=
  RoommatesMatching.ext h

example (μ : RoommatesMatching A) :
    mkt.IsStableMatching μ ↔ mkt.IndividuallyRational μ ∧ mkt.Unblocked μ :=
  Iff.rfl

example (μ : RoommatesMatching A) (a b : A) :
    mkt.IsBlockingPair μ a b ↔ a ≠ b ∧ mkt.Blocks μ a b ∧ mkt.Blocks μ b a :=
  Iff.rfl

example (μ : RoommatesMatching A) (a : A) :
    mkt.IndividuallyRationalFor μ a ↔ μ a = a ∨ mkt.Acceptable a (μ a) :=
  mkt.individuallyRationalFor_iff_eq_or_acceptable μ a

example (μ : RoommatesMatching A) (a : A) :
    mkt.Blocks μ a a ↔ ¬mkt.IndividuallyRationalFor μ a :=
  mkt.blocks_self_iff μ a

example {μ : RoommatesMatching A} (h : mkt.IsStableMatching μ) (a b : A) :
    ¬mkt.IsBlockingPair μ a b :=
  h.not_isBlockingPair mkt a b

example {μ : RoommatesMatching A} {a b : A} (h : mkt.IsBlockingPair μ a b) :
    mkt.IsBlockingPair μ b a :=
  mkt.isBlockingPair_comm.mp h

example [Fintype A] [DecidableEq A] : DecidablePred mkt.IsStableMatching :=
  inferInstance

end Interface

section SharedPreferences

variable {A : Type*} (mkt : RoommatesMarket A)

example (a : A) : mkt.preference a = CompletePreference.ofLinearOrder (mkt.pref a) :=
  rfl

example (a : A) : Std.Antisymm (mkt.preference a).le :=
  inferInstance

example (a y z : A) : mkt.le a y z ↔ y ≼[mkt.preference a] z :=
  mkt.le_iff_preference_le a y z

example (a y z : A) : mkt.lt a y z ↔ y ≺[mkt.preference a] z :=
  mkt.lt_iff_preference_lt a y z

example (a b : A) : mkt.Acceptable a b ↔ a ≺[mkt.preference a] b :=
  mkt.acceptable_iff_preference_lt a b

example (μ : RoommatesMatching A) (a : A) :
    mkt.IndividuallyRationalFor μ a ↔ a ≼[mkt.preference a] μ a :=
  mkt.individuallyRationalFor_iff_preference_le μ a

example (μ : RoommatesMatching A) (a b : A) :
    mkt.Blocks μ a b ↔ μ a ≺[mkt.preference a] b :=
  mkt.blocks_iff_preference_lt μ a b

example (μ : RoommatesMatching A) (a b : A) :
    mkt.IsBlockingPair μ a b ↔
      a ≠ b ∧ μ a ≺[mkt.preference a] b ∧ μ b ≺[mkt.preference b] a :=
  mkt.isBlockingPair_iff_ne_and_preference_lt μ a b

end SharedPreferences

example : ∃ (A : Type) (_ : Finite A) (mkt : RoommatesMarket A),
    ¬∃ μ : RoommatesMatching A, mkt.IsStableMatching μ :=
  RoommatesMarket.exists_not_exists_stableMatching

section TwoAgents

/-- Each agent ranks the other agent above itself. -/
def rank (x y : Bool) : ℕ := if x = y then 0 else 1

/-- Two agents who find each other acceptable. -/
def market : RoommatesMarket Bool where
  pref x := LinearOrder.lift' (rank x) (by cases x <;> decide)

/-- The two agents are matched with each other. -/
def together : RoommatesMatching Bool := ⟨not, Bool.not_not⟩

/-- Both agents are unmatched. -/
def apart : RoommatesMatching Bool := ⟨id, fun _ ↦ rfl⟩

example : market.IsStableMatching together := by decide

example : ¬market.IsStableMatching apart := by decide

example : apart false ≺[market.preference false] true :=
  (market.blocks_iff_preference_lt apart false true).mp (by
    let := market.pref false
    unfold RoommatesMarket.Blocks RoommatesMarket.lt
    decide)

/-- Only `false` finds the other agent acceptable. -/
def asymmetricMarket : RoommatesMarket Bool where
  pref _ := inferInstance

example : asymmetricMarket.IsStableMatching apart := by decide

example : ¬asymmetricMarket.IsStableMatching together := by decide

example : ¬true ≺[asymmetricMarket.preference true] false :=
  (asymmetricMarket.acceptable_iff_preference_lt true false).not.mp (by
    let := asymmetricMarket.pref true
    unfold RoommatesMarket.Acceptable RoommatesMarket.lt
    decide)

end TwoAgents

end MathEconLibTest.Matching.Roommates
