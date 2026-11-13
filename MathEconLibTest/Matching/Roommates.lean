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
stability interface and the non-existence result. A two-agent market in which
each agent accepts the other exercises the decidability instance: matching the
two agents is stable, while leaving both unmatched is blocked by them.
-/

@[expose] public section

namespace MathEconLibTest.Matching.Roommates

open MathEconLib.Matching

section Interface

variable {A : Type*} (mkt : RoommatesMarket A)

example (μ : RoommatesMatching A) (a : A) : μ (μ a) = a := by simp

example {μ ν : RoommatesMatching A} (h : ∀ a, μ a = ν a) : μ = ν := by ext a; exact h a

example (μ : RoommatesMatching A) (a : A) :
    mkt.IndividuallyRationalFor μ a ↔ μ a = a ∨ mkt.Acceptable a (μ a) :=
  mkt.individuallyRationalFor_iff μ a

example (μ : RoommatesMatching A) (a : A) :
    mkt.Blocks μ a a ↔ ¬mkt.IndividuallyRationalFor μ a :=
  mkt.blocks_self_iff μ a

example {μ : RoommatesMatching A} (h : mkt.IsStableMatching μ) (a b : A) :
    ¬mkt.IsBlockingPair μ a b :=
  h.not_isBlockingPair mkt a b

example {μ : RoommatesMatching A} {a b : A} (h : mkt.IsBlockingPair μ a b) :
    mkt.IsBlockingPair μ b a :=
  mkt.isBlockingPair_comm.mp h

end Interface

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
def apart : RoommatesMatching Bool := ⟨id, fun _ => rfl⟩

example : market.IsStableMatching together := by decide

example : ¬market.IsStableMatching apart := by decide

end TwoAgents

end MathEconLibTest.Matching.Roommates
