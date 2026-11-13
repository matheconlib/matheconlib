/-
Copyright (c) 2026 Frederik Glitzner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederik Glitzner
-/
module

public import MathEconLib.Matching.Classical.Roommates.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# A roommates market without a stable matching

Unlike the marriage market, a roommates market need not have a stable
matching. This module formalizes the four-agent counterexample of
Gale and Shapley (1962, Example 3):

| agent | preferences (best first) |
|-------|--------------------------|
| `a`   | `b`, `c`, `d`, `a`       |
| `b`   | `c`, `a`, `d`, `b`       |
| `c`   | `a`, `b`, `d`, `c`       |
| `d`   | `a`, `b`, `c`, `d`       |

Every agent finds every other agent acceptable, so this is an instance with
complete preference lists. Agents `a`, `b`, `c` rank each other cyclically
and all rank `d` last among the others. `d`'s own preferences are irrelevant
to the argument. Whoever is matched with `d`, or left unmatched, forms a
blocking pair with the agent who ranks them first.

## Main results

* `RoommatesMarket.Counterexamples.GaleShapley.not_isStableMatching`: the
  example has no stable matching.
* `RoommatesMarket.exists_not_exists_stableMatching`: some finite roommates
  market has no stable matching.

## References

* David Gale and Lloyd S. Shapley (1962), *College Admissions and the Stability
  of Marriage*, *The American Mathematical Monthly* **69**(1), 9–15, Example 3.
  [DOI: 10.1080/00029890.1962.11989827](https://doi.org/10.1080/00029890.1962.11989827).
-/

@[expose] public section

namespace MathEconLib.Matching

namespace RoommatesMarket

namespace Counterexamples.GaleShapley

/-- The four agents of the Gale–Shapley roommates example. -/
inductive Agent where
  | a
  | b
  | c
  | d
  deriving DecidableEq

open Agent

instance : Fintype Agent where
  elems := {a, b, c, d}
  complete x := by cases x <;> simp

/-- Each agent's ranking score for the others; a larger score is preferred.
Every agent scores itself `0`, so all other agents are acceptable. -/
def rank : Agent → Agent → ℕ
  | a, b => 3 | a, c => 2 | a, d => 1 | a, a => 0
  | b, c => 3 | b, a => 2 | b, d => 1 | b, b => 0
  | c, a => 3 | c, b => 2 | c, d => 1 | c, c => 0
  | d, a => 3 | d, b => 2 | d, c => 1 | d, d => 0

/-- Each agent's ranking scores are distinct. -/
theorem rank_injective : ∀ x, Function.Injective (rank x) := by
  decide

/-- The Gale–Shapley roommates market: preferences are induced by `rank`. -/
def market : RoommatesMarket Agent where
  pref x := LinearOrder.lift' (rank x) (rank_injective x)

/-- Preferences in the example are comparisons of ranking scores. -/
theorem market_lt_iff (x y z : Agent) :
    market.lt x y z ↔ rank x y < rank x z := Iff.rfl

/-- The Gale–Shapley example has no stable matching. -/
theorem not_isStableMatching (μ : RoommatesMatching Agent) :
    ¬market.IsStableMatching μ := by
  intro h
  -- Two distinct agents who each rank the other above their partner block `μ`.
  have block (x y : Agent) (hxy : x ≠ y)
      (hx : rank x (μ x) < rank x y) (hy : rank y (μ y) < rank y x) : False :=
    h.not_isBlockingPair market x y ⟨hxy, hx, hy⟩
  have ha := μ.apply_apply a
  have hb := μ.apply_apply b
  have hc := μ.apply_apply c
  cases hμa : μ a with
  | a => -- `a` is single: `c` and `a` block
    exact block c a (by decide) (by cases hμc : μ c <;> simp_all [rank]) (by simp [hμa, rank])
  | b => -- `a` is with `b`: `c` and `b` block
    exact block c b (by decide) (by cases hμc : μ c <;> simp_all [rank]) (by simp_all [rank])
  | c => -- `a` is with `c`: `a` and `b` block
    exact block a b (by decide) (by simp [hμa, rank]) (by cases hμb : μ b <;> simp_all [rank])
  | d => -- `a` is with `d`: `c` and `a` block
    exact block c a (by decide) (by cases hμc : μ c <;> simp_all [rank]) (by simp [hμa, rank])

end Counterexamples.GaleShapley

/-- Existence of a stable matching can fail: some finite roommates market has
no stable matching. -/
theorem exists_not_exists_stableMatching :
    ∃ (A : Type) (_ : Finite A) (mkt : RoommatesMarket A),
      ¬∃ μ : RoommatesMatching A, mkt.IsStableMatching μ := by
  refine ⟨Counterexamples.GaleShapley.Agent, inferInstance,
    Counterexamples.GaleShapley.market, ?_⟩
  exact fun ⟨μ, hμ⟩ => Counterexamples.GaleShapley.not_isStableMatching μ hμ

end RoommatesMarket

end MathEconLib.Matching
