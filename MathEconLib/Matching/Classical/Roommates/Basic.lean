/-
Copyright (c) 2026 Frederik Glitzner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederik Glitzner
-/
module

public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Basic

/-!
# Roommates markets, matchings, and stability

The stable roommates problem is one-sided: a single population `A` of agents,
any two of whom may be matched with each other.

## Scope and conventions

* Each agent `a` has a strict linear order over **all** agents, including `a`
  itself. Larger agents are preferred. The position of `a` in its own order is
  its outside option: agents ranked above `a` are acceptable, agents ranked
  below `a` are unacceptable.
* Acceptability need not be mutual. Individual rationality rules out matching
  an agent to an unacceptable partner, and an agent cannot take part in a
  blocking pair with someone it finds unacceptable.
* A matching is an involution `μ : A → A`. `μ a = a` means that `a` is
  unmatched; otherwise `μ a` is `a`'s partner, and `μ (μ a) = a` makes the
  partnership mutual.
* Preferences are strict (no ties). Weak preferences are out of scope.

The classical problem of Gale and Shapley (1962), with complete preference
lists, is the special case in which every agent finds every other agent
acceptable.

This differs from `MarriageMarket`, which represents being single by `none`.
A translation between the two models is not yet formalized.

## Main definitions

* `RoommatesMarket A`: preferences of every agent over all agents.
* `RoommatesMatching A`: involutions on `A`.
* `RoommatesMarket.IsStableMatching`: individual rationality and no blocking
  pair of two distinct agents.

## References

* David Gale and Lloyd S. Shapley (1962), *College Admissions and the Stability
  of Marriage*, *The American Mathematical Monthly* **69**(1), 9–15.
  [DOI: 10.1080/00029890.1962.11989827](https://doi.org/10.1080/00029890.1962.11989827).
* Jimmy J. M. Tan (1991), *A necessary and sufficient condition for the existence
  of a complete stable matching*, *Journal of Algorithms* **12**(1), 154–178.
  [DOI: 10.1016/0196-6774(91)90028-W](https://doi.org/10.1016/0196-6774(91)90028-W).
* Dan Gusfield and Robert W. Irving (1989), *The Stable Marriage Problem:
  Structure and Algorithms*, MIT Press.
-/

@[expose] public section

namespace MathEconLib.Matching

universe u

/-- A roommates market. Each agent has a strict linear order over all agents,
including itself; "larger" agents are preferred, and the agent's own position is
its outside option of remaining unmatched. -/
structure RoommatesMarket (A : Type u) where
  /-- Agent `a`'s preference over potential roommates (and itself). -/
  pref : A → LinearOrder A

/-- A roommates matching: each agent is assigned a partner (or itself), and
partnerships are mutual. `μ a = a` means that `a` is unmatched. -/
structure RoommatesMatching (A : Type u) where
  /-- The assignment of each agent. -/
  toFun : A → A
  /-- Partnerships are mutual. -/
  involutive : Function.Involutive toFun

namespace RoommatesMatching

variable {A : Type u}

instance : FunLike (RoommatesMatching A) A A where
  coe := toFun
  coe_injective := by
    rintro ⟨f, _⟩ ⟨g, _⟩ h
    congr

@[simp] theorem apply_apply (μ : RoommatesMatching A) (a : A) : μ (μ a) = a :=
  μ.involutive a

/-- Two matchings are equal when they assign the same agents. -/
@[ext] theorem ext {μ ν : RoommatesMatching A} (h : ∀ a, μ a = ν a) : μ = ν :=
  DFunLike.ext _ _ h

end RoommatesMatching

namespace RoommatesMarket

variable {A : Type u}
variable (mkt : RoommatesMarket A)


/-! ## Preference relations as data -/

/-- Strict preference of agent `a`: `a` prefers `z` to `y`. -/
def lt (a : A) (y z : A) : Prop :=
  letI := mkt.pref a
  y < z

/-- Weak preference of agent `a`: `a` weakly prefers `z` to `y`. -/
def le (a : A) (y z : A) : Prop :=
  letI := mkt.pref a
  y ≤ z

/-- `b` is acceptable to `a`: `a` prefers `b` to remaining unmatched. -/
def Acceptable (a b : A) : Prop :=
  mkt.lt a a b


/-! ## Stability -/

/-- Individual rationality for agent `a`: its assignment is no worse than
remaining unmatched. -/
def IndividuallyRationalFor (μ : RoommatesMatching A) (a : A) : Prop :=
  mkt.le a a (μ a)

/-- Individual rationality for every agent. -/
def IndividuallyRational (μ : RoommatesMatching A) : Prop :=
  ∀ a, mkt.IndividuallyRationalFor μ a

/-- Agent `a` strictly prefers `b` to its current assignment.

This is only `a`'s condition for blocking; it does not require that `b`
reciprocates. -/
def Blocks (μ : RoommatesMatching A) (a b : A) : Prop :=
  mkt.lt a (μ a) b

/-- Two distinct agents block `μ` if each strictly prefers the other to its
current assignment.
Distinctness is part of the definition: with `a = b` the condition would say
that `a` prefers being single to `μ a`, which is a failure of individual
rationality rather than a blocking pair. See `blocks_self_iff`. -/
def IsBlockingPair (μ : RoommatesMatching A) (a b : A) : Prop :=
  a ≠ b ∧ mkt.Blocks μ a b ∧ mkt.Blocks μ b a

/-- The matching has no blocking pair. -/
def Unblocked (μ : RoommatesMatching A) : Prop :=
  ∀ a b, ¬mkt.IsBlockingPair μ a b

/-- Classical stability: individual rationality and no blocking pair. -/
def IsStableMatching (μ : RoommatesMatching A) : Prop :=
  mkt.IndividuallyRational μ ∧ mkt.Unblocked μ


/-! ### Elementary interfaces -/

/-- Individual rationality in words: the agent is unmatched or matched to an
acceptable partner. -/
theorem individuallyRationalFor_iff (μ : RoommatesMatching A) (a : A) :
    mkt.IndividuallyRationalFor μ a ↔ μ a = a ∨ mkt.Acceptable a (μ a) := by
  let := mkt.pref a
  exact le_iff_eq_or_lt.trans (or_congr_left eq_comm)

/-- A stable matching is individually rational for every agent. -/
theorem IsStableMatching.individuallyRationalFor {μ : RoommatesMatching A}
    (h : mkt.IsStableMatching μ) (a : A) : mkt.IndividuallyRationalFor μ a :=
  h.1 a

/-- A stable matching has no blocking pair. -/
theorem IsStableMatching.not_isBlockingPair {μ : RoommatesMatching A}
    (h : mkt.IsStableMatching μ) (a b : A) : ¬mkt.IsBlockingPair μ a b :=
  h.2 a b

/-- Blocking is symmetric in the two agents. -/
theorem isBlockingPair_comm {μ : RoommatesMatching A} {a b : A} :
    mkt.IsBlockingPair μ a b ↔ mkt.IsBlockingPair μ b a := by
  constructor <;> exact fun ⟨hne, hab, hba⟩ => ⟨hne.symm, hba, hab⟩

/-- An agent never blocks with its own partner. -/
theorem not_isBlockingPair_apply (μ : RoommatesMatching A) (a : A) :
    ¬mkt.IsBlockingPair μ a (μ a) := by
  let := mkt.pref a
  exact fun ⟨_, h, _⟩ => lt_irrefl (μ a) h

/-- An agent "blocks with itself" exactly when individual rationality fails. -/
theorem blocks_self_iff (μ : RoommatesMatching A) (a : A) :
    mkt.Blocks μ a a ↔ ¬mkt.IndividuallyRationalFor μ a := by
  let := mkt.pref a
  exact not_le.symm


/-! ## Decidability -/

section Decide

variable [Fintype A] [DecidableEq A]

instance : DecidablePred mkt.IsStableMatching := by
  intro μ
  unfold IsStableMatching IndividuallyRational IndividuallyRationalFor
  unfold Unblocked IsBlockingPair Blocks
  unfold le lt
  infer_instance

end Decide

end RoommatesMarket

end MathEconLib.Matching
