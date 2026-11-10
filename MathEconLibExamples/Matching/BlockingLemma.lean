/-
Copyright (c) 2026 Ayan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayan
-/
module

public import MathEconLib.Matching.Classical.Marriage.BlockingLemma
public import Mathlib.Data.Fin.VecNotation

/-!
# The blocking lemma and weak Pareto optimality: applications and limits

Three small marriage markets around `MarriageMarket.IsManOptimal.exists_isBlockingPair_of_ltM`
and `MarriageMarket.IsManOptimal.not_forall_ltM`.

* `unwilling`: one man and one woman who prefers staying single. Matching them makes the only man
  strictly better off than deferred acceptance and has no blocking pair, so the women's half of
  individual rationality cannot be dropped from either result.
* `trade`: three men and three women. An individually rational matching makes two men strictly
  better off than deferred acceptance and leaves the third man's partner unchanged, so weak Pareto
  optimality cannot be strengthened to full Pareto efficiency. The third man and the partner the
  trade gives to one of the gaining men form the pair promised by the blocking lemma.
* `apply`: three men and three women with a stable matching that is not man-optimal. An unstable,
  individually rational matching makes every man strictly better off than that stable matching,
  so the result is specific to the man-optimal one, and applying it identifies a man who does not
  gain over deferred acceptance.

Outcomes of deferred acceptance are computed by kernel evaluation of the executable algorithm and
transferred along `MarriageMarket.galeShapleyComputable_eq_galeShapley`.
-/

@[expose] public section

namespace MathEconLibExamples.Matching.BlockingLemma

open MathEconLib.Matching MarriageMarket

/-! ## Preferences written as best-first lists -/

/-- Score an option by its position in a best-first list: earlier options score higher. -/
def score {α : Type} [DecidableEq α] (l : List (Option α)) (o : Option α) : ℕ :=
  l.length - l.idxOf o

/-- The strict preference that ranks options in the order of a best-first list. -/
abbrev prefOfList {α : Type} [DecidableEq α] (l : List (Option α))
    (h : Function.Injective (score l)) : LinearOrder (Option α) :=
  LinearOrder.lift' (score l) h

local instance {M W : Type} (mkt : MarriageMarket M W) (m : M) (y z : Option W) :
    Decidable (mkt.leM m y z) :=
  (mkt.prefM m).toDecidableLE y z

local instance {M W : Type} (mkt : MarriageMarket M W) (m : M) (y z : Option W) :
    Decidable (mkt.ltM m y z) :=
  (mkt.prefM m).toDecidableLT y z

local instance {M W : Type} (mkt : MarriageMarket M W) (w : W) (y z : Option M) :
    Decidable (mkt.leW w y z) :=
  (mkt.prefW w).toDecidableLE y z

local instance {M W : Type} (mkt : MarriageMarket M W) (w : W) (y z : Option M) :
    Decidable (mkt.ltW w y z) :=
  (mkt.prefW w).toDecidableLT y z

local instance {M W : Type} (mkt : MarriageMarket M W) (ν : M ≃. W) (m : M) (w : W) :
    Decidable (mkt.IsBlockingPair ν m w) :=
  inferInstanceAs (Decidable (mkt.ltM m (ν m) (some w) ∧ mkt.ltW w (ν.symm w) (some m)))

local instance {M W : Type} [Fintype M] (mkt : MarriageMarket M W) (ν : M ≃. W) :
    Decidable (mkt.IndividuallyRationalM ν) :=
  inferInstanceAs (Decidable (∀ m, mkt.leM m none (ν m)))

local instance {M W : Type} [Fintype W] (mkt : MarriageMarket M W) (ν : M ≃. W) :
    Decidable (mkt.IndividuallyRationalW ν) :=
  inferInstanceAs (Decidable (∀ w, mkt.leW w none (ν.symm w)))

local instance {M W : Type} [Fintype M] [Fintype W] (mkt : MarriageMarket M W) (ν : M ≃. W) :
    Decidable (mkt.IndividuallyRational ν) :=
  inferInstanceAs (Decidable (mkt.IndividuallyRationalM ν ∧ mkt.IndividuallyRationalW ν))

/-! ## The women's half of individual rationality cannot be dropped -/

namespace Unwilling

/-- One man and one woman. He prefers her to being single; she prefers being single to him. -/
def market : MarriageMarket Unit Unit where
  prefM _ := prefOfList [some (), none] (by decide)
  prefW _ := prefOfList [none, some ()] (by decide)

/-- The matching that pairs the only man with the only woman. -/
def paired : Unit ≃. Unit := (Equiv.refl Unit).toPEquiv

/-- The pairing is individually rational for the man. -/
theorem paired_individuallyRationalM : market.IndividuallyRationalM paired := by
  decide

/-- The pairing is not individually rational for the woman. -/
theorem paired_not_individuallyRationalW : ¬ market.IndividuallyRationalW paired := by
  decide

/-- Deferred acceptance leaves the man single, so the pairing is a strict gain for every man. -/
theorem forall_ltM_galeShapley_paired :
    ∀ m, market.ltM m (market.galeShapley m) (paired m) := by
  rw [← market.galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- The pairing has no blocking pair, so the blocking lemma also needs the women's half. -/
theorem paired_not_isBlockingPair : ∀ m w, ¬ market.IsBlockingPair paired m w := by
  decide

end Unwilling

/-! ## Full Pareto efficiency fails

Everyone finds everyone acceptable.
Men: `m0 : w0 > w1 > w2`, `m1 : w1 > w0 > w2`, `m2 : w0 > w1 > w2`.
Women: `w0 : m1 > m2 > m0`, `w1 : m2 > m0 > m1`, `w2 : m0 > m1 > m2`.
Man-proposing deferred acceptance ends at `m0-w2, m1-w0, m2-w1`. -/

namespace Trade

/-- A three-by-three market in which deferred acceptance is not Pareto efficient for the men. -/
def market : MarriageMarket (Fin 3) (Fin 3) where
  prefM := ![prefOfList [some 0, some 1, some 2, none] (by decide),
    prefOfList [some 1, some 0, some 2, none] (by decide),
    prefOfList [some 0, some 1, some 2, none] (by decide)]
  prefW := ![prefOfList [some 1, some 2, some 0, none] (by decide),
    prefOfList [some 2, some 0, some 1, none] (by decide),
    prefOfList [some 0, some 1, some 2, none] (by decide)]

/-- The matching `m0-w2, m1-w1, m2-w0`: relative to deferred acceptance, `m1` and `m2` trade
partners and `m0` keeps his. -/
def traded : Fin 3 ≃. Fin 3 where
  toFun := ![some 2, some 1, some 0]
  invFun := ![some 2, some 1, some 0]
  inv := by decide

/-- The outcome of deferred acceptance. -/
theorem galeShapley_apply : ∀ m, market.galeShapley m = ![some 2, some 0, some 1] m := by
  rw [← market.galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- The trade is individually rational, although it is not stable. -/
theorem traded_individuallyRational : market.IndividuallyRational traded := by
  decide

theorem traded_not_stable : ¬ market.IsStableMatching traded := by
  decide

/-- Every man weakly prefers the trade to deferred acceptance. -/
theorem forall_leM_galeShapley_traded :
    ∀ m, market.leM m (market.galeShapley m) (traded m) := by
  rw [← market.galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- Men `m1` and `m2` strictly prefer the trade to deferred acceptance. -/
theorem ltM_galeShapley_traded :
    market.ltM 1 (market.galeShapley 1) (traded 1) ∧
      market.ltM 2 (market.galeShapley 2) (traded 2) := by
  rw [← market.galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- Weak Pareto optimality still applies: the trade does not make every man strictly better off.
Here the man who does not gain is `m0`. -/
theorem not_forall_ltM_galeShapley_traded :
    ¬ ∀ m, market.ltM m (market.galeShapley m) (traded m) :=
  market.not_forall_ltM_galeShapley traded_individuallyRational.2

/-- The blocking lemma applied to the trade, which `m1` strictly prefers. -/
theorem exists_isBlockingPair_traded :
    ∃ m w, ¬ market.ltM m (market.galeShapley m) (traded m) ∧
      (∃ m', market.ltM m' (market.galeShapley m') (traded m') ∧ traded m' = some w) ∧
      market.IsBlockingPair traded m w :=
  market.exists_isBlockingPair_of_ltM_galeShapley traded_individuallyRational.2
    ltM_galeShapley_traded.1

/-- Independent check by computation: the pair is `(m0, w1)`. Man `m0` does not gain, and the
trade gives `w1` to the gaining man `m1`. -/
theorem isBlockingPair_traded :
    ¬ market.ltM 0 (market.galeShapley 0) (traded 0) ∧ traded 1 = some 1 ∧
      market.IsBlockingPair traded 0 1 := by
  rw [← market.galeShapleyComputable_eq_galeShapley]
  decide +kernel

end Trade

/-! ## An application, and why the stable matching must be man-optimal

Everyone finds everyone acceptable.
Men: `m0 : w0 > w1 > w2`, `m1 : w0 > w1 > w2`, `m2 : w1 > w2 > w0`.
Women: `w0 : m2 > m0 > m1`, `w1 : m0 > m2 > m1`, `w2 : m0 > m1 > m2`.
The matching `m0-w1, m1-w2, m2-w0` is stable. The matching `m0-w0, m1-w1, m2-w2` is individually
rational, is not stable, and is strictly better for every man than that stable matching. -/

namespace Apply

/-- A three-by-three market with a stable matching that is not man-optimal. -/
def market : MarriageMarket (Fin 3) (Fin 3) where
  prefM := ![prefOfList [some 0, some 1, some 2, none] (by decide),
    prefOfList [some 0, some 1, some 2, none] (by decide),
    prefOfList [some 1, some 2, some 0, none] (by decide)]
  prefW := ![prefOfList [some 2, some 0, some 1, none] (by decide),
    prefOfList [some 0, some 2, some 1, none] (by decide),
    prefOfList [some 0, some 1, some 2, none] (by decide)]

/-- The stable matching `m0-w1, m1-w2, m2-w0`. -/
def womenFavored : Fin 3 ≃. Fin 3 where
  toFun := ![some 1, some 2, some 0]
  invFun := ![some 2, some 0, some 1]
  inv := by decide

/-- The diagonal matching `m0-w0, m1-w1, m2-w2`. -/
def diagonal : Fin 3 ≃. Fin 3 where
  toFun := ![some 0, some 1, some 2]
  invFun := ![some 0, some 1, some 2]
  inv := by decide

theorem womenFavored_stable : market.IsStableMatching womenFavored := by
  decide

theorem diagonal_individuallyRational : market.IndividuallyRational diagonal := by
  decide

/-- The diagonal matching is unstable, so optimality among stable matchings says nothing
about it. -/
theorem diagonal_not_stable : ¬ market.IsStableMatching diagonal := by
  decide

/-- Every man strictly prefers the diagonal matching to the stable matching `womenFavored`.
Weak Pareto optimality is therefore false for an arbitrary stable matching. -/
theorem forall_ltM_womenFavored_diagonal :
    ∀ m, market.ltM m (womenFavored m) (diagonal m) := by
  decide

/-- Weak Pareto optimality applied to the diagonal matching: some man does not strictly gain over
deferred acceptance. -/
theorem not_forall_ltM_galeShapley_diagonal :
    ¬ ∀ m, market.ltM m (market.galeShapley m) (diagonal m) :=
  market.not_forall_ltM_galeShapley diagonal_individuallyRational.2

/-- A consequence that needs no computation: `womenFavored` is not man-optimal. -/
theorem womenFavored_not_isManOptimal : ¬ market.IsManOptimal womenFavored := fun h =>
  IsManOptimal.not_forall_ltM market h diagonal_individuallyRational.2
    forall_ltM_womenFavored_diagonal

/-- Independent check by computation: the outcome of deferred acceptance. Man `m0` keeps his
diagonal partner, and he is the man who does not gain. -/
theorem galeShapley_apply : ∀ m, market.galeShapley m = ![some 0, some 2, some 1] m := by
  rw [← market.galeShapleyComputable_eq_galeShapley]
  decide +kernel

end Apply

end MathEconLibExamples.Matching.BlockingLemma
