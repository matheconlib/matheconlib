/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLib.RevealedPreference

/-!
# Independent finite and infinite Reny API pins

These clients import only the public revealed-preference umbrella. Explicit
regularity and affordability clauses prevent changes to a packaged predicate
from silently weakening the expected conclusion. Infinite observations have no
finiteness, countability, or nonemptiness assumption. The margin contract retains
both its finite-sum bound and its fixed-before-finite-subfamilies quantifier order.
-/

set_option autoImplicit false
set_option linter.privateModule false

open MathEconLib.RevealedPreference
open scoped BigOperators

-- Finite regularity includes continuity and concavity on the entire bundle space.
example {L : ℕ} {T : Type*} [Finite T] (hL : 0 < L) (p q : T → Bundle L)
    (hp : RenyPriceAdmissible p) (hq : RenyChoiceAdmissible q) :
    GraphGARP p q ↔ ∃ u : Utility L,
      Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      MonotoneOn u {x | Nonnegative x} ∧
      (∀ x y, Nonnegative x → Nonnegative y → (∀ i, x i < y i) → u x < u y) ∧
      ∀ t y, Nonnegative y →
        (dot (p t) y ≤ dot (p t) (q t) → u y ≤ u (q t)) ∧
        (dot (p t) y < dot (p t) (q t) → u y < u (q t)) :=
  finite_graphGARP_iff_regularRenyRationalization hL p q hp hq

-- The infinite conclusion spells out every regularity and rationalization clause.
example {L : ℕ} {T : Type*} (hL : 0 < L) (p q : T → Bundle L)
    (hp : RenyPriceAdmissible p) (hq : RenyChoiceAdmissible q) :
    GraphGARP p q ↔ ∃ u : Utility L,
      MonotoneOn u {x | Nonnegative x} ∧ QuasiconcaveOn ℝ {x | Nonnegative x} u ∧
      (∀ x y, Nonnegative x → Nonnegative y → (∀ i, x i < y i) → u x < u y) ∧
      ∀ t y, Nonnegative y →
        (dot (p t) y ≤ dot (p t) (q t) → u y ≤ u (q t)) ∧
        (dot (p t) y < dot (p t) (q t) → u y < u (q t)) :=
  infinite_graphGARP_iff_regularRenyRationalization hL p q hp hq

-- Also retain the named terminal characterization as a downstream contract.
example {L : ℕ} {T : Type*} (hL : 0 < L) (p q : T → Bundle L)
    (hp : RenyPriceAdmissible p) (hq : RenyChoiceAdmissible q) :
    ((∃ u : Utility L, RenyRationalizes p q u) ↔ GraphGARP p q) ∧
      (GraphGARP p q ↔ HasRegularRenyRationalization p q) :=
  infinite_reny_characterization hL p q hp hq

-- Strict affordability is essential even without any regularity premise on u.
example {L : ℕ} {T : Type*} (p q : T → Bundle L) (u : Utility L) :
    RenyRationalizes p q u ↔ ∀ t y, Nonnegative y →
      (dot (p t) y ≤ dot (p t) (q t) → u y ≤ u (q t)) ∧
      (dot (p t) y < dot (p t) (q t) → u y < u (q t)) :=
  Iff.rfl

-- One positive schedule, with its full bound, precedes every finite subfamily.
example {L : ℕ} {T : Type*} (hL : 0 < L) (p q : T → Bundle L)
    (hp : RenyPriceAdmissible p) (hq : RenyChoiceAdmissible q)
    (hg : GraphGARP p q) :
    ∃ w : RationalStrongPair L → ℝ,
      (∀ r, 0 < w r) ∧
      (∀ K : Finset (RationalStrongPair L), ∑ r ∈ K, w r ≤ 1 / 2) ∧
      ∀ s : Finset (InfiniteAfriat.Constraint L T),
        ∃ v : InfiniteAfriat.UtilityCube L, ∀ c ∈ s,
          InfiniteAfriat.Satisfies p q w c v :=
  InfiniteAfriat.exists_uniform_margins_and_finite_witnesses hL p q hp hq hg

-- Pin the economic meaning of every constraint used in that margin contract.
example {L : ℕ} {T : Type*} (p q : T → Bundle L)
    (w : RationalStrongPair L → ℝ) (v : InfiniteAfriat.UtilityCube L)
    (t : T) (y : Bundle L) :
    InfiniteAfriat.Satisfies p q w (.budget t y) v ↔
      Nonnegative y → dot (p t) y ≤ dot (p t) (q t) →
        InfiniteAfriat.cubeUtility v y ≤ InfiniteAfriat.cubeUtility v (q t) :=
  Iff.rfl

example {L : ℕ} {T : Type*} (p q : T → Bundle L)
    (w : RationalStrongPair L → ℝ) (v : InfiniteAfriat.UtilityCube L)
    (x y : Bundle L) :
    InfiniteAfriat.Satisfies p q w (.monotone x y) v ↔
      Nonnegative x → Nonnegative y → x ≤ y →
        InfiniteAfriat.cubeUtility v x ≤ InfiniteAfriat.cubeUtility v y :=
  Iff.rfl

example {L : ℕ} {T : Type*} (p q : T → Bundle L)
    (w : RationalStrongPair L → ℝ) (v : InfiniteAfriat.UtilityCube L)
    (x y : Bundle L) (a b : ℝ) :
    InfiniteAfriat.Satisfies p q w (.quasiconcave x y a b) v ↔
      Nonnegative x → Nonnegative y → 0 ≤ a → 0 ≤ b → a + b = 1 →
        min (InfiniteAfriat.cubeUtility v x) (InfiniteAfriat.cubeUtility v y) ≤
          InfiniteAfriat.cubeUtility v (a • x + b • y) :=
  Iff.rfl

example {L : ℕ} {T : Type*} (p q : T → Bundle L)
    (w : RationalStrongPair L → ℝ) (v : InfiniteAfriat.UtilityCube L)
    (r : RationalStrongPair L) :
    InfiniteAfriat.Satisfies p q w (.gap r) v ↔
      InfiniteAfriat.cubeUtility v r.lower + w r ≤ InfiniteAfriat.cubeUtility v r.upper :=
  Iff.rfl

example {L : ℕ} {T : Type*} (p q : T → Bundle L) (u : Utility L) :
    WeakUtilityRationalizes p q u ↔
      ∀ t y, Nonnegative y → dot (p t) y ≤ dot (p t) (q t) → u y ≤ u (q t) :=
  Iff.rfl

-- Weak rationalization reuses the dataset and choice interfaces.
example {L : ℕ} {T : Type*} (p q : T → Bundle L) (u : Utility L)
    (hu : RenyRationalizes p q u) : WeakUtilityRationalizes p q u :=
  hu.weakUtilityRationalizes

example {L : ℕ} {T : Type*} (D : Dataset L T) (u : Utility L) :
    WeakUtilityRationalizes D.price D.choice u ↔ UtilityRationalizes D u :=
  weakUtilityRationalizes_iff_utilityRationalizes D u

example {L : ℕ} {T : Type*} (p q : T → Bundle L) (u : Utility L)
    (hq : RenyChoiceAdmissible q) :
    WeakUtilityRationalizes p q u ↔ ∀ t,
      q t ∈ utilityChoice u {y | Nonnegative y ∧ dot (p t) y ≤ dot (p t) (q t)} :=
  weakUtilityRationalizes_iff_mem_utilityChoice p q u hq

-- This implication concerns the two utility packages, with no data assumptions.
example {L : ℕ} {T : Type*} (p q : T → Bundle L)
    (h : HasFiniteRegularRenyRationalization p q) :
    HasRegularRenyRationalization p q :=
  finiteRegularRenyRationalization_implies_regularRenyRationalization p q h

#print axioms finite_graphGARP_iff_regularRenyRationalization
#print axioms infinite_graphGARP_iff_regularRenyRationalization
#print axioms infinite_reny_characterization
#print axioms InfiniteAfriat.exists_uniform_margins_and_finite_witnesses
#print axioms weakUtilityRationalizes_iff_utilityRationalizes
#print axioms weakUtilityRationalizes_iff_mem_utilityChoice
#print axioms finiteRegularRenyRationalization_implies_regularRenyRationalization
