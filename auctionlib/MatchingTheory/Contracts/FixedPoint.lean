/-
Matching with contracts, Layer 2: the fixed-point development.

DRAFT — mostly design signatures only.
-/
import Matching.Contracts.Basic
import Mathlib.Order.FixedPoints

/-!
# The generalized deferred acceptance operator

The survey's seller-superiority order `⊵` on pairs `(Xˢ, Xᵇ)` — contracts
available to sellers, contracts available to buyers — is realized *literally*
as the product order on `Set X × (Set X)ᵒᵈ`. Its top element `(univ, ∅)` is
the classical starting state of seller-proposing deferred acceptance, and the
greatest fixed point of the operator is the seller-optimal state.

With that encoding, mathlib's Knaster–Tarski development
(`Mathlib.Order.FixedPoints`: `OrderHom.lfp`/`OrderHom.gfp`, and the
`CompleteLattice` instance on `Function.fixedPoints f`) supplies existence and
the lattice theorem; the mathematical content of this file is **Lemma 2.1**,
the bijection between fixed points and stable outcomes, which is where IRC and
substitutability actually work.

Everything is stated at many-to-many generality and, apart from the counting
and iteration sections at the bottom, is finiteness-free.

## Main definitions

* `Market.toSellers`, `Market.toBuyers` — the two half-steps (Azevedo–Hatfield
  form: contract-wise membership tests `x ∈ C (insert x ·)`).
* `Market.daFun`, `Market.daHom` — the operator, raw and bundled.
* `Market.outcomeOf` — the outcome carried by a state: `Xˢ ∩ Xᵇ`.
* `Market.sellerOptimal`, `Market.buyerOptimal` — outcomes of `gfp`/`lfp`.

## Main statements

* `Market.monotone_daFun` — substitutability ⇒ monotonicity (the two antitone
  half-lemmas record that each direction uses one side's substitutability
  only, so the many-to-one refinement gets sharper hypotheses for free).
* `Market.stable_outcomeOf`, `Market.isFixedPt_daFun_of_stable`,
  `Market.stableEquivFixedPoints` — Lemma 2.1/4.1.
* `Market.exists_stable`, `Market.sellerChosen_sellerOptimal` — Thm 2.2/3.2.
* `Market.ncard_buyerSide_eq_of_stable` — Thm 2.3/3.3 (rural hospitals);
  to migrate to `RuralHospitals.lean`.
* `OrderHom.exists_iterate_top_eq_gfp` — finite-lattice iteration (survey
  Observation 1); **upstream mathlib candidate**, parked here for now.
-/

open Function OrderDual

universe u v w

variable {B : Type u} {S : Type v} {X : Type w}

namespace Market

variable (M : Market B S X)

/-! ### The operator -/

/-- Contracts buyers would make available to sellers, given buyer access
`Xb`: `x` is offered iff its buyer takes it from `insert x Xb`. -/
def toSellers (Xb : Set X) : Set X :=
  {x | x ∈ M.choiceB (M.buyer x) (insert x Xb)}

/-- Contracts sellers would make available to buyers, given seller access
`Xs`. -/
def toBuyers (Xs : Set X) : Set X :=
  {x | x ∈ M.choiceS (M.seller x) (insert x Xs)}

/-- Buyer-side substitutability makes `toSellers` antitone: shrinking what
buyers can access enlarges what they concede to sellers. Direct from
`ChoiceFunction.Substitutable.mem_insert_of_subset`. -/
theorem antitone_toSellers (hsub : ∀ b, (M.choiceB b).Substitutable) :
    Antitone M.toSellers := by
  sorry

theorem antitone_toBuyers (hsub : ∀ s, (M.choiceS s).Substitutable) :
    Antitone M.toBuyers := by
  sorry

/-- The **generalized deferred acceptance operator** on the
seller-superiority lattice `Set X × (Set X)ᵒᵈ`. First component: contracts
available to sellers; second: contracts available to buyers, dually ordered. -/
def daFun : Set X × (Set X)ᵒᵈ → Set X × (Set X)ᵒᵈ :=
  fun p => (M.toSellers (ofDual p.2), toDual (M.toBuyers p.1))

/-- Substitutability of all agents makes the operator monotone: assembled
from the two antitone half-lemmas and the `OrderDual` bookkeeping. -/
theorem monotone_daFun (hsub : M.Substitutable) : Monotone M.daFun := by
  sorry

/-- The operator, bundled. Note the hypothesis lives in the *bundling*, not
in `daFun` itself, so unbundled statements stay clean. -/
def daHom (hsub : M.Substitutable) :
    Set X × (Set X)ᵒᵈ →o Set X × (Set X)ᵒᵈ :=
  ⟨M.daFun, M.monotone_daFun hsub⟩

/-- The outcome carried by a state: contracts available to both sides. -/
def outcomeOf (p : Set X × (Set X)ᵒᵈ) : Set X :=
  p.1 ∩ ofDual p.2

/-! ### Lemma 2.1: fixed points ↔ stable outcomes

The load-bearing proofs of the project. Stated in the unbundled forms
downstream proofs consume, then packaged as an `Equiv`. All four need both
IRC and substitutability; none needs finiteness. -/

/-- Lemma 2.1, first half: the outcome of a fixed point is stable. -/
theorem stable_outcomeOf (hsub : M.Substitutable) (hcons : M.Consistent)
    {p : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.daFun p) :
    M.Stable (M.outcomeOf p) := by
  sorry

/-- Lemma 2.1, second half (existence): a stable outcome `A` induces the
fixed point `daFun (A, toDual A)`. -/
theorem isFixedPt_daFun_of_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    IsFixedPt M.daFun (M.daFun (A, toDual A)) := by
  sorry

theorem outcomeOf_daFun_of_stable (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.outcomeOf (M.daFun (A, toDual A)) = A := by
  sorry

/-- Lemma 2.1, second half (uniqueness): `daFun (A, toDual A)` is the only
fixed point with outcome `A`. -/
theorem eq_of_isFixedPt_of_outcomeOf_eq (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} {p : Set X × (Set X)ᵒᵈ}
    (hA : M.Stable A) (hp : IsFixedPt M.daFun p)
    (hout : M.outcomeOf p = A) :
    p = M.daFun (A, toDual A) := by
  sorry

/-- Lemma 2.1, packaged: stable outcomes are in bijection with fixed points
of the deferred acceptance operator. -/
noncomputable def stableEquivFixedPoints (hsub : M.Substitutable)
    (hcons : M.Consistent) :
    {A : Set X // M.Stable A} ≃ fixedPoints M.daFun := by
  sorry

/-! ### Theorem 2.2 / 3.2: existence and side-optimal outcomes

Knaster–Tarski supplies the lattice of fixed points of `daHom hsub`; the
order on `{A // M.Stable A}` itself is developed in `Contracts/Order.lean`
by transporting along `stableEquivFixedPoints` (SPEC §8 Q3). Here we expose
the two distinguished outcomes and their optimality. -/

/-- **Existence of stable outcomes** (Hatfield–Milgrom/Fleiner; survey
Theorems 2.2 and 3.2): the outcome of `gfp (daHom hsub)` works. -/
theorem exists_stable (hsub : M.Substitutable) (hcons : M.Consistent) :
    ∃ A : Set X, M.Stable A := by
  sorry

/-- The **seller-optimal** stable outcome: outcome of the greatest fixed
point (`⊤ = (univ, ∅)` is seller-best, so `gfp` is the seller side). -/
noncomputable def sellerOptimal (hsub : M.Substitutable) : Set X :=
  M.outcomeOf (OrderHom.gfp (M.daHom hsub))

/-- The **buyer-optimal** stable outcome: outcome of the least fixed point. -/
noncomputable def buyerOptimal (hsub : M.Substitutable) : Set X :=
  M.outcomeOf (OrderHom.lfp (M.daHom hsub))

theorem stable_sellerOptimal (hsub : M.Substitutable) (hcons : M.Consistent) :
    M.Stable (M.sellerOptimal hsub) := by
  sorry

/-- Seller-optimality: the seller-optimal outcome is seller-chosen over every
stable outcome. (Buyer-pessimality and the buyer duals are stated in
`Contracts/Order.lean`.) -/
theorem sellerChosen_sellerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.SellerChosen (M.sellerOptimal hsub) A := by
  sorry

/-! ### Rural hospitals (Theorems 2.3 / 3.3) — to migrate to its own file

The one place in the core needing `Fintype X`: the counting argument via
`|A| = Σ_b |A_b| = Σ_s |A_s|` (fiberwise card lemmas) comparing any stable
outcome against the seller-optimal one. -/

theorem ncard_buyerSide_eq_of_stable [Fintype X] (hsub : M.Substitutable)
    (hcons : M.Consistent) (hload : M.SizeMonotone) {A A' : Set X}
    (hA : M.Stable A) (hA' : M.Stable A') (b : B) :
    (M.buyerSide b A).ncard = (M.buyerSide b A').ncard := by
  sorry

theorem ncard_sellerSide_eq_of_stable [Fintype X] (hsub : M.Substitutable)
    (hcons : M.Consistent) (hload : M.SizeMonotone) {A A' : Set X}
    (hA : M.Stable A) (hA' : M.Stable A') (s : S) :
    (M.sellerSide s A).ncard = (M.sellerSide s A').ncard := by
  sorry

end Market

/-! ### The iteration lemma (survey Observation 1) — upstream candidate

Mathlib's Kleene material assumes ω-Scott-continuity; the finite-lattice case
appears missing. Proof plan: `f^[n] ⊤` is antitone (`f ⊤ ≤ ⊤` + monotonicity),
stabilizes by finiteness, and the limit is a fixed point above every fixed
point. State here, prove in M2, PR to `Mathlib.Order.FixedPoints`, delete. -/

/-- A monotone self-map of a finite complete lattice reaches its greatest
fixed point by iterating from `⊤`; dually for `⊥` and `lfp`. -/
theorem OrderHom.exists_iterate_top_eq_gfp {L : Type*} [CompleteLattice L]
    [Finite L] (f : L →o L) :
    ∃ n, f^[n] ⊤ = OrderHom.gfp f := by
  sorry

namespace Market

variable (M : Market B S X)

/-- Seller-proposing deferred acceptance: iterating the operator from the
classical start state `(univ, ∅)` computes the seller-optimal stable outcome
in finitely many steps. The executable algorithm of
`Contracts/CumulativeOffer.lean` will be proved equal to this iteration, so
its correctness, termination, and optimality are this one theorem. -/
theorem exists_iterate_daFun_top (hsub : M.Substitutable) [Finite X] :
    ∃ n, M.daFun^[n] (Set.univ, toDual (∅ : Set X)) =
      OrderHom.gfp (M.daHom hsub) := by
  sorry

end Market
