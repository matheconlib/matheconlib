module

public import Auctionlib.Auction.Affiliation.Basic
public import Auctionlib.Auction.Affiliation.Sublattice
public import Mathlib

/-! # Affiliation as log-supermodularity (Section 7)

This file records the standard logarithmic reformulation of the affiliation
inequality of **Def 7.2**: for a strictly positive density
`f : (Fin n → ℝ) → ℝ`, affiliation is equivalent to *log-supermodularity*
of `f` with respect to the pointwise lattice structure on `Fin n → ℝ`,

`log (f x) + log (f y) ≤ log (f (x ⊔ y)) + log (f (x ⊓ y))`.

This is the notes' remark that affiliation is exactly the MTP₂
(multivariate totally positive of order 2) / log-supermodularity condition:
`log f` is supermodular, so "raising some coordinates never decreases the
marginal impact of raising others". The equivalence is a direct consequence
of the monotonicity of `Real.log` on positive reals (`Real.log_le_log_iff`)
together with `Real.log_mul`.

## The global form does not apply to densities

The global positivity hypothesis `∀ x, 0 < f x` is **unsatisfiable for the library's own
central object**. `SignalValueEnv.f_support` forces the density to vanish as soon as one
coordinate leaves the box `[x_lo, x_hi]`, so no `SignalValueEnv` with at least one bidder
has a globally positive density: `SignalValueEnv.not_forall_f_pos`. The global statement is
therefore about positive kernels — it does apply to a strictly positive *factor* of a
density, as `Auction.Affiliation.Examples.affiliated_coupFactor` illustrates — but never to
a density itself.

## The localized form

`AffiliatedOn f S` restricts the affiliation inequality to profiles in `S`, and
`affiliatedOn_iff_logSupermodularOn` characterizes it by supermodularity of `log ∘ f` on
`S`, assuming positivity only on `S` and `IsSublattice S`. The sublattice hypothesis is
what returns `x ⊔ y` and `x ⊓ y` to `S`, so that all four logarithms are logarithms of
positive numbers. `affiliatedOn_signalBox_iff_logSupermodularOn` is the environment-level
instance, taken at `S = E.signalBox` (a sublattice by
`SignalValueEnv.isSublattice_signalBox`); worked applications to concrete environments are
in `Auctionlib/Auction/Affiliation/Examples.lean`.

## Main results

* `Auction.Affiliation.affiliated_iff_logSupermodular` : the global (density-inapplicable)
  form.
* `Auction.Affiliation.SignalValueEnv.not_forall_f_pos` : no `SignalValueEnv` density with
  `n ≠ 0` satisfies the global hypothesis.
* `Auction.Affiliation.AffiliatedOn`, `Auction.Affiliation.Affiliated.affiliatedOn`,
  `Auction.Affiliation.affiliatedOn_univ_iff` : the localized affiliation predicate.
* `Auction.Affiliation.affiliatedOn_iff_logSupermodularOn`,
  `Auction.Affiliation.affiliatedOn_signalBox_iff_logSupermodularOn` : the localized
  characterization and its environment-level form.
-/

@[expose] public section

namespace Auction.Affiliation

/-- **Def 7.2, logarithmic form** (MTP₂ / log-supermodularity). For a strictly
positive density `f`, affiliation is equivalent to supermodularity of `log ∘ f`
with respect to the pointwise lattice operations on `Fin n → ℝ`:

`log (f x) + log (f y) ≤ log (f (x ⊔ y)) + log (f (x ⊓ y))` for all `x`, `y`.

The multiplicative inequality of `Affiliated` transfers to the additive one via
`Real.log_mul` and the strict monotonicity of `Real.log` on `(0, ∞)`
(`Real.log_le_log_iff`); positivity of `f` is what licenses both steps.

**This statement never applies to a `SignalValueEnv` density.** Its hypothesis
`∀ x, 0 < f x` is refuted by `SignalValueEnv.f_support` for every environment with at least
one bidder — the density vanishes off the box `[x_lo, x_hi]` — so the theorem is
unsatisfiable at `f = E.f`; `SignalValueEnv.not_forall_f_pos` is that refutation in Lean.
It remains usable for strictly positive kernels and for positive *factors* of a density.
For a density, use the localized `affiliatedOn_iff_logSupermodularOn`, which assumes
positivity only on a sublattice `S` and concludes on `S`, or its environment-level form
`affiliatedOn_signalBox_iff_logSupermodularOn` at `S = E.signalBox`. -/
theorem affiliated_iff_logSupermodular {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ x, 0 < f x) :
    Affiliated f ↔ ∀ x y : Fin n → ℝ,
      Real.log (f x) + Real.log (f y) ≤
        Real.log (f (x ⊔ y)) + Real.log (f (x ⊓ y)) := by
  have key : ∀ x y : Fin n → ℝ,
      (Real.log (f x) + Real.log (f y) ≤
          Real.log (f (x ⊔ y)) + Real.log (f (x ⊓ y))) ↔
        f x * f y ≤ f (x ⊔ y) * f (x ⊓ y) := by
    intro x y
    rw [← Real.log_mul (hf x).ne' (hf y).ne', ← Real.log_mul (hf _).ne' (hf _).ne',
      Real.log_le_log_iff (mul_pos (hf x) (hf y)) (mul_pos (hf _) (hf _))]
  constructor
  · intro h x y
    exact (key x y).mpr (h x y)
  · intro h x y
    exact (key x y).mp (h x y)

/-! ### The global hypothesis is unsatisfiable for `SignalValueEnv` densities -/

/-- No `SignalValueEnv` with at least one bidder has a globally positive density: taking the
constant profile at `x_hi + 1` puts every coordinate outside `Set.Icc x_lo x_hi`, so
`f_support` forces the density to `0` there.

Consequently the hypothesis of `affiliated_iff_logSupermodular` can never be discharged at
`f = E.f`, and the localized `affiliatedOn_iff_logSupermodularOn` is the form to use. -/
theorem SignalValueEnv.not_forall_f_pos {n : ℕ} [NeZero n] (E : SignalValueEnv n) :
    ¬ ∀ X, 0 < E.f X := by
  intro h
  have hmem : ((fun _ : Fin n => E.x_hi + 1) (0 : Fin n)) ∉ Set.Icc E.x_lo E.x_hi := by
    simp only [Set.mem_Icc, not_and, not_le]
    intro _
    linarith
  exact (h _).ne' (E.f_support (fun _ => E.x_hi + 1) ⟨(0 : Fin n), hmem⟩)

/-! ### The localized (domain-restricted) form -/

/-- `AffiliatedOn f S`: the affiliation inequality of **Def 7.2** restricted to profiles
lying in `S`, `f (x ⊔ y) * f (x ⊓ y) ≥ f x * f y` for all `x, y ∈ S`.

This is the form a density can actually satisfy on the region where it is positive:
`Affiliated f` implies `AffiliatedOn f S` for every `S` (`Affiliated.affiliatedOn`), and
`AffiliatedOn f Set.univ` is `Affiliated f` (`affiliatedOn_univ_iff`). -/
def AffiliatedOn {n : ℕ} (f : (Fin n → ℝ) → ℝ) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, f (x ⊔ y) * f (x ⊓ y) ≥ f x * f y

/-- `Affiliated f` implies `AffiliatedOn f S` for every `S`. -/
theorem Affiliated.affiliatedOn {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Affiliated f)
    (S : Set (Fin n → ℝ)) : AffiliatedOn f S :=
  fun x _ y _ => hf x y

/-- `AffiliatedOn f Set.univ ↔ Affiliated f`. -/
theorem affiliatedOn_univ_iff {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
    AffiliatedOn f Set.univ ↔ Affiliated f :=
  ⟨fun h x y => h x (Set.mem_univ _) y (Set.mem_univ _), fun h => h.affiliatedOn _⟩

/-- **Def 7.2, logarithmic form, localized** (MTP₂ / log-supermodularity on a sublattice).
For a set `S` closed under the pointwise join and meet and a density positive **only on
`S`**, the affiliation inequality restricted to points of `S` is equivalent to
supermodularity of `log ∘ f` restricted to points of `S`:

`log (f x) + log (f y) ≤ log (f (x ⊔ y)) + log (f (x ⊓ y))` for all `x, y ∈ S`.

`IsSublattice S` is exactly what puts `x ⊔ y` and `x ⊓ y` back into `S`, so that all four
logarithms are logarithms of positive numbers; the proof is otherwise the proof of
`affiliated_iff_logSupermodular`, with membership side conditions.

Unlike the global `affiliated_iff_logSupermodular`, this statement is applicable to
`SignalValueEnv` densities: `E.signalBox` is a sublattice, and a density supported on the
box is positive there in the standard examples (see
`affiliatedOn_signalBox_iff_logSupermodularOn` and the applications in
`Auctionlib/Auction/Affiliation/Examples.lean`). -/
theorem affiliatedOn_iff_logSupermodularOn {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {S : Set (Fin n → ℝ)} (hS : IsSublattice S) (hf : ∀ x ∈ S, 0 < f x) :
    AffiliatedOn f S ↔ ∀ x ∈ S, ∀ y ∈ S,
      Real.log (f x) + Real.log (f y) ≤
        Real.log (f (x ⊔ y)) + Real.log (f (x ⊓ y)) := by
  have key : ∀ x ∈ S, ∀ y ∈ S,
      (Real.log (f x) + Real.log (f y) ≤
          Real.log (f (x ⊔ y)) + Real.log (f (x ⊓ y))) ↔
        f x * f y ≤ f (x ⊔ y) * f (x ⊓ y) := by
    intro x hx y hy
    have hx' := hf x hx
    have hy' := hf y hy
    have hsup := hf _ (hS.supClosed hx hy)
    have hinf := hf _ (hS.infClosed hx hy)
    rw [← Real.log_mul hx'.ne' hy'.ne', ← Real.log_mul hsup.ne' hinf.ne',
      Real.log_le_log_iff (mul_pos hx' hy') (mul_pos hsup hinf)]
  exact ⟨fun h x hx y hy => (key x hx y hy).mpr (h x hx y hy),
    fun h x hx y hy => (key x hx y hy).mp (h x hx y hy)⟩

/-- **The localized characterization at the signal box**, the environment-level form of
`affiliatedOn_iff_logSupermodularOn`. The caller supplies positivity of the density on
`E.signalBox` only — which, unlike global positivity, is compatible with
`SignalValueEnv.f_support` — and the sublattice hypothesis is discharged by
`SignalValueEnv.isSublattice_signalBox`. -/
theorem affiliatedOn_signalBox_iff_logSupermodularOn {n : ℕ} (E : SignalValueEnv n)
    (hpos : ∀ x ∈ E.signalBox, 0 < E.f x) :
    AffiliatedOn E.f E.signalBox ↔ ∀ x ∈ E.signalBox, ∀ y ∈ E.signalBox,
      Real.log (E.f x) + Real.log (E.f y) ≤
        Real.log (E.f (x ⊔ y)) + Real.log (E.f (x ⊓ y)) :=
  affiliatedOn_iff_logSupermodularOn E.isSublattice_signalBox hpos

end Auction.Affiliation
