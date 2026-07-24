module

public import Auctionlib.Auction.Affiliation.MonotoneCondExp

/-! # Proposition 7.4 — Winner's curse (finite case)

This file proves the finite-support version of **Proposition 7.4
(Winner's curse)** from Section 7.

Fix a bidder `i` and a realized own signal `t`.  Inside a finite support
`S : Finset (Fin n → ℝ)`, compare the following two sets of signal profiles:

* the **own-signal slice**, consisting of the profiles `x ∈ S` with `x i = t`;
* the **winning slice**, consisting of those profiles in the own-signal slice
  for which `x j ≤ t` for every bidder `j`.

The second condition says that bidder `i`'s signal is a (not necessarily
unique) maximum, so ties count as wins.  For an affiliated density `f` and a
nondecreasing nonnegative value function `g`, the target theorem is

`E_f[g(X) | X_i = t, X_i = max_j X_j] ≤ E_f[g(X) | X_i = t]`.

The finite theorem assumes:

* `S` is closed under pointwise `⊔` and `⊓`;
* `f` is affiliated and strictly positive on `S`;
* `g` is monotone and nonnegative on `S`;
* the winning slice is nonempty.

The nonemptiness and positivity assumptions ensure that both conditional
averages have positive denominators.  The proof shows that the winning slice
is lattice-lower than the own-signal slice and applies
`condExpOn_le_condExpOn_of_affiliated_of_nonneg` from
`FiniteCondExp.lean`.  The own-signal conditional expectation is
`condExpSlice` from `MonotoneCondExp.lean`.  The proposition's additional
claim that the inequality is generically strict is outside this first finite
scope.
-/

@[expose] public section

namespace Auction.Affiliation

/-- The finite slice of signal profiles in `S` where bidder `i`'s own signal
equals `t`. -/
noncomputable def ownSignalSlice {n : ℕ} (S : Finset (Fin n → ℝ)) (i : Fin n) (t : ℝ) :
    Finset (Fin n → ℝ) :=
  S.filter fun x => x i = t

/-- The finite slice of signal profiles in `S` where bidder `i` has signal `t`
and wins: every bidder's signal is at most `t`.  In particular, another bidder
may also have signal `t`, so ties count as wins. -/
noncomputable def winningSlice {n : ℕ} (S : Finset (Fin n → ℝ)) (i : Fin n) (t : ℝ) :
    Finset (Fin n → ℝ) :=
  (ownSignalSlice S i t).filter fun x => ∀ j, x j ≤ t

/-- The discrete conditional expectation
`E_f[g(X) | X_i = t, X_i = max_j X_j]`: the `f`-weighted average of `g` over
`winningSlice S i t`.

As with `condExpSlice`, division by zero has Lean's usual value `0`.  The
finite winner's-curse theorem will assume that the winning slice is nonempty
and that `f` is positive on `S`, ensuring that this denominator is positive. -/
noncomputable def condExpWinningSlice {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (S : Finset (Fin n → ℝ)) (i : Fin n) (t : ℝ) : ℝ :=
  condExpOn f g (winningSlice S i t)

/-! ### Lattice bookkeeping for the winning and own-signal slices -/

/-- Membership in `ownSignalSlice S i t` means membership in `S` together
with the coordinate equality `x i = t`. -/
@[simp] theorem mem_ownSignalSlice {n : ℕ} {S : Finset (Fin n → ℝ)}
    {i : Fin n} {t : ℝ} {x : Fin n → ℝ} :
    x ∈ ownSignalSlice S i t ↔ x ∈ S ∧ x i = t := by
  simp [ownSignalSlice]

/-- Membership in `winningSlice S i t` means membership in the own-signal
slice together with the condition that every signal is at most `t`. -/
@[simp] theorem mem_winningSlice {n : ℕ} {S : Finset (Fin n → ℝ)}
    {i : Fin n} {t : ℝ} {x : Fin n → ℝ} :
    x ∈ winningSlice S i t ↔ (x ∈ S ∧ x i = t) ∧ ∀ j, x j ≤ t := by
  simp [winningSlice]

/-- The own-signal slice is a subset of the original finite support. -/
theorem ownSignalSlice_subset {n : ℕ} {S : Finset (Fin n → ℝ)}
    {i : Fin n} {t : ℝ} : ownSignalSlice S i t ⊆ S := by
  intro x hx
  exact (mem_ownSignalSlice.mp hx).1

/-- The winning slice is a subset of the original finite support. -/
theorem winningSlice_subset {n : ℕ} {S : Finset (Fin n → ℝ)}
    {i : Fin n} {t : ℝ} : winningSlice S i t ⊆ S := by
  intro x hx
  exact (mem_winningSlice.mp hx).1.1

/-- Every profile in the winning slice also belongs to the full own-signal
slice.  Winning adds restrictions on the rival signals but does not change
the bidder's own-signal condition. -/
theorem winningSlice_subset_ownSignalSlice {n : ℕ}
    {S : Finset (Fin n → ℝ)} {i : Fin n} {t : ℝ} :
    winningSlice S i t ⊆ ownSignalSlice S i t := by
  intro x hx
  have hxown : x ∈ S ∧ x i = t :=
    (mem_winningSlice.mp hx).1
  exact mem_ownSignalSlice.mpr hxown

/-- If `a` is in the winning slice and `b` is in the own-signal slice, then
their pointwise supremum is in the own-signal slice.  Sublattice closure keeps
`a ⊔ b` in `S`, while its `i`th coordinate is `t ⊔ t = t`. -/
theorem sup_mem_ownSignalSlice {n : ℕ} {S : Finset (Fin n → ℝ)}
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    {i : Fin n} {t : ℝ} {a b : Fin n → ℝ}
    (ha : a ∈ winningSlice S i t) (hb : b ∈ ownSignalSlice S i t) :
    a ⊔ b ∈ ownSignalSlice S i t := by
  obtain ⟨⟨haS, hai⟩, _⟩ := mem_winningSlice.mp ha
  obtain ⟨hbS, hbi⟩ := mem_ownSignalSlice.mp hb
  refine mem_ownSignalSlice.mpr ⟨?_, ?_⟩
  · exact Finset.mem_coe.1
      (hsub.supClosed (Finset.mem_coe.2 haS) (Finset.mem_coe.2 hbS))
  · simp only [Pi.sup_apply, hai, hbi, sup_idem]

/-- If `a` is in the winning slice and `b` is in the own-signal slice, then
their pointwise infimum is still in the winning slice.  Its own coordinate is
`t ⊓ t = t`, and every other coordinate is at most the corresponding
coordinate of the already-winning profile `a`, hence at most `t`. -/
theorem inf_mem_winningSlice {n : ℕ} {S : Finset (Fin n → ℝ)}
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    {i : Fin n} {t : ℝ} {a b : Fin n → ℝ}
    (ha : a ∈ winningSlice S i t) (hb : b ∈ ownSignalSlice S i t) :
    a ⊓ b ∈ winningSlice S i t := by
  obtain ⟨⟨haS, hai⟩, hawin⟩ := mem_winningSlice.mp ha
  obtain ⟨hbS, hbi⟩ := mem_ownSignalSlice.mp hb
  refine mem_winningSlice.mpr ⟨⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_coe.1
      (hsub.infClosed (Finset.mem_coe.2 haS) (Finset.mem_coe.2 hbS))
  · simp only [Pi.inf_apply, hai, hbi, inf_idem]
  · intro j
    rw [Pi.inf_apply]
    exact le_trans inf_le_left (hawin j)

/-! ### The affiliation comparison before normalization -/

/-- The cross-multiplied weighted-sum comparison underlying the finite
winner's-curse inequality.  For an affiliated density `f` positive on the
finite sublattice `S` and a monotone nonnegative value function `g`, the
`f`-weighted average numerator over the winning slice, multiplied by the
mass of the full own-signal slice, is at most the reverse product.

This is exactly `sum_mul_sum_le_of_affiliated` with `A` equal to the winning
slice and `B` equal to the own-signal slice.  No nonemptiness assumption is
needed until the products are divided by the two slice masses. -/
theorem sum_mul_sum_le_winningSlice_of_affiliated {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {S : Finset (Fin n → ℝ)}
    (hf : Affiliated f) (hpos : ∀ x ∈ S, 0 < f x)
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    (hg : Monotone g) (hg0 : ∀ x ∈ S, 0 ≤ g x)
    (i : Fin n) (t : ℝ) :
    (∑ x ∈ winningSlice S i t, g x * f x) *
        (∑ x ∈ ownSignalSlice S i t, f x) ≤
      (∑ x ∈ ownSignalSlice S i t, g x * f x) *
        (∑ x ∈ winningSlice S i t, f x) := by
  exact sum_mul_sum_le_of_affiliated hf hpos hsub hg hg0
    winningSlice_subset ownSignalSlice_subset
    (fun _ ha _ hb => sup_mem_ownSignalSlice hsub ha hb)
    (fun _ ha _ hb => inf_mem_winningSlice hsub ha hb)

/-! ### Proposition 7.4 — the normalized finite winner's-curse inequality -/

/-- **Proposition 7.4 (Winner's curse), finite case.** Let `f` be an
affiliated density that is positive on the finite sublattice `S`, and let `g`
be a nondecreasing nonnegative value function.  Conditional on bidder `i`
having signal `t`, additionally learning that bidder `i` wins weakly lowers
the conditional expected value:

`E_f[g(X) | X_i = t, X_i = max_j X_j] ≤ E_f[g(X) | X_i = t]`.

The winning slice is assumed nonempty so that conditioning on winning is
meaningful.  Since `f` is positive on `S`, this makes the winning-slice mass
positive.  The same winning profile also belongs to the full own-signal
slice, so that slice has positive mass as well.

The winning slice is lattice-lower than the own-signal slice:
`sup_mem_ownSignalSlice` sends their pointwise supremum to the own-signal
slice, while `inf_mem_winningSlice` sends their pointwise infimum back to the
winning slice.  The result is therefore a direct specialization of
`condExpOn_le_condExpOn_of_affiliated_of_nonneg`. -/
theorem condExpWinningSlice_le_condExpSlice_of_affiliated {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {S : Finset (Fin n → ℝ)}
    (hf : Affiliated f) (hpos : ∀ x ∈ S, 0 < f x)
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    (hg : Monotone g) (hg0 : ∀ x ∈ S, 0 ≤ g x)
    (i : Fin n) (t : ℝ) (hwin : (winningSlice S i t).Nonempty) :
    condExpWinningSlice f g S i t ≤ condExpSlice f g S i t := by
  -- A winning profile is also an own-signal profile, so nonemptiness of the
  -- winning slice implies nonemptiness of the larger own-signal slice.
  have hwin_subset_own : winningSlice S i t ⊆ ownSignalSlice S i t :=
    winningSlice_subset_ownSignalSlice
  have hown_nonempty : (ownSignalSlice S i t).Nonempty :=
    hwin.mono hwin_subset_own

  -- Both slices lie in `S`, and their pairwise supremum and infimum return
  -- to the upper and lower slices, respectively.
  have hwin_subset : winningSlice S i t ⊆ S :=
    winningSlice_subset
  have hown_subset : ownSignalSlice S i t ⊆ S :=
    ownSignalSlice_subset
  have hsupAB : ∀ a ∈ winningSlice S i t, ∀ b ∈ ownSignalSlice S i t,
      a ⊔ b ∈ ownSignalSlice S i t := by
    intro a ha b hb
    exact sup_mem_ownSignalSlice hsub ha hb
  have hinfAB : ∀ a ∈ winningSlice S i t, ∀ b ∈ ownSignalSlice S i t,
      a ⊓ b ∈ winningSlice S i t := by
    intro a ha b hb
    exact inf_mem_winningSlice hsub ha hb

  -- Positivity of `f` and nonemptiness of the two slices give them positive
  -- total mass inside the generic theorem.
  change
    condExpOn f g (winningSlice S i t) ≤
      condExpOn f g (ownSignalSlice S i t)
  exact condExpOn_le_condExpOn_of_affiliated_of_nonneg
    hf hpos hsub hg hg0
    hwin_subset hown_subset hwin hown_nonempty hsupAB hinfAB

/-! ### Signal/value environment form -/

/-- **Proposition 7.4 (Winner's curse), finite environment form.** In a
`SignalValueEnv` with affiliated signals, bidder `i`'s expected value
conditional on having signal `t` and winning is at most the expected value
conditional only on having signal `t`.

This is the preceding finite theorem with `g = E.v i`.  The environment fields
`v_mono` and `v_nonneg` supply exactly the monotonicity and nonnegativity
assumptions needed there.  Although Proposition 7.4 is stated for a
pure-common-value environment, this inequality uses only these two properties
of bidder `i`'s value, so the formal statement applies to the more general
interdependent-value environment represented by `SignalValueEnv`.

The additional hypothesis that `E.f` is strictly positive on `S` strengthens
the environment's built-in nonnegativity just where it is needed to normalize
the two finite conditional expectations. -/
theorem SignalValueEnv.condExpWinningSlice_le_condExpSlice {n : ℕ}
    (E : SignalValueEnv n) {S : Finset (Fin n → ℝ)}
    (haff : HasAffiliatedSignals E) (hpos : ∀ x ∈ S, 0 < E.f x)
    (hsub : IsSublattice (↑S : Set (Fin n → ℝ)))
    (i : Fin n) (t : ℝ) (hwin : (winningSlice S i t).Nonempty) :
    condExpWinningSlice E.f (E.v i) S i t ≤
      condExpSlice E.f (E.v i) S i t := by
  exact condExpWinningSlice_le_condExpSlice_of_affiliated
    haff hpos hsub (E.v_mono i) (fun x _ => E.v_nonneg i x) i t hwin

end Auction.Affiliation
