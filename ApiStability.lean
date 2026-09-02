import Auctionlib

/-!
# API stability pins

This file pins the **exact statements** of the library's core theorems and
definitions. Each `example` below restates a public declaration's full type
and proves it by the declaration itself, so this file compiles if and only if
every pinned statement is unchanged (binder *names* are free to differ; the
hypotheses, conclusion, and implicitness are locked).

**The rule**: if your change turns this file red, the change alters a public
statement — an added hypothesis, a changed conclusion, a renamed or deleted
declaration. Per `CONTRIBUTING.md` that needs a design discussion first: open
an issue and get agreement before changing the statement. Do **not** silently
edit the pin to make it pass.

The file lives at the repository root (outside `Auctionlib/`) so that
`lake exe mk_all` never touches it, and is built as its own `lean_lib`
(`ApiStability`), listed in `defaultTargets` so a plain `lake build` checks it.
(It is deliberately a non-`module` file: it imports the mk_all-generated root
`Auctionlib`, which is itself a plain import list.)
-/

open MeasureTheory ProbabilityTheory

universe u v w

/-! ## BidderProblem — envelope theorem and Myerson lemmas -/

-- Envelope theorem, integral representation: U(v) = U(low) + ∫ q (Theorem 5.1)
example : ∀ (B : BidderProblem) [B.HasEnvelopeIC],
    ∀ v ∈ B.typeInterval, B.U v = B.U B.lowestType + ∫ (w : ℝ) in B.lowestType..v, B.q w :=
  @BidderProblem.integral_rep

-- Envelope theorem: interim utility is 1-Lipschitz on the type interval (Theorem 5.1)
example : ∀ (B : BidderProblem) [B.HasEnvelopeIC], LipschitzOnWith 1 B.U B.typeInterval :=
  @BidderProblem.lipschitz

-- Envelope theorem: interim winning probability is monotone (Theorem 5.1)
example : ∀ (B : BidderProblem) [B.HasEnvelopeIC], MonotoneOn B.q B.typeInterval :=
  @BidderProblem.q_monotoneOn

-- Myerson payment identity: cost(strategy(s)) = s·q(s) − U(low) − ∫ q (Lemma 5.2)
example : ∀ (B : BidderProblem) [B.HasTypeDeviationIC],
    ∀ s ∈ B.typeInterval,
      B.cost (B.strategy s)
        = s * B.q s - B.U B.lowestType - ∫ (ψ : ℝ) in B.lowestType..s, B.q ψ :=
  @BidderProblem.payment_identity

-- Myerson payment uniqueness: same q and U(low) force the same payments (Lemma 5.2)
example : ∀ (B : BidderProblem) [B.HasTypeDeviationIC],
    ∀ (B₂ : BidderProblem) [B₂.HasTypeDeviationIC],
      B.lowestType = B₂.lowestType → B.highestType = B₂.highestType → B.q = B₂.q →
        B.U B.lowestType = B₂.U B₂.lowestType →
          ∀ s ∈ B.typeInterval, B.cost (B.strategy s) = B₂.cost (B₂.strategy s) :=
  @BidderProblem.payment_unique

-- Myerson sufficiency: monotone q + payment identity ⇒ type-deviation IC
example : ∀ (B : BidderProblem),
    MonotoneOn B.q B.typeInterval →
      (∀ s ∈ B.typeInterval,
        B.cost (B.strategy s)
          = s * B.q s - B.U B.lowestType - ∫ (ψ : ℝ) in B.lowestType..s, B.q ψ) →
        B.HasTypeDeviationIC :=
  @BidderProblem.typeDeviationIC_of_monotone_q

/-! ## Auction — payment and revenue equivalence -/

-- Payment equivalence: two BIC auctions with matching q and boundary utility pay alike
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} (A : Auction Ω n) {Ω₂ : Type} [MeasureSpace Ω₂]
    [IsProbabilityMeasure (volume : Measure Ω₂)] (A₂ : Auction Ω₂ n)
    [A.rules.HasValidAllocation] [A₂.rules.HasValidAllocation] [A.BIC] [A₂.BIC] (i j : Fin n),
    A.θmin i = A₂.θmin j → A.θmax i = A₂.θmax j → A.q i = A₂.q j →
      A.U i (A.θmin i) = A₂.U j (A₂.θmin j) →
        ∀ {s : ℝ}, s ∈ A.interval i → A.p i s = A₂.p j s :=
  @Auction.payment_equivalence

-- Revenue Equivalence Theorem for symmetric IPV auctions (Theorem 6.4)
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [n.AtLeastTwo] (A : Auction Ω n) [A.IsSymmetricIPV]
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (volume : Measure Ω₂)]
    (A₂ : Auction Ω₂ n) [A₂.IsSymmetricIPV]
    [A.rules.HasValidAllocation] [A₂.rules.HasValidAllocation],
    (∀ i : Fin n, A.q i = A₂.q i) →
      A.lowestType = A₂.lowestType →
        A.highestType = A₂.highestType →
          (∀ i : Fin n, IdentDistrib (A.θ i) (A₂.θ i) volume volume) →
            ∀ [A.BIC] [A₂.BIC] [A.HasZeroLowestTypeUtility] [A₂.HasZeroLowestTypeUtility],
              (∀ i : Fin n, Measurable (A₂.p i)) →
                (∀ i : Fin n, Integrable (fun ω => A.p i (A.θ i ω)) volume) →
                  (∀ i : Fin n, Integrable (fun ω => A₂.p i (A₂.θ i ω)) volume) →
                    A.expectedRevenue = A₂.expectedRevenue :=
  @Auction.revenue_equivalence

-- Expected revenue = expected second-highest value for efficient auctions
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [n.AtLeastTwo] (A : Auction Ω n) [A.IsSymmetricIPV]
    [A.rules.HasValidAllocation] [A.rules.IsEfficient] [A.BIC] [A.HasZeroLowestTypeUtility],
    A.expectedRevenue = ∫ (a : Ω), A.S₂ a :=
  @Auction.total_revenue

/-! ## Affiliation (§7) -/

section Affiliation

-- Def 7.2 (affiliation) — definition pin: the exact unfolding of `Affiliated`
example {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Auction.Affiliation.Affiliated f
      ↔ ∀ x y : Fin n → ℝ, f (x ⊔ y) * f (x ⊓ y) ≥ f x * f y :=
  Iff.rfl

-- Remark 6: independent (factorized) densities are affiliated
example : ∀ {n : ℕ} {f : (Fin n → ℝ) → ℝ} {g : Fin n → ℝ → ℝ},
    Auction.Affiliation.Factors f g → Auction.Affiliation.Affiliated f :=
  @Auction.Affiliation.factors_affiliated

-- Affiliation ⇔ log-supermodularity for positive densities (Remark 5)
example : ∀ {n : ℕ} {f : (Fin n → ℝ) → ℝ},
    (∀ x : Fin n → ℝ, 0 < f x) →
      (Auction.Affiliation.Affiliated f ↔
        ∀ x y : Fin n → ℝ,
          Real.log (f x) + Real.log (f y) ≤ Real.log (f (x ⊔ y)) + Real.log (f (x ⊓ y))) :=
  @Auction.Affiliation.affiliated_iff_logSupermodular

-- FKG-style four-sum inequality for affiliated densities (§7, key lemma)
example : ∀ {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {S A B : Finset (Fin n → ℝ)},
    Auction.Affiliation.Affiliated f →
      (∀ x ∈ S, 0 < f x) → IsSublattice (S : Set (Fin n → ℝ)) → Monotone g →
        (∀ x ∈ S, 0 ≤ g x) → A ⊆ S → B ⊆ S →
          (∀ a ∈ A, ∀ b ∈ B, a ⊔ b ∈ B) → (∀ a ∈ A, ∀ b ∈ B, a ⊓ b ∈ A) →
            (∑ x ∈ A, g x * f x) * ∑ x ∈ B, f x ≤ (∑ x ∈ B, g x * f x) * ∑ x ∈ A, f x :=
  @Auction.Affiliation.sum_mul_sum_le_of_affiliated

-- Conditional expectations increase along the sup/inf ordering of events (§7)
example : ∀ {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {S A B : Finset (Fin n → ℝ)},
    Auction.Affiliation.Affiliated f →
      (∀ x ∈ S, 0 < f x) → IsSublattice (S : Set (Fin n → ℝ)) → Monotone g →
        A ⊆ S → B ⊆ S → A.Nonempty → B.Nonempty →
          (∀ a ∈ A, ∀ b ∈ B, a ⊔ b ∈ B) → (∀ a ∈ A, ∀ b ∈ B, a ⊓ b ∈ A) →
            Auction.Affiliation.condExpOn f g A ≤ Auction.Affiliation.condExpOn f g B :=
  @Auction.Affiliation.condExpOn_le_condExpOn_of_affiliated

-- Lemma 7.3: the sliced conditional expectation is monotone in the conditioning signal
example : ∀ {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {S : Finset (Fin n → ℝ)},
    Auction.Affiliation.Affiliated f →
      (∀ x ∈ S, 0 < f x) → IsSublattice (S : Set (Fin n → ℝ)) → Monotone g →
        ∀ i : Fin n,
          MonotoneOn (Auction.Affiliation.condExpSlice f g S i)
            ↑(Finset.image (fun x => x i) S) :=
  @Auction.Affiliation.monotoneOn_condExpSlice_of_affiliated

-- Winner's curse: conditioning on winning lowers the conditional expectation (§7)
example : ∀ {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {S : Finset (Fin n → ℝ)},
    Auction.Affiliation.Affiliated f →
      (∀ x ∈ S, 0 < f x) → IsSublattice (S : Set (Fin n → ℝ)) → Monotone g →
        (∀ x ∈ S, 0 ≤ g x) →
          ∀ (i : Fin n) (t : ℝ),
            (Auction.Affiliation.winningSlice S i t).Nonempty →
              Auction.Affiliation.condExpWinningSlice f g S i t
                ≤ Auction.Affiliation.condExpSlice f g S i t :=
  @Auction.Affiliation.condExpWinningSlice_le_condExpSlice_of_affiliated

end Affiliation

/-! ## All-purchase auctions -/

-- Proposition 6.13 (welfare decomposition): W* − W^C = L_Cournot + L_Contest
example : ∀ φbar c α B_ed WC : ℝ,
    AllPurchase.firstBestEditionSurplus φbar c α - WC
      = AllPurchase.cournotLoss φbar c α B_ed + AllPurchase.contestLoss φbar c α B_ed WC :=
  @AllPurchase.welfare_decomposition

-- Uniform all-pay bid (§9.6.3): b^{AP}(v) = (n−1)/n · vⁿ / v̄ⁿ⁻¹
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [NeZero n] [n.AtLeastTwo] (A : Auction Ω n) [A.HasIdenticalTypes] (vbar : ℝ),
    0 < vbar → A.lowestType = 0 → (∀ t ∈ Set.Icc (0 : ℝ) vbar, A.commonCDF t = t / vbar) →
      ∀ v ∈ Set.Icc (0 : ℝ) vbar,
        A.allPayBid v = ((n : ℝ) - 1) / (n : ℝ) * v ^ n / vbar ^ (n - 1) :=
  @Auction.allPayBid_uniform

/-! ## Game theory -/

-- Nash equilibrium — definition pin: the exact unfolding of `IsNashEquilibrium`
example {ι : Type u} {A : ι → Type v} {O : Type w} [DecidableEq ι]
    (G : GameTheory.Game A O) (P : GameTheory.PayoffStructure O ι) (a : (i : ι) → A i) :
    G.IsNashEquilibrium P a
      ↔ ∀ (i : ι) (s : A i),
          P.payoff i (G.outcome (Function.update a i s)) ≤ P.payoff i (G.outcome a) :=
  Iff.rfl

-- Nash existence: every finite game has a mixed-strategy Nash equilibrium
example : ∀ {ι : Type u} {A : ι → Type v} {O : Type w}
    (G : GameTheory.Game A O) (P : GameTheory.PayoffStructure O ι)
    [(i : ι) → MeasurableSpace (A i)] [MeasurableSpace O]
    [∀ i : ι, DiscreteMeasurableSpace (A i)] [DiscreteMeasurableSpace O]
    [G.Measurable] [Fintype ι] [DecidableEq ι] [(i : ι) → Finite (A i)]
    [∀ i : ι, Nonempty (A i)] [Finite O],
    ∃ a, G.toMixed.IsNashEquilibrium P.toExpected a :=
  @GameTheory.Game.exists_isNashEquilibrium_of_finite
