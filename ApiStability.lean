import MathEconLib

/-!
# API stability pins

This file pins the **exact statements** of the library's core theorems and definitions. Each
`example` below restates a public declaration's full type and proves it by the declaration itself,
so this file compiles if and only if every pinned statement is unchanged (binder *names* are free
to differ; the hypotheses, conclusion, and implicitness are locked).

**The rule**: if your change turns this file red, the change alters a public statement — an added
hypothesis, a changed conclusion, a renamed or deleted declaration. Per `CONTRIBUTING.md` that
needs a design discussion first: open an issue and get agreement before changing the statement. Do
**not** silently edit the pin to make it pass.

The file lives at the repository root (outside `MathEconLib/`) so that `lake exe mk_all` never
touches it, and is built as its own `lean_lib` (`ApiStability`), listed in `defaultTargets` so a
plain `lake build` checks it. (It is deliberately a non-`module` file: it imports the
mk_all-generated root `MathEconLib`, which is itself a plain import list.)
-/

open MeasureTheory ProbabilityTheory
open MathEconLib.Mechanism.Auctions

universe u v w uI uA uB uC uΘ uO

/-! ## Mechanism core — carriers, report maps, and transfer signs -/

section MechanismCore

open MathEconLib.Mechanism

-- Mechanisms allow agent-specific actions and an independent outcome universe.
example : (I : Type uI) → (I → Type uA) → Type uO → Type (max uI uA uO) :=
  @MathEconLib.Mechanism

example : ∀ {I : Type uI} {A : I → Type uA} {O : Type uO},
    (Profile A → O) → ((i : I) → Profile A → ℝ) → MathEconLib.Mechanism I A O :=
  @MathEconLib.Mechanism.mk

example : ∀ {I : Type uI} {A : I → Type uA} {O : Type uO},
    MathEconLib.Mechanism I A O → Profile A → O :=
  @MathEconLib.Mechanism.outcome

example : ∀ {I : Type uI} {A : I → Type uA} {O : Type uO},
    MathEconLib.Mechanism I A O → (i : I) → Profile A → ℝ :=
  @MathEconLib.Mechanism.transfer

example : (I : Type uI) → (I → Type uΘ) → Type uO → Type (max uI uΘ uO) :=
  @DirectMechanism

-- Payments are amounts paid by agents; transfers are amounts received by agents.
example : ∀ {I : Type uI} {A : I → Type uA} {O : Type uO},
    MathEconLib.Mechanism I A O → (i : I) → Profile A → ℝ :=
  @payment

example : ∀ {I : Type uI} {A : I → Type uA} {O : Type uO}
    (M : MathEconLib.Mechanism I A O) (i : I) (a : Profile A),
    M.payment i a = -M.transfer i a :=
  @payment_eq_neg_transfer

example : ∀ {I : Type uI} {A : I → Type uA} {O : Type uO},
    MathEconLib.Mechanism I A O → [Fintype I] → Profile A → ℝ :=
  @revenue

example : ∀ {I : Type uI} {A : I → Type uA} {O : Type uO}
    (M : MathEconLib.Mechanism I A O) [Fintype I] (a : Profile A),
    M.revenue a = -∑ i, M.transfer i a :=
  @revenue_eq_neg_sum_transfer

example : ∀ {I : Type uI} {A : I → Type uA} {O : Type uO}
    (M : MathEconLib.Mechanism I A O) [Fintype I] (a : Profile A),
    M.revenue a = ∑ i, M.payment i a :=
  @revenue_eq_sum_payment

-- Report maps preserve outcomes and transfers and compose pointwise.
example : ∀ {I : Type uI} {A : I → Type uA} {B : I → Type uB} {O : Type uO},
    MathEconLib.Mechanism I A O → (∀ i, B i → A i) → MathEconLib.Mechanism I B O :=
  @comap

example : ∀ {I : Type uI} {A : I → Type uA} {B : I → Type uB} {O : Type uO}
    (M : MathEconLib.Mechanism I A O) (σ : ∀ i, B i → A i) (b : Profile B),
    (M.comap σ).outcome b = M.outcome (fun i => σ i (b i)) :=
  @outcome_comap

example : ∀ {I : Type uI} {A : I → Type uA} {B : I → Type uB} {O : Type uO}
    (M : MathEconLib.Mechanism I A O) (σ : ∀ i, B i → A i) (i : I) (b : Profile B),
    (M.comap σ).transfer i b = M.transfer i (fun j => σ j (b j)) :=
  @transfer_comap

example : ∀ {I : Type uI} {A : I → Type uA} {O : Type uO}
    (M : MathEconLib.Mechanism I A O), M.comap (fun _ => id) = M :=
  @comap_id

example : ∀ {I : Type uI} {A : I → Type uA} {B : I → Type uB} {C : I → Type uC}
    {O : Type uO} (M : MathEconLib.Mechanism I A O)
    (σ : ∀ i, B i → A i) (τ : ∀ i, C i → B i),
    (M.comap σ).comap τ = M.comap (fun i => σ i ∘ τ i) :=
  @comap_comp

-- Values use true types, independently of the mechanism's action spaces.
example : (I : Type uI) → (I → Type uΘ) → Type uO → Type (max uI uΘ uO) :=
  @QuasilinearEnvironment

example : ∀ {I : Type uI} {Θ : I → Type uΘ} {O : Type uO},
    ((i : I) → Profile Θ → O → ℝ) → QuasilinearEnvironment I Θ O :=
  @QuasilinearEnvironment.mk

example : ∀ {I : Type uI} {Θ : I → Type uΘ} {O : Type uO},
    QuasilinearEnvironment I Θ O → (i : I) → Profile Θ → O → ℝ :=
  @QuasilinearEnvironment.value

example : ∀ {I : Type uI} {Θ : I → Type uΘ} {O : Type uO},
    ((i : I) → Θ i → O → ℝ) → QuasilinearEnvironment I Θ O :=
  @QuasilinearEnvironment.ofPrivate

example : ∀ {I : Type uI} {Θ : I → Type uΘ} {O : Type uO}
    (v : (i : I) → Θ i → O → ℝ), (QuasilinearEnvironment.ofPrivate v).IsPrivateValues :=
  @QuasilinearEnvironment.isPrivateValues_ofPrivate

example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {O : Type uO},
    QuasilinearEnvironment I Θ O → MathEconLib.Mechanism I A O →
      (i : I) → Profile Θ → Profile A → ℝ :=
  @QuasilinearEnvironment.utility

example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {O : Type uO}
    (E : QuasilinearEnvironment I Θ O) (M : MathEconLib.Mechanism I A O)
    (i : I) (θ : Profile Θ) (a : Profile A),
    E.utility M i θ a = E.value i θ (M.outcome a) + M.transfer i a :=
  @QuasilinearEnvironment.utility_eq_value_add_transfer

example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {O : Type uO}
    (E : QuasilinearEnvironment I Θ O) (M : MathEconLib.Mechanism I A O)
    (i : I) (θ : Profile Θ) (a : Profile A),
    E.utility M i θ a = E.value i θ (M.outcome a) - M.payment i a :=
  @QuasilinearEnvironment.utility_eq_value_sub_payment

end MechanismCore

/-! ## MathEconLib.BidderProblem — envelope theorem and Myerson lemmas -/

-- Envelope theorem, integral representation: U(v) = U(low) + ∫ q (Theorem 5.1)
example : ∀ (B : MathEconLib.BidderProblem) [B.HasEnvelopeIC],
    ∀ v ∈ B.typeInterval, B.U v = B.U B.lowestType + ∫ (w : ℝ) in B.lowestType..v, B.q w :=
  @MathEconLib.BidderProblem.integral_rep

-- Envelope theorem: interim utility is 1-Lipschitz on the type interval (Theorem 5.1)
example : ∀ (B : MathEconLib.BidderProblem) [B.HasEnvelopeIC],
    LipschitzOnWith 1 B.U B.typeInterval :=
  @MathEconLib.BidderProblem.lipschitz

-- Envelope theorem: interim winning probability is monotone (Theorem 5.1)
example : ∀ (B : MathEconLib.BidderProblem) [B.HasEnvelopeIC], MonotoneOn B.q B.typeInterval :=
  @MathEconLib.BidderProblem.q_monotoneOn

-- Envelope theorem: interim utility has derivative q almost everywhere on the type interval.
example : ∀ (B : MathEconLib.BidderProblem) [B.HasEnvelopeIC],
    ∀ᵐ s ∂volume.restrict B.typeInterval, HasDerivAt B.U (B.q s) s :=
  @MathEconLib.BidderProblem.aeDifferentiable

-- Myerson payment identity: cost(strategy(s)) = s·q(s) − U(low) − ∫ q (Lemma 5.2)
example : ∀ (B : MathEconLib.BidderProblem) [B.HasTypeDeviationIC],
    ∀ s ∈ B.typeInterval,
      B.cost (B.strategy s)
        = s * B.q s - B.U B.lowestType - ∫ (ψ : ℝ) in B.lowestType..s, B.q ψ :=
  @MathEconLib.BidderProblem.payment_identity

-- Myerson payment uniqueness: same q and U(low) force the same payments (Lemma 5.2)
example : ∀ (B : MathEconLib.BidderProblem) [B.HasTypeDeviationIC],
    ∀ (B₂ : MathEconLib.BidderProblem) [B₂.HasTypeDeviationIC],
      B.lowestType = B₂.lowestType → B.highestType = B₂.highestType → B.q = B₂.q →
        B.U B.lowestType = B₂.U B₂.lowestType →
          ∀ s ∈ B.typeInterval, B.cost (B.strategy s) = B₂.cost (B₂.strategy s) :=
  @MathEconLib.BidderProblem.payment_unique

-- Myerson sufficiency: monotone q + payment identity ⇒ type-deviation IC
example : ∀ (B : MathEconLib.BidderProblem),
    MonotoneOn B.q B.typeInterval →
      (∀ s ∈ B.typeInterval,
        B.cost (B.strategy s)
          = s * B.q s - B.U B.lowestType - ∫ (ψ : ℝ) in B.lowestType..s, B.q ψ) →
        B.HasTypeDeviationIC :=
  @MathEconLib.BidderProblem.typeDeviationIC_of_monotone_q

/-! ## MathEconLib.Auction — payment and revenue equivalence -/

-- Truthful opponents give winning probability F(s)^(n−1) under strict-highest-bid allocation.
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [NeZero n] (A : MathEconLib.Auction Ω n)
    [A.HasIndependentTypes] [A.HasIdenticalTypes] [A.HasAtomlessTypes]
    (_ : UsesStrictHighestBidAllocation A.rules (fun o i ↦ o i)) (i : Fin n) (s : ℝ),
    A.q i s = A.commonCDF s ^ (n - 1) :=
  @MathEconLib.Auction.q_eq_pow

-- Strict monotonicity retains density, regularity, and universal IC over nonnegative bids.
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [NeZero n] (A : MathEconLib.Auction Ω n) [A.HasIdenticalTypes]
    [A.HasPosDensity] [n.AtLeastTwo] [A.HasIndependentTypes] [A.HasBoundedTypes]
    [A.HasAtomlessTypes] (halloc : IsUnitIntervalAllocation A.rules (fun o i ↦ o i))
    (_ : UsesStrictHighestBidAllocation A.rules (fun o i ↦ o i))
    {σ : ℝ → ℝ} (_ : Measurable σ) (i : Fin n) (_ : 0 ≤ A.lowestType)
    (_ : (A.toBidderProblem halloc σ i).IsRegular)
    (_ : (A.toBidderProblem halloc σ i).HasUniversalIC (Set.Ici 0)),
    StrictMonoOn σ (Set.Icc A.lowestType A.highestType) :=
  @MathEconLib.Auction.strictMonotonicity

-- Payment equivalence: two BIC auctions with matching q and boundary utility pay alike
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} (A : MathEconLib.Auction Ω n) {Ω₂ : Type} [MeasureSpace Ω₂]
    [IsProbabilityMeasure (volume : Measure Ω₂)] (A₂ : MathEconLib.Auction Ω₂ n)
    (_ : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (_ : IsUnitIntervalAllocation A₂.rules (fun o i => o i)) [A.BIC] [A₂.BIC] (i j : Fin n),
    A.θmin i = A₂.θmin j → A.θmax i = A₂.θmax j → A.q i = A₂.q j →
      A.U i (A.θmin i) = A₂.U j (A₂.θmin j) →
        ∀ {s : ℝ}, s ∈ A.interval i → A.p i s = A₂.p j s :=
  @MathEconLib.Auction.payment_equivalence

-- Revenue Equivalence Theorem for symmetric IPV auctions (Theorem 6.4)
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [n.AtLeastTwo] (A : MathEconLib.Auction Ω n) [A.IsSymmetricIPV]
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (volume : Measure Ω₂)]
    (A₂ : MathEconLib.Auction Ω₂ n) [A₂.IsSymmetricIPV]
    (_ : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (_ : IsUnitIntervalAllocation A₂.rules (fun o i => o i)),
    (∀ i : Fin n, A.q i = A₂.q i) →
      A.lowestType = A₂.lowestType →
        A.highestType = A₂.highestType →
          (∀ i : Fin n, IdentDistrib (A.θ i) (A₂.θ i) volume volume) →
            ∀ [A.BIC] [A₂.BIC] [A.HasZeroLowestTypeUtility] [A₂.HasZeroLowestTypeUtility],
              (∀ i : Fin n, Measurable (A₂.p i)) →
                (∀ i : Fin n, Integrable (fun ω => A.p i (A.θ i ω)) volume) →
                  (∀ i : Fin n, Integrable (fun ω => A₂.p i (A₂.θ i ω)) volume) →
                    A.expectedRevenue = A₂.expectedRevenue :=
  @MathEconLib.Auction.revenue_equivalence

-- Strict-highest-bid allocation already supplies the unit-interval allocation bound.
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [n.AtLeastTwo] (A : MathEconLib.Auction Ω n) [A.IsSymmetricIPV]
    (_ : UsesStrictHighestBidAllocation A.rules (fun o i => o i))
    [A.BIC] [A.HasZeroLowestTypeUtility] (i : Fin n) {s : ℝ},
    s ∈ A.interval i →
      A.p i s = s * A.commonCDF s ^ (n - 1) -
        ∫ ψ in A.lowestType..s, A.commonCDF ψ ^ (n - 1) :=
  @MathEconLib.Auction.payment_formula_strictHighestBid

-- Expected revenue = expected second-highest value for strict-highest-bid auctions
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [n.AtLeastTwo] (A : MathEconLib.Auction Ω n) [A.IsSymmetricIPV]
    (_ : UsesStrictHighestBidAllocation A.rules (fun o i => o i))
    [A.BIC] [A.HasZeroLowestTypeUtility],
    A.expectedRevenue = ∫ (a : Ω), A.S₂ a :=
  @MathEconLib.Auction.total_revenue

/-! ## Affiliation (§7) -/

section Affiliation

-- Def 7.2 (affiliation) — definition pin: the exact unfolding of `Affiliated`
example {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    MathEconLib.Auction.Affiliation.Affiliated f
      ↔ ∀ x y : Fin n → ℝ, f (x ⊔ y) * f (x ⊓ y) ≥ f x * f y :=
  Iff.rfl

-- Remark 6: independent (factorized) densities are affiliated
example : ∀ {n : ℕ} {f : (Fin n → ℝ) → ℝ} {g : Fin n → ℝ → ℝ},
    MathEconLib.Auction.Affiliation.Factors f g → MathEconLib.Auction.Affiliation.Affiliated f :=
  @MathEconLib.Auction.Affiliation.factors_affiliated

-- Affiliation ⇔ log-supermodularity for positive densities (Remark 5)
example : ∀ {n : ℕ} {f : (Fin n → ℝ) → ℝ},
    (∀ x : Fin n → ℝ, 0 < f x) →
      (MathEconLib.Auction.Affiliation.Affiliated f ↔
        ∀ x y : Fin n → ℝ,
          Real.log (f x) + Real.log (f y) ≤ Real.log (f (x ⊔ y)) + Real.log (f (x ⊓ y))) :=
  @MathEconLib.Auction.Affiliation.affiliated_iff_logSupermodular

-- FKG-style four-sum inequality for affiliated densities (§7, key lemma)
example : ∀ {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {S A B : Finset (Fin n → ℝ)},
    MathEconLib.Auction.Affiliation.Affiliated f →
      (∀ x ∈ S, 0 < f x) → IsSublattice (S : Set (Fin n → ℝ)) → Monotone g →
        (∀ x ∈ S, 0 ≤ g x) → A ⊆ S → B ⊆ S →
          (∀ a ∈ A, ∀ b ∈ B, a ⊔ b ∈ B) →
            (∀ a ∈ A, ∀ b ∈ B, a ⊓ b ∈ A) →
              (∑ x ∈ A, g x * f x) * ∑ x ∈ B, f x ≤
                (∑ x ∈ B, g x * f x) * ∑ x ∈ A, f x :=
  @MathEconLib.Auction.Affiliation.sum_mul_sum_le_of_affiliated

-- Conditional expectations increase along the sup/inf ordering of events (§7)
example : ∀ {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {S A B : Finset (Fin n → ℝ)},
    MathEconLib.Auction.Affiliation.Affiliated f →
      (∀ x ∈ S, 0 < f x) → IsSublattice (S : Set (Fin n → ℝ)) → Monotone g →
        A ⊆ S → B ⊆ S → A.Nonempty → B.Nonempty →
          (∀ a ∈ A, ∀ b ∈ B, a ⊔ b ∈ B) →
            (∀ a ∈ A, ∀ b ∈ B, a ⊓ b ∈ A) →
              MathEconLib.Auction.Affiliation.condExpOn f g A ≤
                MathEconLib.Auction.Affiliation.condExpOn f g B :=
  @MathEconLib.Auction.Affiliation.condExpOn_le_condExpOn_of_affiliated

-- Lemma 7.3: the sliced conditional expectation is monotone in the conditioning signal
example : ∀ {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {S : Finset (Fin n → ℝ)},
    MathEconLib.Auction.Affiliation.Affiliated f →
      (∀ x ∈ S, 0 < f x) → IsSublattice (S : Set (Fin n → ℝ)) → Monotone g →
        ∀ i : Fin n,
          MonotoneOn (MathEconLib.Auction.Affiliation.condExpSlice f g S i)
            ↑(Finset.image (fun x => x i) S) :=
  @MathEconLib.Auction.Affiliation.monotoneOn_condExpSlice_of_affiliated

-- Winner's curse: conditioning on winning lowers the conditional expectation (§7)
example : ∀ {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {S : Finset (Fin n → ℝ)},
    MathEconLib.Auction.Affiliation.Affiliated f →
      (∀ x ∈ S, 0 < f x) → IsSublattice (S : Set (Fin n → ℝ)) → Monotone g →
        (∀ x ∈ S, 0 ≤ g x) →
          ∀ (i : Fin n) (t : ℝ),
            (MathEconLib.Auction.Affiliation.winningSlice S i t).Nonempty →
              MathEconLib.Auction.Affiliation.condExpWinningSlice f g S i t
                ≤ MathEconLib.Auction.Affiliation.condExpSlice f g S i t :=
  @MathEconLib.Auction.Affiliation.condExpWinningSlice_le_condExpSlice_of_affiliated

end Affiliation

/-! ## All-purchase auctions -/

-- Revenue decomposition keeps every IC, integrability, and boundary-utility hypothesis.
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [NeZero n] (A : MathEconLib.Auction Ω n)
    (spec : AllPurchaseSpec A.rules (fun o i ↦ o i)) [A.HasIdenticalTypes]
    [A.HasIndependentTypes] [A.HasBoundedTypes] [A.HasAtomlessTypes]
    (β : ℝ → ℝ) (_ : Measurable β)
    (_ : StrictMonoOn β (Set.Icc A.lowestType A.highestType))
    (_ : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (_ : ∀ i, Integrable (fun ω ↦ A.rules.payment i (fun j ↦ β (A.θ j ω))) volume)
    (_ : Integrable (fun ω ↦ A.aggregateBid β ω * spec.φ (A.aggregateBid β ω)) volume)
    (_ : Measurable A.allPayBid)
    (_ : ∀ i, Integrable (fun ω ↦ A.allPayBid (A.θ i ω)) volume)
    (_ : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).U
      (A.toBidderProblem spec.isUnitIntervalAllocation β i).lowestType =
        A.lowestTypeUtility spec.isUnitIntervalAllocation β),
    A.sellerGrossRevenue spec β =
      n * A.expectedAllPayBid - n * A.lowestTypeUtility spec.isUnitIntervalAllocation β +
        A.expectedEditionValue spec β :=
  @MathEconLib.Auction.revenue_decomposition

-- Boundary form additionally requires zero lowest-type utility.
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [NeZero n] (A : MathEconLib.Auction Ω n)
    (spec : AllPurchaseSpec A.rules (fun o i ↦ o i)) [A.HasIdenticalTypes]
    [A.HasIndependentTypes] [A.HasBoundedTypes] [A.HasAtomlessTypes]
    (β : ℝ → ℝ) (_ : Measurable β)
    (_ : StrictMonoOn β (Set.Icc A.lowestType A.highestType))
    (_ : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (_ : ∀ i, Integrable (fun ω ↦ A.rules.payment i (fun j ↦ β (A.θ j ω))) volume)
    (_ : Integrable (fun ω ↦ A.aggregateBid β ω * spec.φ (A.aggregateBid β ω)) volume)
    (_ : Measurable A.allPayBid)
    (_ : ∀ i, Integrable (fun ω ↦ A.allPayBid (A.θ i ω)) volume)
    (_ : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).U
      (A.toBidderProblem spec.isUnitIntervalAllocation β i).lowestType =
        A.lowestTypeUtility spec.isUnitIntervalAllocation β)
    (_ : A.lowestTypeUtility spec.isUnitIntervalAllocation β = 0),
    A.sellerGrossRevenue spec β = n * A.expectedAllPayBid + A.expectedEditionValue spec β :=
  @MathEconLib.Auction.revenue_decomposition_boundary

-- Bundling gain is a profit-difference identity, with no positivity conclusion.
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [NeZero n] (A : MathEconLib.Auction Ω n)
    (spec : AllPurchaseSpec A.rules (fun o i ↦ o i)) [A.HasIdenticalTypes]
    [A.HasIndependentTypes] [A.HasBoundedTypes] [A.HasAtomlessTypes]
    (β : ℝ → ℝ) (_ : Measurable β)
    (_ : StrictMonoOn β (Set.Icc A.lowestType A.highestType))
    (_ : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (_ : ∀ i, Integrable (fun ω ↦ A.rules.payment i (fun j ↦ β (A.θ j ω))) volume)
    (_ : Integrable (fun ω ↦ A.aggregateBid β ω * spec.φ (A.aggregateBid β ω)) volume)
    (_ : Measurable A.allPayBid)
    (_ : ∀ i, Integrable (fun ω ↦ A.allPayBid (A.θ i ω)) volume)
    (_ : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).U
      (A.toBidderProblem spec.isUnitIntervalAllocation β i).lowestType =
        A.lowestTypeUtility spec.isUnitIntervalAllocation β)
    (_ : A.lowestTypeUtility spec.isUnitIntervalAllocation β = 0) (c B_ed : ℝ),
    A.bundledProfit spec β c - A.allPayBenchmarkProfit - A.editionsOnlyBenchmarkProfit spec c B_ed =
      A.expectedEditionValue spec β - c * A.expectedAggregateBid β - (spec.price - c) * B_ed :=
  @MathEconLib.Auction.bundling_revenue_gain

-- Algebraic profit formula: maximum and uniqueness over all real prices.
example : ∀ {φbar α c M : ℝ} {n : ℕ}, 0 < α → 1 ≤ n → ∀ p : ℝ,
    MathEconLib.AllPurchase.sellerProfitInterior φbar α c M n p ≤
      MathEconLib.AllPurchase.sellerProfitInterior φbar α c M n
        (MathEconLib.AllPurchase.optimalPriceInterior φbar c α M) :=
  @MathEconLib.AllPurchase.sellerProfitInterior_le_at_optimal

example : ∀ {φbar α c M : ℝ} {n : ℕ}, 0 < α → 1 ≤ n → ∀ p : ℝ,
    (MathEconLib.AllPurchase.sellerProfitInterior φbar α c M n p =
      MathEconLib.AllPurchase.sellerProfitInterior φbar α c M n
        (MathEconLib.AllPurchase.optimalPriceInterior φbar c α M)) ↔
      p = MathEconLib.AllPurchase.optimalPriceInterior φbar c α M :=
  @MathEconLib.AllPurchase.sellerProfitInterior_eq_at_optimal_iff

-- The interior formula is identified with actual profit at the supplied auction's posted price.
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [NeZero n] [n.AtLeastTwo] (A : MathEconLib.LinearScarcityAuction Ω n)
    [A.HasIdenticalTypes] [A.HasIndependentTypes] [A.HasBoundedTypes] [A.HasAtomlessTypes]
    (β : ℝ → ℝ) (_ : Measurable β)
    (_ : StrictMonoOn β (Set.Icc A.lowestType A.highestType))
    (_ : ∀ j, Integrable (fun ω => β (A.θ j ω)) volume)
    (_ : (A.toBidderProblem A.spec.isUnitIntervalAllocation β 0).HasTypeDeviationIC)
    (_ : A.K_linear β < 0)
    (_ : (A.toBidderProblem A.spec.isUnitIntervalAllocation β 0).U
      (A.toBidderProblem A.spec.isUnitIntervalAllocation β 0).lowestType =
        (A.K_linear β) ^ 2 / (4 * A.α_coeff)) (c : ℝ),
    A.toAuction.bundledProfit A.spec β c =
      MathEconLib.AllPurchase.sellerProfitInterior A.φ_bar A.α_coeff c
        A.toAuction.expectedSqrtAllPayBid n A.spec.price :=
  @MathEconLib.LinearScarcityAuction.bundledProfit_eq_sellerProfitInterior

-- The price-independent moment and actual expected aggregate quantity use the same hypotheses.
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [NeZero n] [n.AtLeastTwo] (A : MathEconLib.LinearScarcityAuction Ω n)
    [A.HasIdenticalTypes] [A.HasIndependentTypes] [A.HasBoundedTypes] [A.HasAtomlessTypes]
    (β : ℝ → ℝ) (_ : Measurable β)
    (_ : StrictMonoOn β (Set.Icc A.lowestType A.highestType))
    (_ : ∀ j, Integrable (fun ω => β (A.θ j ω)) volume)
    (_ : (A.toBidderProblem A.spec.isUnitIntervalAllocation β 0).HasTypeDeviationIC)
    (_ : A.K_linear β < 0)
    (_ : (A.toBidderProblem A.spec.isUnitIntervalAllocation β 0).U
      (A.toBidderProblem A.spec.isUnitIntervalAllocation β 0).lowestType =
        (A.K_linear β) ^ 2 / (4 * A.α_coeff)),
    A.toAuction.expectedAggregateBid β =
      MathEconLib.AllPurchase.interiorMeanQuantity A.φ_bar A.α_coeff
        A.toAuction.expectedSqrtAllPayBid n A.spec.price :=
  @MathEconLib.LinearScarcityAuction.expectedAggregateBid_eq_interiorMeanQuantity

-- Edition-welfare bound and moment identity over supplied real parameters.
example : ∀ φbar c α : ℝ, 0 < α → ∀ B : ℝ,
    MathEconLib.AllPurchase.editionWelfare φbar c α B ≤
      MathEconLib.AllPurchase.firstBestEditionSurplus φbar c α :=
  @MathEconLib.AllPurchase.editionWelfare_le_firstBest

example : ∀ φbar c α EB EB2 : ℝ,
    MathEconLib.AllPurchase.editionWelfare φbar c α EB -
      MathEconLib.AllPurchase.bundledEditionWelfareMoments φbar c α EB EB2 = α * (EB2 - EB ^ 2) :=
  @MathEconLib.AllPurchase.editionWelfare_mean_sub_bundled

-- Auction welfare bridge needs aggregate quantity and its square to be integrable.
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} (A : MathEconLib.LinearScarcityAuction Ω n) (β : ℝ → ℝ) (c : ℝ),
    Integrable (A.toAuction.aggregateBid β) volume →
      Integrable (fun ω ↦ (A.toAuction.aggregateBid β ω) ^ 2) volume →
        A.bundledEditionWelfare β c =
          A.toAuction.expectedEditionValue A.spec β - c * A.toAuction.expectedAggregateBid β :=
  @MathEconLib.LinearScarcityAuction.bundledEditionWelfare_eq

-- Reusable algebraic welfare-gap identity over supplied values.
-- The economic statement and the signs of the two gaps are pinned or proved separately.
example : ∀ φbar c α B_ed WC : ℝ,
    MathEconLib.AllPurchase.firstBestEditionSurplus φbar c α - WC
      = MathEconLib.AllPurchase.cournotLoss φbar c α B_ed +
        MathEconLib.AllPurchase.contestLoss φbar c α B_ed WC :=
  @MathEconLib.AllPurchase.welfare_decomposition

-- Proposition 6.13: actual expected edition welfare decomposes at the auction's Cournot
-- benchmark. Square integrability is the only strategy assumption; gap signs are separate.
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} (A : MathEconLib.LinearScarcityAuction Ω n) (β : ℝ → ℝ) (c : ℝ),
    MemLp (A.toAuction.aggregateBid β) 2 volume →
      MathEconLib.AllPurchase.firstBestEditionSurplus A.φ_bar c A.α_coeff -
          (∫ ω, A.toAuction.aggregateBid β ω * A.spec.φ (A.toAuction.aggregateBid β ω) -
            c * A.toAuction.aggregateBid β ω) =
        MathEconLib.AllPurchase.cournotLoss A.φ_bar c A.α_coeff A.cournotQuantityLinear +
          MathEconLib.AllPurchase.contestLoss A.φ_bar c A.α_coeff A.cournotQuantityLinear
            (A.bundledEditionWelfare β c) :=
  @MathEconLib.LinearScarcityAuction.welfare_decomposition

-- The welfare penalty is the variance of the actual aggregate purchases.
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} (A : MathEconLib.LinearScarcityAuction Ω n) (β : ℝ → ℝ) (c : ℝ),
    MemLp (A.toAuction.aggregateBid β) 2 volume →
      MathEconLib.AllPurchase.editionWelfare A.φ_bar c A.α_coeff
          (A.toAuction.expectedAggregateBid β) - A.bundledEditionWelfare β c =
        A.α_coeff * variance (A.toAuction.aggregateBid β) volume :=
  @MathEconLib.LinearScarcityAuction.editionWelfare_mean_sub_bundled_eq_variance

-- Uniform all-pay bid (§9.6.3): b^{AP}(v) = (n−1)/n · vⁿ / v̄ⁿ⁻¹
example : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {n : ℕ} [NeZero n] [n.AtLeastTwo] (A : MathEconLib.Auction Ω n)
    [A.HasIdenticalTypes] (vbar : ℝ),
    0 < vbar → A.lowestType = 0 →
      (∀ t ∈ Set.Icc (0 : ℝ) vbar, A.commonCDF t = t / vbar) →
      ∀ v ∈ Set.Icc (0 : ℝ) vbar,
        A.allPayBid v = ((n : ℝ) - 1) / (n : ℝ) * v ^ n / vbar ^ (n - 1) :=
  @MathEconLib.Auction.allPayBid_uniform

/-! ## Game theory -/

-- Nash equilibrium — definition pin: the exact unfolding of `IsNashEquilibrium`
example {ι : Type u} {A : ι → Type v} {O : Type w} [DecidableEq ι]
    (G : MathEconLib.GameTheory.Game A O) (P : MathEconLib.GameTheory.PayoffStructure O ι)
    (a : (i : ι) → A i) :
    G.IsNashEquilibrium P a
      ↔ ∀ (i : ι) (s : A i),
          P.payoff i (G.outcome (Function.update a i s)) ≤ P.payoff i (G.outcome a) :=
  Iff.rfl

-- Nash existence: every finite game has a mixed-strategy Nash equilibrium
example : ∀ {ι : Type u} {A : ι → Type v} {O : Type w}
    (G : MathEconLib.GameTheory.Game A O) (P : MathEconLib.GameTheory.PayoffStructure O ι)
    [(i : ι) → MeasurableSpace (A i)] [MeasurableSpace O]
    [∀ i : ι, DiscreteMeasurableSpace (A i)] [DiscreteMeasurableSpace O]
    [G.Measurable] [Fintype ι] [DecidableEq ι] [(i : ι) → Finite (A i)]
    [∀ i : ι, Nonempty (A i)] [Finite O],
    ∃ a, G.toMixed.IsNashEquilibrium P.toExpected a :=
  @MathEconLib.GameTheory.Game.exists_isNashEquilibrium_of_finite

-- Pure existence preserves independent player, action, outcome, and ambient-vector universes.
universe uE

example : ∀ {ι : Type u} {A : ι → Type v} {O : Type w}
    (G : MathEconLib.GameTheory.Game A O) (P : MathEconLib.GameTheory.PayoffStructure O ι)
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [TopologicalSpace O] [G.Continuous] [P.Continuous] [Finite ι] [DecidableEq ι]
    {E : ι → Type uE} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalAddGroup (E i)]
    [∀ i, ContinuousSMul ℝ (E i)] [∀ i, T2Space (E i)] [∀ i, LocallyConvexSpace ℝ (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (_ : ∀ i, Convex ℝ (k i))
    (_ : ∀ a i, QuasiconcaveOn ℝ (k i) (Subtype.val.extend
      ((fun s ↦ P.payoff i (G.outcome (Function.update a i s))) ∘ (e i).symm) 0)),
    ∃ a, G.IsNashEquilibrium P a :=
  @MathEconLib.GameTheory.Game.exists_isNashEquilibrium_of_quasiconcaveOn.{u, v, w, uE}

-- Compact mixed existence retains the expected-payoff continuity hypothesis.
example : ∀ {ι : Type u} {A : ι → Type v} {O : Type w}
    (G : MathEconLib.GameTheory.Game A O) (P : MathEconLib.GameTheory.PayoffStructure O ι)
    [Fintype ι] [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    [∀ i, CompactSpace (A i)] [∀ i, TopologicalSpace.MetrizableSpace (A i)]
    [∀ i, Nonempty (A i)] [∀ i, MeasurableSpace (A i)] [MeasurableSpace O]
    [∀ i, BorelSpace (A i)] [BorelSpace O] [G.Continuous] [P.Continuous]
    [P.toExpected.Continuous],
    ∃ a, G.toMixed.IsNashEquilibrium P.toExpected a :=
  @MathEconLib.GameTheory.Game.exists_isNashEquilibrium_of_isCompact.{u, v, w}
