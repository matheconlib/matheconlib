module

public import MathEconLib.Auction.AllPurchase.Basic
public import MathEconLib.Auction.AllPurchase.LinearScarcity
public import MathEconLib.Auction.IdenticalTypes
public import MathEconLib.Auction.SymmetricIPV
public import MathEconLib.ForMathlib.IndepFun

/-!
# Revenue decomposition for the all-purchase auction

For aggregate purchases `B = Σⱼ β(Vⱼ)`, price `p`, and per-edition value `φ(B)`, gross revenue
`𝔼[p · B]` is all-pay contest revenue `n · 𝔼[b^{AP}(V)]`, less the baseline utility retained by
bidders `n · U(lowestType)`, plus aggregate edition value `𝔼[B · φ(B)]`. This decomposition assumes
independent identical bounded atomless types, a common measurable strictly increasing strategy
satisfying type-deviation incentive compatibility, equal lowest-type utilities, and the stated
measurability and integrability conditions.

When lowest-type utility is zero, the decomposition compares bundled profit with the sum of all-pay
revenue and editions-only profit, allowing a unit production cost `c` and a supplied editions-only
quantity. Under linear scarcity, the benchmark is the interior stationary Cournot quantity.

This is part of MathEconLib's all-purchase analysis, whose economic-theory research write-up is
pending. See `docs/AuctionReferences.md` for provenance and citation guidance.

## Main definitions

* `Auction.aggregateBid`: total purchases under a common strategy.
* `Auction.sellerGrossRevenue`: price times expected total purchases.
* `Auction.lowestTypeUtility`: bidder 0's interim utility at its lowest type.
* `Auction.allPayBenchmarkProfit`, `Auction.editionsOnlyBenchmarkProfit`, and
  `Auction.bundledProfit`: the three profits in the bundling comparison.
* `LinearScarcityAuction.cournotQuantityLinear`: the interior stationary editions-only quantity.

## Main statements

* `Auction.expectedNetPayment_eq`: expected net payments are all-pay revenue less baseline utility.
* `Auction.revenue_decomposition`: the three-term gross-revenue identity.
* `Auction.bundling_revenue_gain`: the profit difference when lowest-type utility is 0.
* `LinearScarcityAuction.bundling_revenue_gain_of_isBoundaryRegime`: the profit comparison at the
  linear-scarcity benchmark quantity.

## Tags

all-purchase auction, revenue decomposition, all-pay auction, bundling, cournot competition
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset MathEconLib.Mechanism.Auctions

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace Auction

/-! ### Aggregate bid and edition-value quantities -/

variable (A : Auction Ω n) (spec : AllPurchaseSpec A.rules (fun o i => o i))

/-- Aggregate purchases under the common strategy `β`: `B(ω) = Σⱼ β(Vⱼ(ω))`. -/
noncomputable def aggregateBid (β : ℝ → ℝ) : Ω → ℝ :=
  fun ω => ∑ j, β (A.θ j ω)

/-- Expected aggregate quantity `𝔼[B]`. -/
noncomputable def expectedAggregateBid (β : ℝ → ℝ) : ℝ :=
  𝔼[A.aggregateBid β]

/-- Seller's gross revenue at price `p` under strategy `β`: `𝔼[p · B] = p · 𝔼[B]`. -/
noncomputable def sellerGrossRevenue (β : ℝ → ℝ) : ℝ :=
  spec.price * A.expectedAggregateBid β

/-- Expected aggregate edition value: `𝔼[B · φ(B)]`. -/
noncomputable def expectedEditionValue (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω => A.aggregateBid β ω * spec.φ (A.aggregateBid β ω)]

/-- Expected total net receipts `𝔼[∑ᵢ tᵢ(β·θ)]`. For an all-purchase auction, these equal
`𝔼[(p − φ(B)) · B]`: gross receipts less the value of the purchased editions. -/
noncomputable def expectedNetPayment (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω => ∑ i, A.rules.payment i (fun j => β (A.θ j ω))]

/-! ### Quantities under a common type distribution -/

variable [HasIdenticalTypes A]

/-- Expected all-pay benchmark bid `𝔼[b^{AP}(V)]`, evaluated at bidder 0's type. Identical type
distributions make this expectation the same for every bidder. -/
noncomputable def expectedAllPayBid : ℝ :=
  𝔼[fun ω => A.allPayBid (A.θ 0 ω)]

/-- Bidder 0's interim utility at its lowest type under the common strategy `β`.

This is the common baseline utility only when lowest-type utilities are equal across bidders, as
required explicitly in the revenue decomposition. -/
noncomputable def lowestTypeUtility
    (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i)) (β : ℝ → ℝ) : ℝ :=
  (A.toBidderProblem halloc β 0).U (A.toBidderProblem halloc β 0).lowestType

/-! ### Seller's three mechanism options -/

/-- All-pay-only benchmark profit `Π_A = n · 𝔼[b^{AP}(V)]`: the sum of the `n` bidders' expected
all-pay benchmark bids. -/
noncomputable def allPayBenchmarkProfit : ℝ :=
  (n : ℝ) * A.expectedAllPayBid

/-- Editions-only profit `Π_B = (p − c) · B_ed` at the supplied total quantity `B_ed`, price `p`,
and unit production cost `c`. -/
noncomputable def editionsOnlyBenchmarkProfit (c B_ed : ℝ) : ℝ :=
  (spec.price - c) * B_ed

/-- Bundled all-purchase profit `Π_C = (p − c) · 𝔼[B]` under strategy `β`, with unit production
cost `c`. -/
noncomputable def bundledProfit (β : ℝ → ℝ) (c : ℝ) : ℝ :=
  (spec.price - c) * A.expectedAggregateBid β

/-! ### `bidThreshold` identity under strict monotonicity -/

/-- Under strict monotonicity of `β` on `[lo, hi]`, the bid threshold of a type's own bid equals
that type: `bidThreshold β lo hi (β v) = v` for every `v ∈ [lo, hi]`. Thus lower bids correspond to
lower types within the interval. -/
lemma bidThreshold_strictMono_eq
    {β : ℝ → ℝ} {lo hi v : ℝ}
    (hβ_mono : StrictMonoOn β (Icc lo hi))
    (hle : lo ≤ hi)
    (hv : v ∈ Icc lo hi) :
    bidThreshold β lo hi (β v) = v := by
  have hbdd : BddAbove (insert lo { w ∈ Icc lo hi | β w < β v }) :=
    ⟨hi, fun w hw => by
      rcases Set.mem_insert_iff.mp hw with rfl | ⟨hw_mem, _⟩
      · exact hle
      · exact hw_mem.2⟩
  have hne : (insert lo { w ∈ Icc lo hi | β w < β v }).Nonempty :=
    Set.insert_nonempty _ _
  apply le_antisymm
  · -- upper bound: every element of the set is ≤ v
    apply csSup_le hne
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | ⟨hw_mem, hw_lt⟩
    · exact hv.1
    · by_contra h
      push_neg at h  -- h : v < w
      linarith [hβ_mono hv hw_mem h]
  · -- lower bound: v ≤ sSup, by approximation from below
    rcases eq_or_lt_of_le hv.1 with heq | hlt
    · -- v = lo: lo is a member via the insert-point
      calc v = lo := heq.symm
        _ ≤ bidThreshold β lo hi (β v) :=
              le_csSup hbdd (Set.mem_insert _ _)
    · -- lo < v: for every ε > 0, v - min(ε/2, (v-lo)/2) is a member,
      -- giving v < bidThreshold + ε.
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      set δ := min (ε / 2) ((v - lo) / 2) with hδ_def
      have hvlo_pos : 0 < v - lo := sub_pos.mpr hlt
      have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
      have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hδ_le_half : δ ≤ (v - lo) / 2 := min_le_right _ _
      have hvδ_mem : v - δ ∈ Icc lo hi :=
        ⟨by linarith, by linarith [hv.2]⟩
      have hβ_lt : β (v - δ) < β v :=
        hβ_mono hvδ_mem hv (by linarith)
      have h_mem : v - δ ∈ insert lo { w ∈ Icc lo hi | β w < β v } :=
        Set.mem_insert_of_mem _ ⟨hvδ_mem, hβ_lt⟩
      have h_le : v - δ ≤ bidThreshold β lo hi (β v) := le_csSup hbdd h_mem
      linarith

/-! ### Winning probabilities and all-pay benchmark bids -/

omit [n.AtLeastTwo] in
/-- **Interim winning probability at a bidder's own bid.** Under strict-highest-bid allocation,
independent identical bounded atomless types, and a *strictly* monotone measurable strategy `β`,
the winning probability when bidder `i` submits `β(v)` and opponents also play `β` equals
`F(v)^{n-1}` for `v` in the type interval. -/
lemma q_strat_at_strictMono_eq
    (hstrict : UsesStrictHighestBidAllocation A.rules (fun o i => o i))
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    {β : ℝ → ℝ}
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hβ_meas : Measurable β)
    (i : Fin n) {v : ℝ} (hv : v ∈ Icc A.lowestType A.highestType) :
    A.q_strat β i (β v) = A.commonCDF v ^ (n - 1) := by
  have hle : A.lowestType ≤ A.highestType := le_trans hv.1 hv.2
  rw [A.q_strat_eq_cdf_pow hstrict hβ_mono.monotoneOn hβ_meas i (β v),
      bidThreshold_strictMono_eq hβ_mono hle hv]

omit [n.AtLeastTwo] in
/-- A type `v` bidder's interim allocation under `β` is `q(v) = F(v)^{n-1}` on the type interval,
assuming strict-highest-bid allocation, independent identical bounded atomless types, and a
measurable strategy strictly increasing on that interval. -/
lemma toBidderProblem_q_eq_cdf_pow
    (hstrict : UsesStrictHighestBidAllocation A.rules (fun o i => o i))
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    {β : ℝ → ℝ}
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hβ_meas : Measurable β)
    (i : Fin n) {v : ℝ} (hv : v ∈ Icc A.lowestType A.highestType) :
    (A.toBidderProblem hstrict.isUnitIntervalAllocation β i).q v = A.commonCDF v ^ (n - 1) := by
  simp only [BidderProblem.q_eq, toBidderProblem_winProb,
    toBidderProblem_strategy]
  exact A.q_strat_at_strictMono_eq hstrict hβ_mono hβ_meas i hv

omit [n.AtLeastTwo] in
/-- The all-pay benchmark bid associated with bidder `i`'s interim allocation is
`v · F(v)^{n-1} − ∫_{lowestType}^v F(ψ)^{n-1} dψ` on the type interval. This equality assumes
strict-highest-bid allocation, independent identical bounded atomless types, a measurable strategy
strictly increasing on that interval, and type-deviation incentive compatibility for bidder `i`. -/
lemma toBidderProblem_allPayBid_eq
    (hstrict : UsesStrictHighestBidAllocation A.rules (fun o i => o i))
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    {β : ℝ → ℝ}
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hβ_meas : Measurable β)
    (i : Fin n)
    [BidderProblem.HasTypeDeviationIC (A.toBidderProblem hstrict.isUnitIntervalAllocation β i)]
    {v : ℝ} (hv : v ∈ Icc A.lowestType A.highestType) :
    (A.toBidderProblem hstrict.isUnitIntervalAllocation β i).allPayBid v = A.allPayBid v := by
  -- Both sides are `v · _ - ∫ lowestType..v, _`; the `_` pieces agree on [lowestType, v].
  simp only [BidderProblem.allPayBid, allPayBid]
  have hlo : (A.toBidderProblem hstrict.isUnitIntervalAllocation β i).lowestType =
      A.lowestType := by
    simp [toBidderProblem]
  have hq_at_v : (A.toBidderProblem hstrict.isUnitIntervalAllocation β i).q v =
      A.commonCDF v ^ (n - 1) :=
    A.toBidderProblem_q_eq_cdf_pow hstrict hβ_mono hβ_meas i hv
  rw [hlo, hq_at_v]
  -- Now need: ∫ ψ in lowestType..v, B.q ψ = ∫ ψ in lowestType..v, F(ψ)^(n-1)
  congr 1
  apply intervalIntegral.integral_congr
  intro ψ hψ
  rw [Set.uIcc_of_le hv.1] at hψ
  have hψ_mem : ψ ∈ Icc A.lowestType A.highestType :=
    ⟨hψ.1, le_trans hψ.2 hv.2⟩
  exact A.toBidderProblem_q_eq_cdf_pow hstrict hβ_mono hβ_meas i hψ_mem

/-! ### Pointwise decomposition lemma -/

omit [NeZero n] [n.AtLeastTwo] [HasIdenticalTypes A] in
/-- For every type realization, total net payments plus aggregate edition value equal gross
receipts: `∑ᵢ tᵢ(β·θ(ω)) + B(ω) · φ(B(ω)) = p · B(ω)`. -/
lemma net_payment_plus_edition_value
    (β : ℝ → ℝ) (ω : Ω) :
    (∑ i, A.rules.payment i (fun j => β (A.θ j ω))) +
      A.aggregateBid β ω * spec.φ (A.aggregateBid β ω) =
    spec.price * A.aggregateBid β ω := by
  simp_rw [spec.payment_eq, ← Finset.mul_sum]
  change (spec.price -
      spec.φ (A.aggregateBid β ω)) *
        A.aggregateBid β ω +
      A.aggregateBid β ω * spec.φ
        (A.aggregateBid β ω) =
    spec.price * A.aggregateBid β ω
  ring

/-! ### Gross revenue, net payments, and edition value -/

omit [NeZero n] [n.AtLeastTwo] [HasIdenticalTypes A] in
/-- With integrable total net payments and aggregate edition value, gross revenue satisfies
`p · 𝔼[B] = 𝔼[∑ᵢ tᵢ] + 𝔼[B · φ(B)]`. -/
lemma sellerGrossRevenue_eq_netPayment_add_editionValue
    (β : ℝ → ℝ)
    (hnet_int : Integrable
      (fun ω => ∑ i, A.rules.payment i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.aggregateBid β ω * spec.φ (A.aggregateBid β ω)) ℙ) :
    A.sellerGrossRevenue spec β =
      A.expectedNetPayment β + A.expectedEditionValue spec β := by
  -- Pointwise: ∑ tᵢ + B·φ(B) = p·B; integrate by linearity.
  have hpt := A.net_payment_plus_edition_value spec β
  simp only [sellerGrossRevenue, expectedAggregateBid, expectedNetPayment,
    expectedEditionValue]
  -- rewrite p · 𝔼[B] = 𝔼[p · B]
  rw [show spec.price * ∫ ω, A.aggregateBid β ω ∂ℙ =
    ∫ ω, spec.price * A.aggregateBid β ω ∂ℙ from by
    rw [integral_const_mul]]
  rw [show (fun ω => spec.price * A.aggregateBid β ω) =
    (fun ω => (∑ i, A.rules.payment i (fun j => β (A.θ j ω))) +
      A.aggregateBid β ω * spec.φ (A.aggregateBid β ω))
    from funext fun ω => (hpt ω).symm]
  exact integral_add hnet_int hedition_int

/-! ### Net payments and lowest-type utility -/

omit [NeZero n] [n.AtLeastTwo] [HasIdenticalTypes A] in
/-- Bidder `i`'s expected net payment equals the expectation of its interim payment at its own bid:
`𝔼[tᵢ(β·θ)] = 𝔼[p_strat β i (β(Vᵢ))]`. This assumes independent bounded types, a measurable
strategy, and an integrable payment. -/
lemma integral_t_i_eq_integral_p_strat
    (spec : AllPurchaseSpec A.rules (fun o i => o i))
    [HasIndependentTypes A] [HasBoundedTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (i : Fin n)
    (ht_int : Integrable
      (fun ω => A.rules.payment i (fun j => β (A.θ j ω))) ℙ) :
    𝔼[fun ω => A.rules.payment i (fun j => β (A.θ j ω))] =
      𝔼[fun ω => A.p_strat β i (β (A.θ i ω))] := by
  -- Set X = β ∘ θᵢ and Y = ∑_{j ≠ i} β ∘ θⱼ. These are independent.
  set X : Ω → ℝ := fun ω => β (A.θ i ω) with hX_def
  set Y : Ω → ℝ := fun ω => ∑ j ∈ Finset.univ.erase i, β (A.θ j ω) with hY_def
  have hX_meas : Measurable X := hβ_meas.comp (A.θ_measurable i)
  have hY_meas : Measurable Y :=
    Finset.measurable_sum _ (fun j _ => hβ_meas.comp (A.θ_measurable j))
  -- Independence of X and Y from iIndepFun θ via `iIndepFun.comp` (apply β)
  -- + `indepFun_finset_sum_of_notMem` (sum over `erase i` ⫫ value at `i`).
  have hXY : IndepFun X Y ℙ := by
    have hβθ_indep : iIndepFun (fun j => fun ω => β (A.θ j ω)) ℙ :=
      HasIndependentTypes.θ_indep.comp (fun _ => β) (fun _ => hβ_meas)
    have hβθ_meas : ∀ j, Measurable (fun ω => β (A.θ j ω)) :=
      fun j => hβ_meas.comp (A.θ_measurable j)
    have hYX_indep :
        IndepFun (∑ j ∈ Finset.univ.erase i, fun ω => β (A.θ j ω))
                 (fun ω => β (A.θ i ω)) ℙ :=
      hβθ_indep.indepFun_finset_sum_of_notMem hβθ_meas (Finset.notMem_erase i _)
    -- (∑ j ∈ s, (fun ω => f j ω)) ω = ∑ j ∈ s, f j ω, so the sum-of-functions equals Y.
    have hY_pw : (∑ j ∈ Finset.univ.erase i, fun ω => β (A.θ j ω)) = Y := by
      ext ω; simp [Y, Finset.sum_apply]
    rw [hY_pw] at hYX_indep
    exact hYX_indep.symm
  -- h: the integrand as a function of (X, Y).
  set h : ℝ → ℝ → ℝ :=
    fun x y => (spec.price -
      spec.φ (x + y)) * x with hh_def
  have hφ_meas : Measurable (spec.φ) :=
    (spec.φ_continuous).measurable
  have hh_meas : Measurable h.uncurry := by
    refine Measurable.mul ?_ (measurable_fst.comp (measurable_id))
    · refine (measurable_const.sub ?_)
      refine hφ_meas.comp ?_
      exact (measurable_fst.comp measurable_id).add (measurable_snd.comp measurable_id)
  -- Pointwise rewrite: t_i via AllPurchaseSpec.payment_eq + Finset.sum_update_univ.
  have hLHS : (fun ω => A.rules.payment i (fun j => β (A.θ j ω))) =
      (fun ω => h (X ω) (Y ω)) := by
    funext ω
    simp only [spec.payment_eq, h, X, Y]
    -- Sum over all = β(θᵢ) + sum over erase i
    have : ∑ j, β (A.θ j ω) = β (A.θ i ω) +
        ∑ j ∈ Finset.univ.erase i, β (A.θ j ω) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm]
    rw [this]
  have hRHS : (fun ω => A.p_strat β i (β (A.θ i ω))) =
      (fun ω => ∫ ω', h (X ω) (Y ω') ∂ℙ) := by
    funext ω
    simp only [Auction.p_strat, h, X, Y]
    congr 1
    funext ω'
    simp only [spec.payment_eq, Function.update_self]
    -- Sum with i-th position updated: β(θᵢ ω) + sum over erase i at ω'
    have : ∑ j, Function.update (fun k => β (A.θ k ω')) i (β (A.θ i ω)) j =
        β (A.θ i ω) + ∑ j ∈ Finset.univ.erase i, β (A.θ j ω') := by
      rw [Finset.sum_update_univ]
    rw [this]
  rw [hLHS, hRHS]
  -- Apply the Fubini helper.
  exact MeasureTheory.integral_indep_swap hXY hX_meas hY_meas h hh_meas
    (hLHS ▸ ht_int)

omit [n.AtLeastTwo] in
/-- **Symmetric net payment identity.**

Expected total net payments equal `n · (𝔼[b^{AP}(V)] − U(lowestType))`: all-pay benchmark revenue
less the total baseline utility retained by bidders. The identity assumes independent identical
bounded atomless types, a measurable strategy strictly increasing on the type interval,
type-deviation incentive compatibility for every bidder, equal lowest-type utilities, measurable
all-pay benchmark bids, and integrable payments and benchmark bids. -/
lemma expectedNetPayment_eq
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.payment i (fun j => β (A.θ j ω))) ℙ)
    (hallPayBid_meas : Measurable A.allPayBid)
    (hallPayBid_int : ∀ i, Integrable (fun ω => A.allPayBid (A.θ i ω)) ℙ)
    (hU_sym : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).U
        (A.toBidderProblem spec.isUnitIntervalAllocation β i).lowestType
        = A.lowestTypeUtility spec.isUnitIntervalAllocation β) :
    A.expectedNetPayment β =
      n * (A.expectedAllPayBid - A.lowestTypeUtility spec.isUnitIntervalAllocation β) := by
  -- Step 1: pull the sum out of the integral using integrability of each term.
  have step1 : A.expectedNetPayment β =
      ∑ i, 𝔼[fun ω => A.rules.payment i (fun j => β (A.θ j ω))] := by
    simp only [expectedNetPayment]
    exact integral_finset_sum _ (fun i _ => ht_int i)
  rw [step1]
  -- Step 2: show each per-bidder integral equals `expectedAllPayBid − lowestTypeUtility β`.
  have per_bidder : ∀ i,
      𝔼[fun ω => A.rules.payment i (fun j => β (A.θ j ω))] =
        A.expectedAllPayBid - A.lowestTypeUtility spec.isUnitIntervalAllocation β := fun i => by
    -- (a) iterated expectation
    rw [A.integral_t_i_eq_integral_p_strat spec β hβ_meas i (ht_int i)]
    -- (b)+(c)+(d) pointwise: p_strat β i (β v) = A.allPayBid v − U(lowestType)
    have hθ_mem : ∀ ω,
        A.θ i ω ∈ (A.toBidderProblem spec.isUnitIntervalAllocation β i).typeInterval :=
      fun ω => HasBoundedTypes.θ_in (A := A) i ω
    have hθ_mem' : ∀ ω, A.θ i ω ∈ Icc A.lowestType A.highestType := fun ω => by
      have := HasBoundedTypes.θ_in (A := A) i ω
      simpa [A.θmin_eq_lowestType, A.θmax_eq_highestType] using this
    letI := hIC i
    have pointwise : ∀ ω,
        A.p_strat β i (β (A.θ i ω)) =
          A.allPayBid (A.θ i ω) -
            (A.toBidderProblem spec.isUnitIntervalAllocation β i).U
              (A.toBidderProblem spec.isUnitIntervalAllocation β i).lowestType := by
      intro ω
      have hBP := (A.toBidderProblem spec.isUnitIntervalAllocation β i).netPaymentIdentity
        (A.θ i ω) (hθ_mem ω)
      have hbridge :=
        A.toBidderProblem_allPayBid_eq spec.usesStrictHighestBidAllocation hβ_mono hβ_meas i
          (hθ_mem' ω)
      -- `(B.cost (B.strategy v)) = B.allPayBid v - B.U lowestType`; rewrite B.allPayBid.
      rw [hbridge] at hBP
      -- LHS of hBP is definitionally `p_strat β i (β (θᵢ ω))`.
      exact hBP
    rw [show (fun ω => A.p_strat β i (β (A.θ i ω))) =
          (fun ω => A.allPayBid (A.θ i ω) -
            (A.toBidderProblem spec.isUnitIntervalAllocation β i).U
              (A.toBidderProblem spec.isUnitIntervalAllocation β i).lowestType)
        from funext pointwise]
    -- linearity: 𝔼[f(θᵢ) − c] = 𝔼[f(θᵢ)] − c
    rw [integral_sub (hallPayBid_int i) (integrable_const _)]
    rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
    -- (e) IdentDistrib: 𝔼[A.allPayBid(θᵢ)] = 𝔼[A.allPayBid(θ₀)] = expectedAllPayBid
    have hident : ∫ ω, A.allPayBid (A.θ i ω) ∂ℙ = ∫ ω, A.allPayBid (A.θ 0 ω) ∂ℙ := by
      rw [← integral_map (A.θ_measurable i).aemeasurable
            hallPayBid_meas.aestronglyMeasurable,
          (HasIdenticalTypes.θ_identical i 0).map_eq,
          integral_map (A.θ_measurable 0).aemeasurable
            hallPayBid_meas.aestronglyMeasurable]
    rw [hident, hU_sym i]
    rfl
  -- Step 3: sum n equal copies
  simp_rw [per_bidder]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Revenue decomposition -/

omit [n.AtLeastTwo] in
/-- **Revenue decomposition, general form.**

Gross revenue satisfies `𝔼[p · B] = n · 𝔼[b^{AP}(V)] − n · U(lowestType) + 𝔼[B · φ(B)]`: contest
revenue less baseline bidder utility plus edition value.

The assumptions are independent identical bounded atomless types, a measurable strategy strictly
increasing on the type interval, type-deviation incentive compatibility for every bidder, equal
lowest-type utilities, measurable all-pay benchmark bids, and integrable payments, benchmark bids,
and aggregate edition value. -/
theorem revenue_decomposition
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.payment i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.aggregateBid β ω * spec.φ (A.aggregateBid β ω)) ℙ)
    (hallPayBid_meas : Measurable A.allPayBid)
    (hallPayBid_int : ∀ i, Integrable (fun ω => A.allPayBid (A.θ i ω)) ℙ)
    (hU_sym : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).U
        (A.toBidderProblem spec.isUnitIntervalAllocation β i).lowestType
        = A.lowestTypeUtility spec.isUnitIntervalAllocation β) :
    A.sellerGrossRevenue spec β =
      n * A.expectedAllPayBid - n * A.lowestTypeUtility spec.isUnitIntervalAllocation β +
        A.expectedEditionValue spec β := by
  have hnet_int : Integrable
      (fun ω => ∑ i, A.rules.payment i (fun j => β (A.θ j ω))) ℙ :=
    integrable_finset_sum _ (fun i _ => ht_int i)
  rw [A.sellerGrossRevenue_eq_netPayment_add_editionValue spec β
        hnet_int hedition_int,
      A.expectedNetPayment_eq spec β hβ_meas hβ_mono hIC ht_int
        hallPayBid_meas hallPayBid_int hU_sym]
  ring

omit [n.AtLeastTwo] in
/-- **Boundary-regime revenue decomposition, `U(lowestType) = 0`.**

Under the assumptions of `revenue_decomposition`, if the common lowest-type utility is zero, gross
revenue is `𝔼[p · B] = n · 𝔼[b^{AP}(V)] + 𝔼[B · φ(B)]`: all-pay benchmark revenue plus aggregate
edition value. -/
theorem revenue_decomposition_boundary
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.payment i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.aggregateBid β ω * spec.φ (A.aggregateBid β ω)) ℙ)
    (hallPayBid_meas : Measurable A.allPayBid)
    (hallPayBid_int : ∀ i, Integrable (fun ω => A.allPayBid (A.θ i ω)) ℙ)
    (hU_sym : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).U
        (A.toBidderProblem spec.isUnitIntervalAllocation β i).lowestType
        = A.lowestTypeUtility spec.isUnitIntervalAllocation β)
    (hU0 : A.lowestTypeUtility spec.isUnitIntervalAllocation β = 0) :
    A.sellerGrossRevenue spec β =
      n * A.expectedAllPayBid + A.expectedEditionValue spec β := by
  rw [A.revenue_decomposition spec β hβ_meas hβ_mono hIC
        ht_int hedition_int hallPayBid_meas hallPayBid_int hU_sym, hU0]
  ring

/-! ### Bundled and standalone profit comparison -/

omit [n.AtLeastTwo] in
/-- **Boundary-regime profit comparison.**

Under the assumptions of `revenue_decomposition_boundary`, the profit difference between the
bundled all-purchase auction and the sum of the all-pay and editions-only benchmarks is
`Π_C − Π_A − Π_B = 𝔼[B·φ(B)] − c · 𝔼[B] − (p − c) · B^{ed-only}`. Here `c` is unit production cost
and `B^{ed-only}` is the supplied editions-only quantity; the identity does not assert that this
difference is positive.

**Comparison with an alternative expression.** For `p ≠ 0`, the expression
`(p − c)·(𝔼[B] − B^{ed-only}) + c · 𝔼[B·φ(B)] / p`, minus the profit difference here is
`p · 𝔼[B] − 𝔼[B·φ(B)]·(p − c)/p`. -/
theorem bundling_revenue_gain
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.payment i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.aggregateBid β ω * spec.φ (A.aggregateBid β ω)) ℙ)
    (hallPayBid_meas : Measurable A.allPayBid)
    (hallPayBid_int : ∀ i, Integrable (fun ω => A.allPayBid (A.θ i ω)) ℙ)
    (hU_sym : ∀ i, (A.toBidderProblem spec.isUnitIntervalAllocation β i).U
        (A.toBidderProblem spec.isUnitIntervalAllocation β i).lowestType
        = A.lowestTypeUtility spec.isUnitIntervalAllocation β)
    (hU0 : A.lowestTypeUtility spec.isUnitIntervalAllocation β = 0)
    (c B_ed : ℝ) :
    A.bundledProfit spec β c -
        A.allPayBenchmarkProfit -
        A.editionsOnlyBenchmarkProfit spec c B_ed =
      A.expectedEditionValue spec β -
        c * A.expectedAggregateBid β -
        (spec.price - c) * B_ed := by
  have h := A.revenue_decomposition_boundary spec β hβ_meas hβ_mono hIC
    ht_int hedition_int hallPayBid_meas hallPayBid_int hU_sym hU0
  -- h : sellerGrossRevenue β = n · expectedAllPayBid + expectedEditionValue β
  -- i.e. p · 𝔼[B] = n · 𝔼[b^{AP}] + 𝔼[B·φ(B)]
  simp only [bundledProfit, allPayBenchmarkProfit, editionsOnlyBenchmarkProfit,
    sellerGrossRevenue] at h ⊢
  linarith

end Auction

/-! ### LinearScarcity specialization -/

namespace LinearScarcityAuction

variable (A : LinearScarcityAuction Ω n)
variable [A.HasIdenticalTypes] [A.HasIndependentTypes]
variable [A.HasBoundedTypes] [A.HasAtomlessTypes]

omit [n.AtLeastTwo] in
/-- **Boundary-regime revenue decomposition under linear scarcity.**

For linear scarcity `φ(B) = φ̄ − αB`, gross revenue is `𝔼[p · B] = n · 𝔼[b^{AP}(V)] + 𝔼[B · φ(B)]`
when every bidder's lowest type earns zero utility, as required by the boundary-regime
assumption.

The result also assumes independent identical bounded atomless types, a measurable strategy
strictly increasing on the type interval, type-deviation incentive compatibility for every bidder,
and integrable payments, all-pay benchmark bids, and aggregate edition value. -/
theorem revenue_decomposition_boundary_of_isBoundaryRegime
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i,
      (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (hBR : ∀ i, (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β i).IsBoundaryRegime)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.payment i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.toAuction.aggregateBid β ω *
        A.spec.φ (A.toAuction.aggregateBid β ω)) ℙ)
    (hallPayBid_int : ∀ i, Integrable
      (fun ω => A.toAuction.allPayBid (A.θ i ω)) ℙ) :
    A.toAuction.sellerGrossRevenue A.spec β =
      n * A.toAuction.expectedAllPayBid +
        A.toAuction.expectedEditionValue A.spec β := by
  have hU0 : A.toAuction.lowestTypeUtility A.spec.isUnitIntervalAllocation β = 0 := by
    change (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β 0).U
      (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β 0).lowestType = 0
    exact (hBR 0).U_lowestType_zero
  have hU_sym : ∀ i,
      (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β i).U
        (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β i).lowestType =
        A.toAuction.lowestTypeUtility A.spec.isUnitIntervalAllocation β := fun i => by
    rw [(hBR i).U_lowestType_zero, hU0]
  exact A.toAuction.revenue_decomposition_boundary A.spec β hβ_meas hβ_mono hIC
    ht_int hedition_int A.toAuction.allPayBid_measurable hallPayBid_int hU_sym hU0

/-! #### Linear-scarcity profit comparison -/

/-- Interior stationary Cournot candidate for total editions-only purchases under linear scarcity:
`B^{ed-only} = n(φ̄ − p)/(α(n+1))`.

For payoff `bᵢ · (φ̄ − αB − p)`, symmetric first-order conditions give this quantity. Since
`α > 0`, it is positive when `φ̄ > p`, zero when `φ̄ = p`, and negative when `φ̄ < p`; in the last
case it is infeasible for a game with nonnegative purchases. -/
noncomputable def cournotQuantityLinear : ℝ :=
  (n : ℝ) * (A.φ_bar - A.spec.price) /
    (A.α_coeff * ((n : ℝ) + 1))

omit [n.AtLeastTwo] in
/-- **Boundary-regime profit comparison under linear scarcity.**

Bundled profit minus all-pay benchmark profit and editions-only profit at
`B_ed = n(φ̄ − p)/(α(n+1))` equals `𝔼[B·φ(B)] − c · 𝔼[B] − (p − c) · B_ed`, where `c` is unit
production cost. The comparison assumes independent identical bounded atomless types, a measurable
strategy strictly increasing on the type interval, type-deviation incentive compatibility and zero
lowest-type utility for every bidder, and integrable payments, benchmark bids, and edition value.
The benchmark quantity is the interior stationary Cournot candidate and is feasible as a
nonnegative purchase quantity only when `φ̄ ≥ p`. -/
theorem bundling_revenue_gain_of_isBoundaryRegime
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i,
      (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (hBR : ∀ i, (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β i).IsBoundaryRegime)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.payment i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.toAuction.aggregateBid β ω *
        A.spec.φ (A.toAuction.aggregateBid β ω)) ℙ)
    (hallPayBid_int : ∀ i, Integrable
      (fun ω => A.toAuction.allPayBid (A.θ i ω)) ℙ)
    (c : ℝ) :
    A.toAuction.bundledProfit A.spec β c -
        A.toAuction.allPayBenchmarkProfit -
        A.toAuction.editionsOnlyBenchmarkProfit A.spec c A.cournotQuantityLinear =
      A.toAuction.expectedEditionValue A.spec β -
        c * A.toAuction.expectedAggregateBid β -
        (A.spec.price - c) * A.cournotQuantityLinear := by
  have hU0 : A.toAuction.lowestTypeUtility A.spec.isUnitIntervalAllocation β = 0 := by
    change (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β 0).U
      (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β 0).lowestType = 0
    exact (hBR 0).U_lowestType_zero
  have hU_sym : ∀ i,
      (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β i).U
        (A.toAuction.toBidderProblem A.spec.isUnitIntervalAllocation β i).lowestType =
        A.toAuction.lowestTypeUtility A.spec.isUnitIntervalAllocation β := fun i => by
    rw [(hBR i).U_lowestType_zero, hU0]
  exact A.toAuction.bundling_revenue_gain A.spec β hβ_meas hβ_mono hIC
    ht_int hedition_int A.toAuction.allPayBid_measurable hallPayBid_int hU_sym hU0
    c A.cournotQuantityLinear

end LinearScarcityAuction

end

end MathEconLib
