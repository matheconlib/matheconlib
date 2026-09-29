module

public import MathEconLib.Auction.AllPurchase.Basic
public import MathEconLib.Auction.AllPurchase.LinearScarcity
public import MathEconLib.Auction.SymmetricIPV
public import MathEconLib.Auction.IdenticalTypes
public import MathEconLib.ForMathlib.IndepFun

/-!
# Revenue decomposition for the all-purchase auction (§6.7.1)

We decompose the seller's gross revenue `𝔼[p · B]` (with `B = Σⱼ β(Vⱼ)`)
into three economically meaningful pieces:

- the **contest rent** `n · 𝔼[b^{AP}(V)]`,
- the **baseline utility transfer** `−n · U(lowestType)`, and
- the **aggregate edition value** `𝔼[B · φ(B)]`.

This is **Proposition 6.10** in Scott's lecture notes. The proof decomposes
`p · B = (p − φ(B)) · B + φ(B) · B` pointwise, identifies the first piece with
the sum of individual net payments `∑ᵢ tᵢ`, applies the net-payment identity
(Proposition 6.4, stated here as `BidderProblem.netPaymentIdentity`) to each
bidder, and then exploits symmetry to collect `n` equal terms.

**Status**: fully proved (no `sorry`) modulo the integrability and symmetry
hypotheses that the caller must supply.  The proof goes through
`BidderProblem.netPaymentIdentity` (Proposition 6.4) plus a Fubini /
iterated-expectation step derived from `iIndepFun` + `indepFun_finset_sum_of_notMem`.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace Auction

/-! ### Aggregate bid and edition-value quantities -/

variable (A : Auction Ω n) [A.rules.IsAllPurchase]

/-- Aggregate equilibrium bid: `B(ω) = Σⱼ β(Vⱼ(ω))`. -/
noncomputable def aggregateBid (β : ℝ → ℝ) : Ω → ℝ :=
  fun ω => ∑ j, β (A.θ j ω)

/-- Expected aggregate quantity `𝔼[B]`. -/
noncomputable def expectedAggregateBid (β : ℝ → ℝ) : ℝ :=
  𝔼[A.aggregateBid β]

/-- Seller's **gross** revenue under equilibrium strategy `β`:
`𝔼[p · B] = p · 𝔼[B]`. -/
noncomputable def sellerGrossRevenue (β : ℝ → ℝ) : ℝ :=
  A.rules.allPurchase_p_price * A.expectedAggregateBid β

/-- Expected aggregate edition value: `𝔼[B · φ(B)]`. -/
noncomputable def expectedEditionValue (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω => A.aggregateBid β ω * A.rules.allPurchaseφ (A.aggregateBid β ω)]

/-- Expected total net payment to the seller: `𝔼[∑ᵢ tᵢ(β·θ)]`.
By `t_eq`, this equals `𝔼[(p − φ(B)) · B]`. -/
noncomputable def expectedNetPayment (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω => ∑ i, A.rules.t i (fun j => β (A.θ j ω))]

/-! ### Symmetric quantities (needs `HasIdenticalTypes`) -/

variable [HasIdenticalTypes A]

/-- Expected all-pay bid under the common type distribution: `𝔼[b^{AP}(V)]`.
By `HasIdenticalTypes` this is independent of which bidder's type we use. -/
noncomputable def expectedAllPayBid : ℝ :=
  𝔼[fun ω => A.allPayBid (A.θ 0 ω)]

/-- Lowest-type utility for the bidder-0 problem under equilibrium strategy `β`.

Under the symmetric equilibrium we care about, this is the common `U(lowestType)`
shared across bidders (the "baseline edition rent"). -/
noncomputable def lowestTypeUtility (β : ℝ → ℝ) : ℝ :=
  (A.toBidderProblem β 0).U (A.toBidderProblem β 0).lowestType

/-! ### Seller's three mechanism options (for Corollary 6.11) -/

/-- **Option A — All-pay only.** Seller profit `Π_A = n · 𝔼[b^{AP}(V)]`.
By revenue equivalence this equals `n · 𝔼[V_{(n-1:n)}]` (Auction.RevenueEquivalence). -/
noncomputable def allPayBenchmarkProfit : ℝ :=
  (n : ℝ) * A.expectedAllPayBid

/-- **Option B — Editions only.** Seller profit `Π_B = (p − c) · B^{ed-only}`,
where `B^{ed-only}` is the symmetric Cournot equilibrium total quantity in
the editions-only mechanism (a parameter — the Cournot game itself is not
formalized in this file). -/
noncomputable def editionsOnlyBenchmarkProfit (c B_ed : ℝ) : ℝ :=
  (A.rules.allPurchase_p_price - c) * B_ed

/-- **Option C — Bundled all-purchase.** Seller profit `Π_C = (p − c) · 𝔼[B]`. -/
noncomputable def bundledProfit (β : ℝ → ℝ) (c : ℝ) : ℝ :=
  (A.rules.allPurchase_p_price - c) * A.expectedAggregateBid β

/-! ### `bidThreshold` identity under strict monotonicity -/

/-- Under strict monotonicity of `β` on `[lo, hi]`, the bid threshold of a type's
own bid equals that type.  That is, `bidThreshold β lo hi (β v) = v` for every
`v ∈ [lo, hi]`.

This is the key algebraic fact we need to bridge the BidderProblem-level
`allPayBid` (which uses `B.q = winProb ∘ strategy`) to the Auction-level
`allPayBid` (which uses `F(v)^{n-1}`). -/
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

/-! ### `q_strat` and `allPayBid` bridges -/

omit [n.AtLeastTwo] in
/-- **Interim winning probability at a bidder's own bid.** Under efficient
allocation, independent identical bounded atomless types, and a *strictly*
monotone measurable strategy `β`, the winning probability when bidder `i`
reports type `v` and opponents also play `β` equals `F(v)^{n-1}`. -/
lemma q_strat_at_strictMono_eq
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    {β : ℝ → ℝ}
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hβ_meas : Measurable β)
    (i : Fin n) {v : ℝ} (hv : v ∈ Icc A.lowestType A.highestType) :
    A.q_strat β i (β v) = A.commonCDF v ^ (n - 1) := by
  have hle : A.lowestType ≤ A.highestType := le_trans hv.1 hv.2
  rw [A.q_strat_eq_cdf_pow hβ_mono.monotoneOn hβ_meas i (β v),
      bidThreshold_strictMono_eq hβ_mono hle hv]

omit [n.AtLeastTwo] in
/-- **BidderProblem `q` bridges to `F(v)^{n-1}`.** The `toBidderProblem β i`
structure's `q` equals the common CDF power, for types in the interval,
under strictly monotone `β`. -/
lemma toBidderProblem_q_eq_cdf_pow
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    {β : ℝ → ℝ}
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hβ_meas : Measurable β)
    (i : Fin n) {v : ℝ} (hv : v ∈ Icc A.lowestType A.highestType) :
    (A.toBidderProblem β i).q v = A.commonCDF v ^ (n - 1) := by
  simp only [BidderProblem.q_eq, toBidderProblem_winProb,
    toBidderProblem_strategy]
  exact A.q_strat_at_strictMono_eq hβ_mono hβ_meas i hv

omit [n.AtLeastTwo] in
/-- **BidderProblem `allPayBid` bridges to `A.allPayBid`.**

The `toBidderProblem β i` structure computes its all-pay bid via `B.q`, which
equals `F(ψ)^{n-1}` on the type interval by `toBidderProblem_q_eq_cdf_pow`;
integrating the two formulae over `[lowestType, v]` yields the same value. -/
lemma toBidderProblem_allPayBid_eq
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    {β : ℝ → ℝ}
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hβ_meas : Measurable β)
    (i : Fin n)
    [BidderProblem.HasTypeDeviationIC (A.toBidderProblem β i)]
    {v : ℝ} (hv : v ∈ Icc A.lowestType A.highestType) :
    (A.toBidderProblem β i).allPayBid v = A.allPayBid v := by
  -- Both sides are `v · _ - ∫ lowestType..v, _`; the `_` pieces agree on [lowestType, v].
  simp only [BidderProblem.allPayBid, allPayBid]
  have hlo : (A.toBidderProblem β i).lowestType = A.lowestType := by
    simp [toBidderProblem]
  have hq_at_v : (A.toBidderProblem β i).q v = A.commonCDF v ^ (n - 1) :=
    A.toBidderProblem_q_eq_cdf_pow hβ_mono hβ_meas i hv
  rw [hlo, hq_at_v]
  -- Now need: ∫ ψ in lowestType..v, B.q ψ = ∫ ψ in lowestType..v, F(ψ)^(n-1)
  congr 1
  apply intervalIntegral.integral_congr
  intro ψ hψ
  rw [Set.uIcc_of_le hv.1] at hψ
  have hψ_mem : ψ ∈ Icc A.lowestType A.highestType :=
    ⟨hψ.1, le_trans hψ.2 hv.2⟩
  exact A.toBidderProblem_q_eq_cdf_pow hβ_mono hβ_meas i hψ_mem

/-! ### Pointwise decomposition lemma -/

omit [NeZero n] [n.AtLeastTwo] [HasIdenticalTypes A] in
/-- **Pointwise decomposition.** For every `ω`,
`∑ᵢ tᵢ(β·θ(ω)) + B(ω) · φ(B(ω)) = p · B(ω)`.

Proof: `tᵢ(b) = (p − φ(B)) · bᵢ` by `t_eq`; summing over `i` gives
`(p − φ(B)) · B`, and adding `φ(B) · B` collapses to `p · B`. -/
lemma net_payment_plus_edition_value
    (β : ℝ → ℝ) (ω : Ω) :
    (∑ i, A.rules.t i (fun j => β (A.θ j ω))) +
      A.aggregateBid β ω * A.rules.allPurchaseφ (A.aggregateBid β ω) =
    A.rules.allPurchase_p_price * A.aggregateBid β ω := by
  simp_rw [Mechanism.IsAllPurchase.t_eq, ← Finset.mul_sum]
  show (A.rules.allPurchase_p_price -
      Mechanism.IsAllPurchase.φ (M := A.rules) (A.aggregateBid β ω)) *
        A.aggregateBid β ω +
      A.aggregateBid β ω * Mechanism.IsAllPurchase.φ (M := A.rules)
        (A.aggregateBid β ω) =
    A.rules.allPurchase_p_price * A.aggregateBid β ω
  ring

/-! ### Step 1: gross revenue = net payment + edition value -/

omit [NeZero n] [n.AtLeastTwo] [HasIdenticalTypes A] in
/-- The seller's gross revenue decomposes as net payment plus expected edition
value.  This follows by integrating the pointwise identity
`net_payment_plus_edition_value`. -/
lemma sellerGrossRevenue_eq_netPayment_add_editionValue
    (β : ℝ → ℝ)
    (hnet_int : Integrable
      (fun ω => ∑ i, A.rules.t i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.aggregateBid β ω * A.rules.allPurchaseφ (A.aggregateBid β ω)) ℙ) :
    A.sellerGrossRevenue β =
      A.expectedNetPayment β + A.expectedEditionValue β := by
  -- Pointwise: ∑ tᵢ + B·φ(B) = p·B; integrate by linearity.
  have hpt := A.net_payment_plus_edition_value β
  simp only [sellerGrossRevenue, expectedAggregateBid, expectedNetPayment,
    expectedEditionValue]
  -- rewrite p · 𝔼[B] = 𝔼[p · B]
  rw [show A.rules.allPurchase_p_price * ∫ ω, A.aggregateBid β ω ∂ℙ =
    ∫ ω, A.rules.allPurchase_p_price * A.aggregateBid β ω ∂ℙ from by
    rw [integral_const_mul]]
  rw [show (fun ω => A.rules.allPurchase_p_price * A.aggregateBid β ω) =
    (fun ω => (∑ i, A.rules.t i (fun j => β (A.θ j ω))) +
      A.aggregateBid β ω * A.rules.allPurchaseφ (A.aggregateBid β ω))
    from funext fun ω => (hpt ω).symm]
  exact integral_add hnet_int hedition_int

/-! ### Step 2: identify the net payment with the all-pay bid up to `U(a)` -/

omit [NeZero n] [n.AtLeastTwo] [HasIdenticalTypes A] in
/-- The net payment to a single bidder is the strategy-dependent interim
payment evaluated at the bidder's own bid: `𝔼[tᵢ(β·θ)] = 𝔼[p_strat β i (β(Vᵢ))]`.

Proof: iterated expectation + independence of `Vᵢ` from `V₋ᵢ`, via
`integral_indep_swap`. -/
lemma integral_t_i_eq_integral_p_strat
    [HasIndependentTypes A] [HasBoundedTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (i : Fin n)
    (ht_int : Integrable
      (fun ω => A.rules.t i (fun j => β (A.θ j ω))) ℙ) :
    𝔼[fun ω => A.rules.t i (fun j => β (A.θ j ω))] =
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
    fun x y => (A.rules.allPurchase_p_price -
      Mechanism.IsAllPurchase.φ (M := A.rules) (x + y)) * x with hh_def
  have hφ_meas : Measurable (Mechanism.IsAllPurchase.φ (M := A.rules)) :=
    (Mechanism.IsAllPurchase.φ_continuous (M := A.rules)).measurable
  have hh_meas : Measurable h.uncurry := by
    refine Measurable.mul ?_ (measurable_fst.comp (measurable_id))
    · refine (measurable_const.sub ?_)
      refine hφ_meas.comp ?_
      exact (measurable_fst.comp measurable_id).add (measurable_snd.comp measurable_id)
  -- Pointwise rewrite: t_i via t_eq + Finset.sum_update_univ.
  have hLHS : (fun ω => A.rules.t i (fun j => β (A.θ j ω))) =
      (fun ω => h (X ω) (Y ω)) := by
    funext ω
    simp only [Mechanism.IsAllPurchase.t_eq, h, X, Y]
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
    simp only [Mechanism.IsAllPurchase.t_eq, Function.update_self]
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

Under independence + identical types and IC for the bidder problem built from
`β`, the aggregate net payment equals `n · (𝔼[b^{AP}(V)] − U(lowestType))`.

This combines:
1. linearity to pull the sum outside the integral;
2. symmetry (`IdentDistrib`) to reduce to bidder 0;
3. iterated expectation (`integral_t_i_eq_integral_p_strat`);
4. the net-payment identity `cost ∘ strategy = allPayBid − U(lowestType)`;
5. the bridge from the bidder-problem `allPayBid` to `A.allPayBid`
   (`B.q v = F(v)^{n-1}` under efficient + IPV + strict monotonicity of `β`). -/
lemma expectedNetPayment_eq
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i, (A.toBidderProblem β i).HasTypeDeviationIC)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.t i (fun j => β (A.θ j ω))) ℙ)
    (hallPayBid_meas : Measurable A.allPayBid)
    (hallPayBid_int : ∀ i, Integrable (fun ω => A.allPayBid (A.θ i ω)) ℙ)
    (hU_sym : ∀ i, (A.toBidderProblem β i).U (A.toBidderProblem β i).lowestType
        = A.lowestTypeUtility β) :
    A.expectedNetPayment β = n * (A.expectedAllPayBid - A.lowestTypeUtility β) := by
  -- Step 1: pull the sum out of the integral using integrability of each term.
  have step1 : A.expectedNetPayment β =
      ∑ i, 𝔼[fun ω => A.rules.t i (fun j => β (A.θ j ω))] := by
    simp only [expectedNetPayment]
    exact integral_finset_sum _ (fun i _ => ht_int i)
  rw [step1]
  -- Step 2: show each per-bidder integral equals `expectedAllPayBid − lowestTypeUtility β`.
  have per_bidder : ∀ i,
      𝔼[fun ω => A.rules.t i (fun j => β (A.θ j ω))] =
        A.expectedAllPayBid - A.lowestTypeUtility β := fun i => by
    -- (a) iterated expectation
    rw [A.integral_t_i_eq_integral_p_strat β hβ_meas i (ht_int i)]
    -- (b)+(c)+(d) pointwise: p_strat β i (β v) = A.allPayBid v − U(lowestType)
    have hθ_mem : ∀ ω, A.θ i ω ∈ (A.toBidderProblem β i).typeInterval := fun ω =>
      HasBoundedTypes.θ_in (A := A) i ω
    have hθ_mem' : ∀ ω, A.θ i ω ∈ Icc A.lowestType A.highestType := fun ω => by
      have := HasBoundedTypes.θ_in (A := A) i ω
      simpa [A.θmin_eq_lowestType, A.θmax_eq_highestType] using this
    letI := hIC i
    have pointwise : ∀ ω,
        A.p_strat β i (β (A.θ i ω)) =
          A.allPayBid (A.θ i ω) -
            (A.toBidderProblem β i).U (A.toBidderProblem β i).lowestType := by
      intro ω
      have hBP := (A.toBidderProblem β i).netPaymentIdentity (A.θ i ω) (hθ_mem ω)
      have hbridge := A.toBidderProblem_allPayBid_eq hβ_mono hβ_meas i (hθ_mem' ω)
      -- `(B.cost (B.strategy v)) = B.allPayBid v - B.U lowestType`; rewrite B.allPayBid.
      rw [hbridge] at hBP
      -- LHS of hBP is definitionally `p_strat β i (β (θᵢ ω))`.
      exact hBP
    rw [show (fun ω => A.p_strat β i (β (A.θ i ω))) =
          (fun ω => A.allPayBid (A.θ i ω) -
            (A.toBidderProblem β i).U (A.toBidderProblem β i).lowestType)
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

/-! ### Proposition 6.10 — Revenue decomposition -/

omit [n.AtLeastTwo] in
/-- **Proposition 6.10 (Revenue decomposition, general form).**

In any symmetric strictly increasing equilibrium `β` of the all-purchase
auction,
`𝔼[p · B] = n · 𝔼[b^{AP}(V)] − n · U(lowestType) + 𝔼[B · φ(B)]`.

The integrability hypotheses will typically be discharged from boundedness of
types and continuity of `β` and `φ`; leaving them explicit here matches how
`LinearScarcityAuction` handles the same issues. -/
theorem revenue_decomposition
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i, (A.toBidderProblem β i).HasTypeDeviationIC)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.t i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.aggregateBid β ω * A.rules.allPurchaseφ (A.aggregateBid β ω)) ℙ)
    (hallPayBid_meas : Measurable A.allPayBid)
    (hallPayBid_int : ∀ i, Integrable (fun ω => A.allPayBid (A.θ i ω)) ℙ)
    (hU_sym : ∀ i, (A.toBidderProblem β i).U (A.toBidderProblem β i).lowestType
        = A.lowestTypeUtility β) :
    A.sellerGrossRevenue β =
      n * A.expectedAllPayBid - n * A.lowestTypeUtility β +
        A.expectedEditionValue β := by
  have hnet_int : Integrable
      (fun ω => ∑ i, A.rules.t i (fun j => β (A.θ j ω))) ℙ :=
    integrable_finset_sum _ (fun i _ => ht_int i)
  rw [A.sellerGrossRevenue_eq_netPayment_add_editionValue β
        hnet_int hedition_int,
      A.expectedNetPayment_eq β hβ_meas hβ_mono hIC ht_int
        hallPayBid_meas hallPayBid_int hU_sym]
  ring

omit [n.AtLeastTwo] in
/-- **Proposition 6.10 (boundary-regime form, `U(lowestType) = 0`).**

When the lowest type earns zero utility (e.g. under `K ≥ 0` and
`IsBoundaryRegime`), the decomposition simplifies to
`𝔼[p · B] = n · 𝔼[b^{AP}(V)] + 𝔼[B · φ(B)]`. -/
theorem revenue_decomposition_boundary
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i, (A.toBidderProblem β i).HasTypeDeviationIC)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.t i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.aggregateBid β ω * A.rules.allPurchaseφ (A.aggregateBid β ω)) ℙ)
    (hallPayBid_meas : Measurable A.allPayBid)
    (hallPayBid_int : ∀ i, Integrable (fun ω => A.allPayBid (A.θ i ω)) ℙ)
    (hU_sym : ∀ i, (A.toBidderProblem β i).U (A.toBidderProblem β i).lowestType
        = A.lowestTypeUtility β)
    (hU0 : A.lowestTypeUtility β = 0) :
    A.sellerGrossRevenue β =
      n * A.expectedAllPayBid + A.expectedEditionValue β := by
  rw [A.revenue_decomposition β hβ_meas hβ_mono hIC
        ht_int hedition_int hallPayBid_meas hallPayBid_int hU_sym, hU0]
  ring

/-! ### Corollary 6.11 — bundled vs standalone revenue comparison -/

omit [n.AtLeastTwo] in
/-- **Corollary 6.11 (boundary regime, corrected form).**

In the boundary regime (`U(lowestType) = 0`), the gain from bundling the
all-pay contest with the editions sale (Option C) relative to running the
two mechanisms separately (Options A + B) is
`Π_C − Π_A − Π_B = 𝔼[B·φ(B)] − c · 𝔼[B] − (p − c) · B^{ed-only}`.

The proof is pure algebra given `revenue_decomposition_boundary`: that
identity gives `p · 𝔼[B] = n · 𝔼[b^{AP}] + 𝔼[B·φ(B)]`, hence
`Π_C = (p − c) · 𝔼[B] = n · 𝔼[b^{AP}] + 𝔼[B·φ(B)] − c · 𝔼[B]
     = Π_A + 𝔼[B·φ(B)] − c · 𝔼[B]`,
and rearranging gives the stated identity.

**Note (§6.7.1).** This identity differs from the closed form in §6.7.1,
`(p − c)·(𝔼[B] − B^{ed-only}) + c · 𝔼[B·φ(B)] / p`, by the term
`p · 𝔼[B] − 𝔼[B·φ(B)]·(p − c)/p`.
-/
theorem bundling_revenue_gain
    [HasIndependentTypes A] [HasBoundedTypes A] [HasAtomlessTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i, (A.toBidderProblem β i).HasTypeDeviationIC)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.t i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.aggregateBid β ω * A.rules.allPurchaseφ (A.aggregateBid β ω)) ℙ)
    (hallPayBid_meas : Measurable A.allPayBid)
    (hallPayBid_int : ∀ i, Integrable (fun ω => A.allPayBid (A.θ i ω)) ℙ)
    (hU_sym : ∀ i, (A.toBidderProblem β i).U (A.toBidderProblem β i).lowestType
        = A.lowestTypeUtility β)
    (hU0 : A.lowestTypeUtility β = 0)
    (c B_ed : ℝ) :
    A.bundledProfit β c -
        A.allPayBenchmarkProfit -
        A.editionsOnlyBenchmarkProfit c B_ed =
      A.expectedEditionValue β -
        c * A.expectedAggregateBid β -
        (A.rules.allPurchase_p_price - c) * B_ed := by
  have h := A.revenue_decomposition_boundary β hβ_meas hβ_mono hIC
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
/-- **Proposition 6.10 for `LinearScarcityAuction` in boundary regime.**

When every bidder's induced `BidderProblem` is in the boundary regime
(`U(lowestType) = 0`), the baseline-utility term drops out and the
decomposition simplifies to
`𝔼[p · B] = n · 𝔼[b^{AP}(V)] + 𝔼[B · φ(B)]`.

`IsBoundaryRegime` is the natural economic condition here: for all-purchase
auctions with linear scarcity it holds whenever `K_linear β ≥ 0` (see
`QuadraticCostProblem.boundary_regime_strategy`).  Using it we discharge both
`hU_sym` and `hU0` from the general `revenue_decomposition_boundary`, and
`hallPayBid_meas` from the reusable `Auction.allPayBid_measurable`. -/
theorem revenue_decomposition_boundary_of_isBoundaryRegime
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i, (A.toAuction.toBidderProblem β i).HasTypeDeviationIC)
    (hBR : ∀ i, (A.toAuction.toBidderProblem β i).IsBoundaryRegime)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.t i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.toAuction.aggregateBid β ω *
        A.rules.allPurchaseφ (A.toAuction.aggregateBid β ω)) ℙ)
    (hallPayBid_int : ∀ i, Integrable
      (fun ω => A.toAuction.allPayBid (A.θ i ω)) ℙ) :
    A.toAuction.sellerGrossRevenue β =
      n * A.toAuction.expectedAllPayBid +
        A.toAuction.expectedEditionValue β := by
  have hU0 : A.toAuction.lowestTypeUtility β = 0 := by
    change (A.toAuction.toBidderProblem β 0).U
      (A.toAuction.toBidderProblem β 0).lowestType = 0
    exact (hBR 0).U_lowestType_zero
  have hU_sym : ∀ i,
      (A.toAuction.toBidderProblem β i).U
        (A.toAuction.toBidderProblem β i).lowestType =
        A.toAuction.lowestTypeUtility β := fun i => by
    rw [(hBR i).U_lowestType_zero, hU0]
  exact A.toAuction.revenue_decomposition_boundary β hβ_meas hβ_mono hIC
    ht_int hedition_int A.toAuction.allPayBid_measurable hallPayBid_int hU_sym hU0

/-! #### Corollary 6.11 — LinearScarcity specialization -/

/-- **Symmetric Cournot equilibrium total quantity** in the editions-only
mechanism under linear scarcity:
`B^{ed-only} = n(φ̄ − p)/(α(n+1))`.

Derived from the symmetric Cournot FOC `φ̄ − p − αB_{−i} − 2αbᵢ = 0` for the
editions-only payoff `bᵢ · (φ̄ − αB − p)`.  The Cournot mechanism itself is
not formalized here — this is the algebraic quantity that enters
Corollary 6.11. -/
noncomputable def cournotQuantityLinear : ℝ :=
  (n : ℝ) * (A.φ_bar - A.rules.allPurchase_p_price) /
    (A.α_coeff * ((n : ℝ) + 1))

omit [n.AtLeastTwo] in
/-- **Corollary 6.11 for `LinearScarcityAuction` in boundary regime** with
the linear-scarcity Cournot quantity plugged in.

Discharges `hU_sym`, `hU0`, and `hallPayBid_meas` automatically through
`IsBoundaryRegime` + `allPayBid_measurable`.  The remaining hypotheses
(`hβ_meas`, `hβ_mono`, `hIC`, integrability) are the same set already
required by `revenue_decomposition_boundary_of_isBoundaryRegime`. -/
theorem bundling_revenue_gain_of_isBoundaryRegime
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hIC : ∀ i, (A.toAuction.toBidderProblem β i).HasTypeDeviationIC)
    (hBR : ∀ i, (A.toAuction.toBidderProblem β i).IsBoundaryRegime)
    (ht_int : ∀ i, Integrable
      (fun ω => A.rules.t i (fun j => β (A.θ j ω))) ℙ)
    (hedition_int : Integrable
      (fun ω => A.toAuction.aggregateBid β ω *
        A.rules.allPurchaseφ (A.toAuction.aggregateBid β ω)) ℙ)
    (hallPayBid_int : ∀ i, Integrable
      (fun ω => A.toAuction.allPayBid (A.θ i ω)) ℙ)
    (c : ℝ) :
    A.toAuction.bundledProfit β c -
        A.toAuction.allPayBenchmarkProfit -
        A.toAuction.editionsOnlyBenchmarkProfit c A.cournotQuantityLinear =
      A.toAuction.expectedEditionValue β -
        c * A.toAuction.expectedAggregateBid β -
        (A.rules.allPurchase_p_price - c) * A.cournotQuantityLinear := by
  have hU0 : A.toAuction.lowestTypeUtility β = 0 := by
    change (A.toAuction.toBidderProblem β 0).U
      (A.toAuction.toBidderProblem β 0).lowestType = 0
    exact (hBR 0).U_lowestType_zero
  have hU_sym : ∀ i,
      (A.toAuction.toBidderProblem β i).U
        (A.toAuction.toBidderProblem β i).lowestType =
        A.toAuction.lowestTypeUtility β := fun i => by
    rw [(hBR i).U_lowestType_zero, hU0]
  exact A.toAuction.bundling_revenue_gain β hβ_meas hβ_mono hIC
    ht_int hedition_int A.toAuction.allPayBid_measurable hallPayBid_int hU_sym hU0
    c A.cournotQuantityLinear

end LinearScarcityAuction

end

end MathEconLib
