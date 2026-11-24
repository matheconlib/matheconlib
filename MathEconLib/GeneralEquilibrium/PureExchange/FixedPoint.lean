/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.GeneralEquilibrium.PureExchange.Demand
public import MathEconLib.ForMathlib.Kakutani

/-!
# A simultaneous capped-demand and price-response fixed point

The compact product consists of the closed normalized price simplex and one temporary
consumption box per household. The price response maximizes the value of aggregate excess
demand; household responses retain every greatest feasible alternative. Kakutani supplies a
simultaneous fixed point without strict convexity or a continuous demand selection.

This is the finite pure-exchange specialization of the classical fictitious-market-participant
method, using a temporary cap chosen for this development. The originals cover broader
production settings and permit excess supply at zero prices; strict positivity and exact
clearing here are proved separately from the stated stronger exchange assumptions.

## References

Kenneth J. Arrow and Gérard Debreu (1954), *Existence of an Equilibrium for a Competitive
Economy*, Econometrica **22**(3), 265–290, §§2.5 and 3.1–3.4.
[DOI: 10.2307/1907353](https://doi.org/10.2307/1907353).

Gérard Debreu (1959), *Theory of Value*, Cowles Foundation Monograph 17, §§5.6–5.7,
pp. 81–87, for the price-maximizer/excess-demand correspondence construction.
[Primary scan](https://cowles.yale.edu/sites/default/files/2022-09/m17-all.pdf).
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Topology
open MathEconLib.Preferences MathEconLib.RevealedPreference Set Filter

namespace MathEconLib.GeneralEquilibrium.PureExchange
namespace Internal

variable {L : ℕ}

/-- Strict individual endowments yield positive wealth on every simplex face. -/
lemma wealth_pos_of_mem_priceSimplex {e p : Bundle L}
    (he : ∀ k, 0 < e k) (hp : p ∈ priceSimplex) : 0 < dot p e := by
  have hex : ∃ k, 0 < p k := by
    by_contra h
    have hz : ∀ k, p k = 0 := fun k =>
      le_antisymm (le_of_not_gt (fun hk => h ⟨k, hk⟩)) (hp.1 k)
    have hsum : (∑ k, p k) = 0 := by simp [hz]
    linarith [hp.2]
  obtain ⟨k, hk⟩ := hex
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hp.1 j) (he j).le)
    ⟨k, Finset.mem_univ k, mul_pos hk (he k)⟩

lemma isCompact_priceSimplex : IsCompact (priceSimplex (L := L)) := by
  have hclosed : IsClosed (priceSimplex (L := L)) := by
    change IsClosed (Set.Ici (0 : Bundle L) ∩ {p | ∑ k, p k = 1})
    exact isClosed_Ici.inter (isClosed_eq
      (continuous_finsetSum _ (fun k _ => continuous_apply k)) continuous_const)
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Bundle L) 1)).of_isClosed_subset hclosed
  intro p hp
  refine ⟨hp.1, fun k => ?_⟩
  change p k ≤ 1
  rw [← hp.2]
  exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ k)

lemma convex_priceSimplex : Convex ℝ (priceSimplex (L := L)) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun k => add_nonneg (mul_nonneg ha (hp.1 k)) (mul_nonneg hb (hq.1 k)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hp.2, hq.2, mul_one, hab]

lemma priceSimplex_nonempty (hL : 0 < L) : (priceSimplex (L := L)).Nonempty := by
  classical
  let k : Fin L := ⟨0, hL⟩
  refine ⟨Pi.single k 1, (fun j => ?_), ?_⟩
  · by_cases h : k = j <;> simp [h]
  · simp

/-- The auctioneer chooses every normalized price maximizing excess-demand value. -/
def auctionDemand (z : Bundle L) : Set (Bundle L) :=
  {p | p ∈ priceSimplex ∧ IsMaxOn (fun q => dot q z) priceSimplex p}

lemma auctionDemand_nonempty (hL : 0 < L) (z : Bundle L) :
    (auctionDemand z).Nonempty := by
  obtain ⟨p, hp, hmax⟩ := isCompact_priceSimplex.exists_isMaxOn
    (priceSimplex_nonempty hL) (continuous_id.dotProduct continuous_const).continuousOn
  exact ⟨p, hp, hmax⟩

lemma auctionDemand_mem_of_tendsto
    {A : Type*} {l : Filter A} [NeBot l]
    {zs ps : A → Bundle L} {z p : Bundle L}
    (hz : Tendsto zs l (𝓝 z)) (hp : Tendsto ps l (𝓝 p))
    (hmem : ∀ᶠ n in l, ps n ∈ auctionDemand (zs n)) : p ∈ auctionDemand z := by
  refine ⟨isCompact_priceSimplex.isClosed.mem_of_tendsto hp
    (hmem.mono fun _ hn => hn.1), ?_⟩
  intro q hq
  exact le_of_tendsto_of_tendsto (tendsto_dot tendsto_const_nhds hz)
    (tendsto_dot hp hz) (hmem.mono fun _ hn => hn.2 hq)

lemma isCompact_auctionDemand (z : Bundle L) : IsCompact (auctionDemand z) := by
  apply isCompact_priceSimplex.of_isClosed_subset _ (fun _ h => h.1)
  apply IsSeqClosed.isClosed
  intro ps p hmem hp
  exact auctionDemand_mem_of_tendsto tendsto_const_nhds hp (Eventually.of_forall hmem)

lemma convex_auctionDemand (z : Bundle L) : Convex ℝ (auctionDemand z) := by
  intro p hp q hq a b ha hb hab
  refine ⟨convex_priceSimplex hp.1 hq.1 ha hb hab, ?_⟩
  intro r hr
  have hlin : dot (a • p + b • q) z = a * dot p z + b * dot q z := by
    simp only [dot, add_dotProduct, smul_dotProduct, smul_eq_mul]
  change dot r z ≤ dot (a • p + b • q) z
  rw [hlin]
  calc
    dot r z = a * dot r z + b * dot r z := by rw [← add_mul, hab, one_mul]
    _ ≤ a * dot p z + b * dot q z :=
      add_le_add (mul_le_mul_of_nonneg_left (hp.2 hr) ha)
        (mul_le_mul_of_nonneg_left (hq.2 hr) hb)

variable {I : Type*} [Fintype I]

/-- Compact domain for the price and all household consumptions. -/
def exchangeDomain (M : Bundle L) : Set (Bundle L × (I → Bundle L)) :=
  priceSimplex ×ˢ Set.univ.pi (fun _ : I => consumptionBox M)

omit [Fintype I] in
lemma isCompact_exchangeDomain (M : Bundle L) : IsCompact (exchangeDomain (I := I) M) :=
  isCompact_priceSimplex.prod (isCompact_univ_pi fun _ => isCompact_consumptionBox M)

omit [Fintype I] in
lemma convex_exchangeDomain (M : Bundle L) : Convex ℝ (exchangeDomain (I := I) M) :=
  convex_priceSimplex.prod (convex_pi fun _ _ => convex_Icc (0 : Bundle L) M)

omit [Fintype I] in
lemma exchangeDomain_nonempty (hL : 0 < L) {M : Bundle L} (hM : Nonnegative M) :
    (exchangeDomain (I := I) M).Nonempty := by
  obtain ⟨p, hp⟩ := priceSimplex_nonempty hL
  exact ⟨(p, 0), hp, fun _ _ => ⟨le_rfl, hM⟩⟩

/-- Combined auctioneer and household preference-demand correspondence. -/
def exchangeCorr (e : I → Bundle L) (R : I → CompletePreference (Orthant L)) (M : Bundle L)
    (s : exchangeDomain (I := I) M) : Set (Bundle L × (I → Bundle L)) :=
  auctionDemand ((∑ i, s.val.2 i) - ∑ i, e i) ×ˢ
    Set.univ.pi (fun i => cappedDemand (R i) (e i) M s.val.1)

lemma exchangeCorr_subset
    (e : I → Bundle L) (R : I → CompletePreference (Orthant L)) (M : Bundle L)
    (s : exchangeDomain (I := I) M) : exchangeCorr e R M s ⊆ exchangeDomain M := by
  intro y hy
  exact ⟨hy.1.1, fun i hi => (hy.2 i hi).choose_spec.1.1⟩

lemma isCompact_exchangeCorr
    (e : I → Bundle L) (R : I → CompletePreference (Orthant L))
    (hR : ∀ i, PreferenceRegularity (R i)) (M : Bundle L)
    (s : exchangeDomain (I := I) M) : IsCompact (exchangeCorr e R M s) :=
  (isCompact_auctionDemand _).prod
    (isCompact_univ_pi fun i => isCompact_cappedDemand (R i) (hR i) (e i) M s.val.1)

lemma convex_exchangeCorr
    (e : I → Bundle L) (R : I → CompletePreference (Orthant L))
    (hR : ∀ i, PreferenceRegularity (R i)) (M : Bundle L)
    (s : exchangeDomain (I := I) M) : Convex ℝ (exchangeCorr e R M s) :=
  (convex_auctionDemand _).prod
    (convex_pi fun i _ => convex_cappedDemand (R i) (hR i) (e i) M s.val.1)

lemma exchangeCorr_nonempty (hL : 0 < L)
    (e : I → Bundle L) (R : I → CompletePreference (Orthant L))
    (hR : ∀ i, PreferenceRegularity (R i)) (M : Bundle L)
    (he : ∀ i k, 0 < e i k) (hM : Nonnegative M)
    (s : exchangeDomain (I := I) M) : (exchangeCorr e R M s).Nonempty := by
  apply Set.Nonempty.prod (auctionDemand_nonempty hL _)
  apply Set.univ_pi_nonempty_iff.mpr
  intro i
  exact cappedDemand_nonempty (R i) (hR i) hM
    (wealth_pos_of_mem_priceSimplex (he i) s.property.1).le

lemma upperHemicontinuous_exchangeCorr
    (e : I → Bundle L) (R : I → CompletePreference (Orthant L))
    (hR : ∀ i, PreferenceRegularity (R i)) (M : Bundle L)
    (he : ∀ i k, 0 < e i k) :
    UpperHemicontinuous (exchangeCorr e R M) := by
  intro s
  apply UpperHemicontinuousAt.of_sequences (isCompact_exchangeDomain M).isSeqCompact
    (Eventually.of_forall (exchangeCorr_subset e R M))
  intro ss hss ys hys y hy
  have hs : Tendsto (fun n => (ss n).val) atTop (𝓝 s.val) :=
    continuous_subtype_val.tendsto s |>.comp hss
  have hsum : Tendsto (fun n => (∑ i, (ss n).val.2 i) - ∑ i, e i) atTop
      (𝓝 ((∑ i, s.val.2 i) - ∑ i, e i)) := by
    exact (tendsto_finsetSum _ (fun i _ =>
      (continuous_apply i).tendsto _ |>.comp hs.snd_nhds)).sub tendsto_const_nhds
  refine ⟨auctionDemand_mem_of_tendsto hsum hy.fst_nhds
    (Eventually.of_forall fun n => (hys n).1), ?_⟩
  intro i _
  exact cappedDemand_mem_of_tendsto (R i) (hR i)
    (wealth_pos_of_mem_priceSimplex (he i) s.property.1) hs.fst_nhds
    ((continuous_apply i).tendsto _ |>.comp hy.snd_nhds)
    (fun n => (hys n).2 i (Set.mem_univ i))

/-- A simultaneous capped preference-demand and auctioneer fixed point, derived
from preference primitives rather than supplied demand regularity. -/
theorem exists_capped_fixedPoint (hL : 0 < L)
    (e : I → Bundle L) (R : I → CompletePreference (Orthant L))
    (hR : ∀ i, PreferenceRegularity (R i)) (M : Bundle L)
    (he : ∀ i k, 0 < e i k) (hM : Nonnegative M) :
    ∃ (p : Bundle L) (x : I → Bundle L), p ∈ priceSimplex ∧
      (∀ i, x i ∈ cappedDemand (R i) (e i) M p) ∧
      (∀ q ∈ priceSimplex,
        dot q ((∑ i, x i) - ∑ i, e i) ≤ dot p ((∑ i, x i) - ∑ i, e i)) := by
  obtain ⟨s, hs⟩ := kakutaniGlicksbergFan (isCompact_exchangeDomain (I := I) M)
    (convex_exchangeDomain M) (exchangeDomain_nonempty hL hM)
    (F := exchangeCorr e R M)
    (hF := upperHemicontinuous_exchangeCorr e R hR M he)
    (exchangeCorr_subset e R M) (isCompact_exchangeCorr e R hR M)
    (convex_exchangeCorr e R hR M) (exchangeCorr_nonempty hL e R hR M he hM)
  exact ⟨s.val.1, s.val.2, hs.1.1, fun i => hs.2 i (Set.mem_univ i),
    fun q hq => hs.1.2 hq⟩

end Internal
end MathEconLib.GeneralEquilibrium.PureExchange
