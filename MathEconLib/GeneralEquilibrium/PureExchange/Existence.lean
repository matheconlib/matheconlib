/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.GeneralEquilibrium.PureExchange.FixedPoint

/-!
# Walrasian existence with multivalued household demand

`exists_walrasianEquilibrium` proves the finite pure-exchange theorem from complete,
transitive preferences on the nonnegative orthant, separate closed upper and lower contours,
ordinary convexity, strong monotonicity, and strictly positive individual endowments.
It returns the independently defined equilibrium predicate, normalized strictly positive
prices, and budget exhaustion. Demand can be multivalued.

The fixed point uses a temporary consumption cap. Aggregate feasibility makes that cap
slack. A relational strict-mixture lemma, derived from the stated preference conditions,
then gives unrestricted budget optimality. No utility representation or concavifiability
is assumed. This is a classical sufficient exchange theorem, not a formalization of the
full Arrow–Debreu production theorem or every existence theorem in MWG.

## References

Victor H. Aguiar (2026), *Microeconomic Theory I*, Fall 2026 edition, November 18 revision,
Appendix B, “Fixed Points and Equilibrium Existence”, Proposition B.4, “Walrasian existence
with convex preferences”, pp. 216–217
([stable PDF](https://github.com/vaguiarl/Econ803Micro1SFUFall2026/blob/bd3bef405f1291ee4c494826f1cf734f773cb95f/notes/Microeconomics_1_notes_by_Victor_Aguiar.pdf)).
The preference and endowment assumptions and the full-budget, exact-clearing conclusion agree.
Here positive commodity dimension is explicit; the consumer set may be empty. The temporary
ceiling is aggregate resources plus one, rather than twice aggregate resources.

Kenneth J. Arrow and Gérard Debreu (1954), *Existence of an Equilibrium for a Competitive
Economy*, Econometrica **22**(3), 265–290, §§2.5 and 3.1–3.4, for the classical fictitious
price-participant method. [DOI: 10.2307/1907353](https://doi.org/10.2307/1907353).

Gérard Debreu (1959), *Theory of Value*, Cowles Foundation Monograph 17, §§5.6–5.7,
for the price-response/excess-demand correspondence method.
[Primary scan](https://cowles.yale.edu/sites/default/files/2022-09/m17-all.pdf).
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Topology
open MathEconLib.Preferences MathEconLib.RevealedPreference Set Filter

namespace MathEconLib.GeneralEquilibrium.PureExchange

variable {L : ℕ}

namespace Internal

lemma convex_fullBudget (e p : Bundle L) : Convex ℝ (fullBudget e p) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun k => add_nonneg (mul_nonneg ha (hx.1 k)) (mul_nonneg hb (hy.1 k)), ?_⟩
  rw [dot_add_smul]
  calc
    a * dot p x + b * dot p y ≤ a * dot p e + b * dot p e :=
      add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    _ = dot p e := by rw [← add_mul, hab, one_mul]

lemma dot_sum {I : Type*} [Fintype I] (p : Bundle L) (x : I → Bundle L) :
    dot p (∑ i, x i) = ∑ i, dot p (x i) := by
  simp only [dot, dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- Auctioneer optimality and household affordability imply aggregate feasibility. -/
lemma aggregate_le_of_auctioneer {I : Type*} [Fintype I]
    (e x : I → Bundle L) (p : Bundle L)
    (hbudget : ∀ i, dot p (x i) ≤ dot p (e i))
    (hauction : ∀ q ∈ priceSimplex,
      dot q ((∑ i, x i) - ∑ i, e i) ≤ dot p ((∑ i, x i) - ∑ i, e i)) :
    (∑ i, x i) ≤ ∑ i, e i := by
  classical
  have hwalras : dot p ((∑ i, x i) - ∑ i, e i) ≤ 0 := by
    rw [dot_sub, dot_sum, dot_sum]
    exact sub_nonpos.mpr (Finset.sum_le_sum fun i _ => hbudget i)
  intro k
  have hvertex : Pi.single k (1 : ℝ) ∈ priceSimplex := by
    refine ⟨fun j => ?_, ?_⟩
    · by_cases h : k = j <;> simp [h]
    · simp
  have h := (hauction (Pi.single k 1) hvertex).trans hwalras
  simpa only [dot, single_dotProduct, one_mul, Pi.sub_apply, sub_nonpos] using h

/-- Positive prices turn value clearing and free disposal into exact clearing. -/
lemma clearing_of_pos_budget_eq {I : Type*} [Fintype I]
    (e x : I → Bundle L) (p : Bundle L) (hp : ∀ k, 0 < p k)
    (hbudget : ∀ i, dot p (x i) = dot p (e i))
    (hfeas : (∑ i, x i) ≤ ∑ i, e i) : (∑ i, x i) = ∑ i, e i := by
  have hsum : ∑ k, p k * ((∑ i, e i) k - (∑ i, x i) k) = 0 := by
    change dot p ((∑ i, e i) - ∑ i, x i) = 0
    rw [dot_sub, dot_sum, dot_sum]
    simp_rw [hbudget]
    exact sub_self _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k (_ : k ∈ Finset.univ) => mul_nonneg (hp k).le (sub_nonneg.mpr (hfeas k)))).mp hsum
  ext k
  have hk := (mul_eq_zero.mp (hz k (Finset.mem_univ k))).resolve_left (ne_of_gt (hp k))
  exact (sub_eq_zero.mp hk).symm

/-- Strong monotonicity includes weak coordinate monotonicity. -/
lemma weak_mono (R : CompletePreference (Orthant L)) (hR : PreferenceRegularity R) {x y : Orthant L}
    (h : x.val ≤ y.val) : R.le x y := by
  by_cases heq : x = y
  · subst y
    exact R.toPreference.le_refl x
  · exact (hR.strong_mono (lt_of_le_of_ne h
      (fun hval => heq (Subtype.ext hval)))).1

/-- Continuity, ordinary convexity, and strong monotonicity imply strict
improvement along a segment toward a strictly preferred bundle. This does not
assert a local-to-global theorem for arbitrary quasiconcave functions. -/
lemma not_le_mixture (R : CompletePreference (Orthant L)) (hR : PreferenceRegularity R)
    {x y : Orthant L} (hyx : ¬R.le y x)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1)
    (hz : Nonnegative (a • x.val + b • y.val)) :
    ¬R.le ⟨a • x.val + b • y.val, hz⟩ x := by
  let ys : ℕ → Orthant L := fun n =>
    ⟨radialWeight n • y.val, fun k => mul_nonneg (radialWeight_nonneg n) (y.property k)⟩
  have hys : Tendsto ys atTop (𝓝 y) := by
    apply tendsto_subtype_rng.mpr
    simpa [ys] using tendsto_radialWeight.smul (tendsto_const_nhds (x := y.val))
  obtain ⟨n, hn⟩ : ∃ n, ¬R.le (ys n) x := by
    by_contra! h
    exact hyx ((hR.closed_lower x).mem_of_tendsto hys (Eventually.of_forall h))
  have hxyn : R.le x (ys n) := (R.total x (ys n)).resolve_right hn
  obtain ⟨hz', hxz'⟩ := hR.convex_upper x
    (show x.val ∈ {v | ∃ hv : Nonnegative v, R.le x ⟨v, hv⟩} from
      ⟨x.property, R.toPreference.le_refl x⟩)
    (show (ys n).val ∈ {v | ∃ hv : Nonnegative v, R.le x ⟨v, hv⟩} from
      ⟨(ys n).property, hxyn⟩) ha hb.le hab
  obtain ⟨k, hk⟩ : ∃ k, 0 < y.val k := by
    by_contra h
    have hy0 : ∀ k, y.val k ≤ 0 := fun k => le_of_not_gt (fun hk => h ⟨k, hk⟩)
    exact hyx (weak_mono R hR (fun k => (hy0 k).trans (x.property k)))
  have hlt : a • x.val + b • (ys n).val < a • x.val + b • y.val := by
    apply Pi.lt_def.mpr
    refine ⟨fun j => ?_, k, ?_⟩
    · change a * x.val j + b * (radialWeight n * y.val j) ≤ a * x.val j + b * y.val j
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul_of_nonneg_right (radialWeight_lt_one n).le (y.property j)) hb.le)
    · change a * x.val k + b * (radialWeight n * y.val k) < a * x.val k + b * y.val k
      exact add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left
        (by simpa using mul_lt_mul_of_pos_right (radialWeight_lt_one n) hk) hb)
  intro hzx
  exact (hR.strong_mono (x := ⟨_, hz'⟩) (y := ⟨_, hz⟩) hlt).2
    (R.toPreference.le_trans hzx hxz')

/-- A slack-cap optimum is an optimum on the entire budget under precisely
continuous convex strongly monotone preferences, without concavifiability. -/
theorem cappedDemand_full_max
    (R : CompletePreference (Orthant L)) (hR : PreferenceRegularity R)
    {e M p : Bundle L} {x : Orthant L}
    (hx : x.val ∈ cappedDemand R e M p)
    (hslack : ∀ k, x.val k < M k) :
    ∀ y : Orthant L, y.val ∈ fullBudget e p → R.le y x := by
  rcases hx with ⟨hxnn, hxcap, hxmax⟩
  have hxfull : x.val ∈ fullBudget e p := ⟨x.property, hxcap.2⟩
  intro y hy
  by_contra hyx
  let f : ℝ → Bundle L := fun t => (1 - t) • x.val + t • y.val
  have hfcont : Continuous f :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 x.val) := by
    simpa [f] using (hfcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ v : Bundle L in 𝓝 x.val, ∀ k, v k < M k := by
    apply Filter.eventually_all.mpr
    intro k
    exact (isOpen_lt (continuous_apply k) continuous_const).mem_nhds (hslack k)
  obtain ⟨t, hcap, ht⟩ := ((hf.eventually hnear).and
    (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))).exists
  have ha : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hab : (1 - t) + t = 1 := by ring
  have hfull : f t ∈ fullBudget e p :=
    convex_fullBudget e p hxfull hy ha ht.1.le hab
  have hmax : R.le ⟨f t, hfull.1⟩ x := hxmax
    ⟨⟨hfull.1, fun k => (hcap k).le⟩, hfull.2⟩
  exact not_le_mixture R hR hyx ha ht.1 hab hfull.1 hmax

lemma preference_price_pos_of_full_max
    (R : CompletePreference (Orthant L)) (hR : PreferenceRegularity R)
    {e p : Bundle L} {x : Orthant L}
    (hp : Nonnegative p) (hx : x.val ∈ fullBudget e p)
    (hmax : ∀ y : Orthant L, y.val ∈ fullBudget e p → R.le y x) : ∀ k, 0 < p k := by
  classical
  intro k
  by_contra hk
  have hpk : p k = 0 := le_antisymm (le_of_not_gt hk) (hp k)
  let v : Bundle L := x.val + Pi.single k 1
  have hxv : x.val < v := by
    apply Pi.lt_def.mpr
    refine ⟨fun j => ?_, k, ?_⟩
    · dsimp [v]
      have hnonneg : (0 : ℝ) ≤ (Pi.single k (1 : ℝ) : Bundle L) j := by
        by_cases h : k = j <;> simp [h]
      exact le_add_of_nonneg_right hnonneg
    · simp [v]
  have hv : v ∈ fullBudget e p := by
    refine ⟨fun j => (x.property j).trans (le_of_lt hxv j), ?_⟩
    simpa [v, dot, dotProduct_add, hpk] using hx.2
  exact (hR.strong_mono (x := x) (y := ⟨v, hv.1⟩) hxv).2 (hmax _ hv)

lemma preference_budget_eq_of_full_max (hL : 0 < L)
    (R : CompletePreference (Orthant L)) (hR : PreferenceRegularity R)
    {e p : Bundle L} {x : Orthant L}
    (hp : p ∈ priceSimplex) (hx : x.val ∈ fullBudget e p)
    (hmax : ∀ y : Orthant L, y.val ∈ fullBudget e p → R.le y x) :
    dot p x.val = dot p e := by
  by_contra hne
  have hlt : dot p x.val < dot p e := lt_of_le_of_ne hx.2 hne
  let δ := (dot p e - dot p x.val) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let v : Bundle L := fun k => x.val k + δ
  have hxv : x.val < v := by
    apply Pi.lt_def.mpr
    exact ⟨fun k => by dsimp [v]; linarith, ⟨0, hL⟩, by dsimp [v]; linarith⟩
  have hcost : dot p v = dot p x.val + δ := by
    simp only [dot, dotProduct, v, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul, hp.2, one_mul]
  have hv : v ∈ fullBudget e p := by
    refine ⟨fun j => (x.property j).trans (le_of_lt hxv j), ?_⟩
    rw [hcost]
    dsimp [δ]
    linarith
  exact (hR.strong_mono (x := x) (y := ⟨v, hv.1⟩) hxv).2 (hmax _ hv)

/-- A simultaneous capped preference-demand/auctioneer fixed point is an
unrestricted Walrasian equilibrium with exact market clearing. A household is needed to
force strict positivity of the given fixed-point price; with no households and two goods,
a boundary price also satisfies the fixed-point conditions. -/
theorem competitive_of_cappedDemand (hL : 0 < L)
    {I : Type*} [Fintype I] [Nonempty I]
    (e : I → Bundle L) (R : I → CompletePreference (Orthant L))
    (hR : ∀ i, PreferenceRegularity (R i)) (p : Bundle L) (x : I → Orthant L)
    (hp : p ∈ priceSimplex)
    (hx : ∀ i, (x i).val ∈ cappedDemand (R i) (e i) (resourceCap e) p)
    (hauction : ∀ q ∈ priceSimplex,
      dot q ((∑ i, (x i).val) - ∑ i, e i) ≤ dot p ((∑ i, (x i).val) - ∑ i, e i)) :
    (∀ k, 0 < p k) ∧
    (∀ i, dot p (x i).val = dot p (e i)) ∧
    (∀ i (y : Orthant L), y.val ∈ fullBudget (e i) p → (R i).le y (x i)) ∧
    (∑ i, (x i).val) = ∑ i, e i := by
  have hbudget : ∀ i, dot p (x i).val ≤ dot p (e i) := fun i => (hx i).choose_spec.1.2
  have hfeas := aggregate_le_of_auctioneer e (fun i => (x i).val) p hbudget hauction
  have hslack : ∀ i k, (x i).val k < resourceCap e k := by
    intro i k
    have hle : (x i).val k ≤ (∑ j, (x j).val) k := by
      simpa only [Finset.sum_apply] using
        (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (x j).property k)
          (Finset.mem_univ i))
    have hle' := hle.trans (hfeas k)
    change (x i).val k < (∑ j, e j) k + 1
    linarith
  have hfull : ∀ i, (x i).val ∈ fullBudget (e i) p := fun i => ⟨(x i).property, hbudget i⟩
  have hmax : ∀ i (y : Orthant L), y.val ∈ fullBudget (e i) p → (R i).le y (x i) :=
    fun i => cappedDemand_full_max (R i) (hR i) (hx i) (hslack i)
  have hpos : ∀ k, 0 < p k :=
    preference_price_pos_of_full_max (R (Classical.choice inferInstance))
      (hR (Classical.choice inferInstance)) hp.1
      (hfull _) (hmax _)
  have hbudgeteq : ∀ i, dot p (x i).val = dot p (e i) :=
    fun i => preference_budget_eq_of_full_max hL (R i) (hR i) hp (hfull i) (hmax i)
  exact ⟨hpos, hbudgeteq, hmax,
    clearing_of_pos_budget_eq e (fun i => (x i).val) p hpos hbudgeteq hfeas⟩

end Internal

open Internal

variable {I : Type*} [Fintype I]

/-- Under continuous, convex, strongly monotone preferences and strictly positive
individual endowments, a finite pure-exchange economy has an exact Walrasian equilibrium.
The additional conclusions normalize prices, exclude zero prices, and exhaust budgets.
The household set may be empty: uniform positive prices support the empty allocation.
Positive commodity dimension is necessary because equilibrium prices must be nonzero. -/
theorem exists_walrasianEquilibrium (hL : 0 < L)
    (e : I → Bundle L) (P : I → CompletePreference (Orthant L))
    (he : ∀ i k, 0 < e i k) (hP : ∀ i, PreferenceRegularity (P i)) :
    ∃ (p : Bundle L) (x : I → Orthant L), IsWalrasianEquilibrium e P p x ∧
      (∑ k, p k) = 1 ∧ (∀ k, 0 < p k) ∧
      (∀ i, dot p (x i).val = dot p (e i)) := by
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let p : Bundle L := fun _ => (L : ℝ)⁻¹
    let x : I → Orthant L := isEmptyElim
    have h : 0 < (L : ℝ) := by exact_mod_cast hL
    have hpos : ∀ k, 0 < p k := fun _ => inv_pos.mpr h
    have hsum : (∑ k, p k) = 1 := by simp [p, h.ne']
    refine ⟨p, x, ?_, hsum, hpos, isEmptyElim⟩
    exact {
      endowment_nonneg := isEmptyElim
      price_nonneg := fun k => (hpos k).le
      price_ne_zero := fun hz => by simp [hz] at hsum
      budget_feasible := isEmptyElim
      optimal := isEmptyElim
      clearing := by simp }
  | inr hI =>
    have hM : Nonnegative (resourceCap e) := by
      intro k
      change 0 ≤ (∑ i, e i) k + 1
      have hsum : 0 ≤ (∑ i, e i) k := by
        simp only [Finset.sum_apply]
        exact Finset.sum_nonneg fun i _ => (he i k).le
      linarith
    obtain ⟨p, x, hp, hx, hauction⟩ :=
      exists_capped_fixedPoint hL e P hP (resourceCap e) he hM
    let xs : I → Orthant L := fun i => ⟨x i, (hx i).choose⟩
    obtain ⟨hpos, hbudget, hmax, hclear⟩ :=
      competitive_of_cappedDemand hL e P hP p xs hp hx hauction
    refine ⟨p, xs, ?_, hp.2, hpos, hbudget⟩
    exact {
      endowment_nonneg := fun i k => (he i k).le
      price_nonneg := hp.1
      price_ne_zero := fun hz => by have h := hp.2; simp [hz] at h
      budget_feasible := fun i => (hbudget i).le
      optimal := fun i y hy => hmax i y ⟨y.property, hy⟩
      clearing := hclear }

end MathEconLib.GeneralEquilibrium.PureExchange
