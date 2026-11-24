/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.Choice.Compact
public import MathEconLib.GeneralEquilibrium.PureExchange.Basic
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences

/-!
# Capped preference demand at boundary prices

This implementation layer derives maximizer attainment, compactness, convexity, and upper
hemicontinuity from the declared preference conditions. Capped demand uses the shared
`Choice.maximizers` correspondence. Separate closed upper and lower contours suffice for
the varying-price graph argument; no utility representation, demand selection, or jointly
closed preference graph is assumed. Positive limiting endowment income is explicit.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Topology
open MathEconLib.Preferences MathEconLib.RevealedPreference Set Filter

namespace MathEconLib.GeneralEquilibrium.PureExchange
namespace Internal

variable {L : ℕ}

/-- The temporary box is compact in finite commodity dimension. -/
theorem isCompact_consumptionBox (M : Bundle L) : IsCompact (consumptionBox M) :=
  isCompact_Icc

/-- A capped budget is a closed subset of the temporary box. -/
theorem isClosed_cappedBudget (e M p : Bundle L) : IsClosed (cappedBudget e M p) :=
  isClosed_Icc.inter (isClosed_le (continuous_dot p) continuous_const)

/-- Capped budgets are compact, without any price sign restriction. -/
theorem isCompact_cappedBudget (e M p : Bundle L) : IsCompact (cappedBudget e M p) :=
  (isCompact_consumptionBox M).of_isClosed_subset (isClosed_cappedBudget e M p)
    (fun _ hx => hx.1)

/-- Capped budgets are convex, without any price sign restriction. -/
theorem convex_cappedBudget (e M p : Bundle L) : Convex ℝ (cappedBudget e M p) := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_Icc (0 : Bundle L) M) hx.1 hy.1 ha hb hab, ?_⟩
  rw [dot_add_smul]
  calc
    a * dot p x + b * dot p y ≤ a * dot p e + b * dot p e :=
      add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    _ = dot p e := by rw [← add_mul, hab, one_mul]

/-- Nonnegative wealth makes zero affordable inside a nonnegative cap. -/
theorem zero_mem_cappedBudget {e M p : Bundle L}
    (hM : Nonnegative M) (hm : 0 ≤ dot p e) : (0 : Bundle L) ∈ cappedBudget e M p := by
  exact ⟨⟨le_rfl, hM⟩, by simpa using hm⟩

/-- Radial contraction stays in the temporary nonnegative box. -/
theorem smul_mem_consumptionBox {M y : Bundle L} (hy : y ∈ consumptionBox M)
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) : a • y ∈ consumptionBox M := by
  constructor
  · intro k
    exact mul_nonneg ha (hy.1 k)
  · intro k
    exact (mul_le_mul_of_nonneg_right ha' (hy.1 k)).trans (by simpa using hy.2 k)

/-- Joint continuity of expenditure along a filter. -/
theorem tendsto_dot {A : Type*} {l : Filter A}
    {ps xs : A → Bundle L} {p x : Bundle L}
    (hp : Tendsto ps l (𝓝 p)) (hx : Tendsto xs l (𝓝 x)) :
    Tendsto (fun n => dot (ps n) (xs n)) l (𝓝 (dot p x)) :=
  ((continuous_fst.dotProduct continuous_snd).tendsto (p, x)).comp (hp.prodMk_nhds hx)

variable {L : ℕ}

lemma isClosed_nonnegative : IsClosed {x : Bundle L | Nonnegative x} :=
  isClosed_Ici

lemma isClosedEmbedding_orthant_val :
    Topology.IsClosedEmbedding (Subtype.val : Orthant L → Bundle L) :=
  Topology.IsClosedEmbedding.subtypeVal isClosed_nonnegative

/-- Closed upper contours remain closed in ambient commodity space because the
consumption orthant itself is closed. -/
lemma isClosed_upperContour (R : CompletePreference (Orthant L))
    (hR : PreferenceRegularity R) (x : Orthant L) :
    IsClosed {y : Bundle L | ∃ hy : Nonnegative y, R.le x ⟨y, hy⟩} := by
  have h := isClosed_nonnegative.isClosedMap_subtype_val _ (hR.closed_upper x)
  convert h using 1
  ext y
  constructor
  · rintro ⟨hy, hxy⟩
    exact ⟨⟨y, hy⟩, hxy, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.property, hz⟩

/-- Capped preference demand retains every optimum and its budget feasibility. -/
def cappedDemand (R : CompletePreference (Orthant L)) (e M p : Bundle L) : Set (Bundle L) :=
  {x | ∃ hx : Nonnegative x, (⟨x, hx⟩ : Orthant L) ∈
    Choice.maximizers R.toPreference {y | y.val ∈ cappedBudget e M p}}

lemma cappedDemand_subset_box (R : CompletePreference (Orthant L)) (e M p : Bundle L) :
    cappedDemand R e M p ⊆ consumptionBox M := by
  rintro x ⟨_, hx, _⟩
  exact hx.1

lemma cappedDemand_nonempty (R : CompletePreference (Orthant L)) (hR : PreferenceRegularity R)
    {e M p : Bundle L}
    (hM : Nonnegative M) (hm : 0 ≤ dot p e) :
    (cappedDemand R e M p).Nonempty := by
  let S : Set (Orthant L) := {x | x.val ∈ cappedBudget e M p}
  have hcompact : IsCompact S :=
    isClosedEmbedding_orthant_val.isCompact_preimage (isCompact_cappedBudget e M p)
  have hne : S.Nonempty :=
    ⟨⟨0, fun _ => le_rfl⟩, zero_mem_cappedBudget hM hm⟩
  obtain ⟨x, hx, hmax⟩ := Choice.maximizers_nonempty_of_isCompact
    R hcompact hne (fun x _ => hR.closed_upper x)
  exact ⟨x.val, x.property, hx, hmax⟩

lemma isClosed_cappedDemand (R : CompletePreference (Orthant L))
    (hR : PreferenceRegularity R) (e M p : Bundle L) :
    IsClosed (cappedDemand R e M p) := by
  rcases (cappedDemand R e M p).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h]
    exact isClosed_empty
  obtain ⟨hxn, hxb, hxm⟩ := hx
  have heq : cappedDemand R e M p = cappedBudget e M p ∩
      {y : Bundle L | ∃ hy : Nonnegative y, R.le ⟨x, hxn⟩ ⟨y, hy⟩} := by
    ext y
    constructor
    · rintro ⟨hyn, hyb, hym⟩
      exact ⟨hyb, hyn, hym hxb⟩
    · rintro ⟨hyb, hyn, hxy⟩
      exact ⟨hyn, hyb, fun z hz => R.le_trans (hxm hz) hxy⟩
  rw [heq]
  exact (isClosed_cappedBudget e M p).inter (isClosed_upperContour R hR ⟨x, hxn⟩)

lemma isCompact_cappedDemand (R : CompletePreference (Orthant L))
    (hR : PreferenceRegularity R) (e M p : Bundle L) :
    IsCompact (cappedDemand R e M p) :=
  (isCompact_consumptionBox M).of_isClosed_subset (isClosed_cappedDemand R hR e M p)
    (cappedDemand_subset_box R e M p)

lemma convex_cappedDemand (R : CompletePreference (Orthant L))
    (hR : PreferenceRegularity R) (e M p : Bundle L) :
    Convex ℝ (cappedDemand R e M p) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hxn, hxb, hxm⟩ := hx
  obtain ⟨hyn, hyb, hym⟩ := hy
  have hbudget := convex_cappedBudget e M p hxb hyb ha hb hab
  refine ⟨hbudget.1.1, hbudget, ?_⟩
  intro z hz
  obtain ⟨_, hrel⟩ := hR.convex_upper z ⟨hxn, hxm hz⟩ ⟨hyn, hym hz⟩ ha hb hab
  exact hrel


/-- Radial contraction coefficients tending to 1 from below. -/
noncomputable def radialWeight (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 1)

lemma radialWeight_nonneg (n : ℕ) : 0 ≤ radialWeight n := by
  dsimp [radialWeight]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  linarith

lemma radialWeight_lt_one (n : ℕ) : radialWeight n < 1 := by
  dsimp [radialWeight]
  have hdiv : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

lemma tendsto_radialWeight : Tendsto radialWeight atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1)
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Closed demand graph derived from the two separate closed contour conditions.
No utility representation or jointly closed preference graph is assumed. -/
theorem cappedDemand_mem_of_tendsto
    (R : CompletePreference (Orthant L)) (hR : PreferenceRegularity R)
    {A : Type*} {l : Filter A} [NeBot l]
    {e M p x : Bundle L} {ps xs : A → Bundle L}
    (hm : 0 < dot p e)
    (hp : Tendsto ps l (𝓝 p)) (hx : Tendsto xs l (𝓝 x))
    (hd : ∀ n, xs n ∈ cappedDemand R e M (ps n)) :
    x ∈ cappedDemand R e M p := by
  have hnonneg : ∀ n, Nonnegative (xs n) := fun n => (hd n).choose
  have hbox : x ∈ consumptionBox M :=
    isClosed_Icc.mem_of_tendsto hx
      (Eventually.of_forall (fun n => (hd n).choose_spec.1.1))
  have hbudget : dot p x ≤ dot p e :=
    le_of_tendsto_of_tendsto (tendsto_dot hp hx) (tendsto_dot hp tendsto_const_nhds)
      (Eventually.of_forall (fun n => (hd n).choose_spec.1.2))
  have hxsub : Tendsto (fun n => (⟨xs n, hnonneg n⟩ : Orthant L)) l
      (𝓝 (⟨x, hbox.1⟩ : Orthant L)) := tendsto_subtype_rng.mpr hx
  refine ⟨hbox.1, ⟨hbox, hbudget⟩, ?_⟩
  intro y hy
  have hstrict (a : ℝ) (ha : 0 ≤ a) (ha' : a < 1) :
      R.le ⟨a • y.val, (smul_mem_consumptionBox hy.1 ha ha'.le).1⟩ ⟨x, hbox.1⟩ := by
    have hcost : dot p (a • y.val) < dot p e := by
      calc
        dot p (a • y.val) = a * dot p y.val := by
          simp only [dot, dotProduct_smul, smul_eq_mul]
        _ ≤ a * dot p e := mul_le_mul_of_nonneg_left hy.2 ha
        _ < dot p e := by nlinarith
    have ht : Tendsto (fun n => dot (ps n) (a • y.val) - dot (ps n) e) l
        (𝓝 (dot p (a • y.val) - dot p e)) :=
      (tendsto_dot hp tendsto_const_nhds).sub (tendsto_dot hp tendsto_const_nhds)
    apply (hR.closed_upper
      ⟨a • y.val, (smul_mem_consumptionBox hy.1 ha ha'.le).1⟩).mem_of_tendsto hxsub
    filter_upwards [ht.eventually_lt_const (sub_neg.mpr hcost)] with n hcostn
    exact (hd n).choose_spec.2
      ⟨smul_mem_consumptionBox hy.1 ha ha'.le, (sub_neg.mp hcostn).le⟩
  have hay : Tendsto
      (fun n => (⟨radialWeight n • y.val,
        (smul_mem_consumptionBox hy.1 (radialWeight_nonneg n)
          (radialWeight_lt_one n).le).1⟩ : Orthant L)) atTop (𝓝 y) := by
    apply tendsto_subtype_rng.mpr
    simpa using tendsto_radialWeight.smul (tendsto_const_nhds (x := y.val))
  exact (hR.closed_lower ⟨x, hbox.1⟩).mem_of_tendsto hay
    (Eventually.of_forall (fun n => hstrict (radialWeight n)
      (radialWeight_nonneg n) (radialWeight_lt_one n)))

/-- Positive endowment income gives upper hemicontinuity on the specified price
set, derived from separate contour continuity and compact box containment. -/
theorem upperHemicontinuous_cappedDemand
    (R : CompletePreference (Orthant L)) (hR : PreferenceRegularity R) (e M : Bundle L)
    (P : Set (Bundle L))
    (hm : ∀ p ∈ P, 0 < dot p e) :
    UpperHemicontinuous (fun p : P => cappedDemand R e M p.val) := by
  intro p
  apply UpperHemicontinuousAt.of_sequences (isCompact_consumptionBox M).isSeqCompact
    (Eventually.of_forall (fun q x hx => hx.choose_spec.1.1))
  intro ps hps xs hxs x hx
  exact cappedDemand_mem_of_tendsto R hR (hm p.val p.property)
    (continuous_subtype_val.tendsto p |>.comp hps) hx hxs

end Internal
end MathEconLib.GeneralEquilibrium.PureExchange
