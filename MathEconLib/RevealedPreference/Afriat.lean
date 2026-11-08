/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.GARP

/-!
# The complete finite Afriat theorem

For a nonempty finite dataset, GARP is equivalent to positive-multiplier Afriat
inequalities and to a continuous, concave, strictly increasing utility rationalization.
The explicit utility is the minimum of finitely many affine support planes, defined
on the entire bundle space; rationalization is required on observed nonnegative budgets.

Continuity and concavity hold globally. Strict increase uses weak coordinate dominance
with unequal bundles. Observed choices are weak maximizers: neither unique demand nor
nonempty choice on every unobserved menu is asserted. The lower-envelope construction
requires a nonempty observation type; the graph/certificate theorem also allows empty data.

## References and provenance

Sidney N. Afriat (1967), *The Construction of Utility Functions from Expenditure Data*,
International Economic Review **8**(1), 67–77.
[DOI: 10.2307/2525382](https://doi.org/10.2307/2525382).

Hal R. Varian (1982), *The Nonparametric Approach to Demand Analysis*,
Econometrica **50**(4), 945–973.
[DOI: 10.2307/1912771](https://doi.org/10.2307/1912771).

Ported from Victor H. Aguiar's Apache-2.0 Lean development
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), module `GlobalAfriat`.
The finite classical Afriat result is covered; the pairwise WGARP and infinite-data
extensions are outside this module's scope.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace MathEconLib.RevealedPreference

variable {L : ℕ} {T : Type*}

/-- Lower envelope of the global Afriat support planes. -/
noncomputable def globalAfriatUtility [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L) : Utility L :=
  fun x => Finset.univ.inf' Finset.univ_nonempty
    (fun t => globalAfriatSupport U lam p q t x)

theorem globalAfriatUtility_le_support [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T) (x : Bundle L) :
    globalAfriatUtility U lam p q x ≤
      globalAfriatSupport U lam p q t x := by
  unfold globalAfriatUtility
  exact Finset.inf'_le _ (Finset.mem_univ t)

theorem le_globalAfriatUtility_of_le_supports [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L) {a : ℝ} {x : Bundle L}
    (h : ∀ t, a ≤ globalAfriatSupport U lam p q t x) :
    a ≤ globalAfriatUtility U lam p q x := by
  unfold globalAfriatUtility
  apply Finset.le_inf'
  intro t _ht
  exact h t

@[simp]
theorem globalAfriatSupport_choice_self
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T) :
    globalAfriatSupport U lam p q t (q t) = U t := by
  simp [globalAfriatSupport]

/-- The envelope interpolates every observed Afriat utility level. -/
theorem globalAfriatUtility_eq_observed [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hA : AfriatInequalities U lam p q) (s : T) :
    globalAfriatUtility U lam p q (q s) = U s := by
  apply le_antisymm
  · calc
      globalAfriatUtility U lam p q (q s) ≤
          globalAfriatSupport U lam p q s (q s) :=
        globalAfriatUtility_le_support U lam p q s (q s)
      _ = U s := globalAfriatSupport_choice_self U lam p q s
  · exact le_globalAfriatUtility_of_le_supports U lam p q (hA s)

/-- Every affine support plane is continuous. -/
theorem globalAfriatSupport_continuous
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T) :
    Continuous (globalAfriatSupport U lam p q t) := by
  unfold globalAfriatSupport
  exact continuous_const.add
    (continuous_const.mul ((continuous_dot (p t)).sub continuous_const))

/-- A finite lower envelope of continuous affine planes is continuous. -/
theorem globalAfriatUtility_continuous [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L) :
    Continuous (globalAfriatUtility U lam p q) := by
  unfold globalAfriatUtility
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun t _ht => globalAfriatSupport_continuous U lam p q t)

/-- Exact affine-combination identity for a global support plane. -/
theorem globalAfriatSupport_add_smul
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T)
    (x y : Bundle L) (a b : ℝ) (hab : a + b = 1) :
    globalAfriatSupport U lam p q t (a • x + b • y) =
      a * globalAfriatSupport U lam p q t x +
        b * globalAfriatSupport U lam p q t y := by
  unfold globalAfriatSupport
  rw [dot_add_smul]
  calc
    U t + lam t * (a * dot (p t) x + b * dot (p t) y - dot (p t) (q t)) =
        (a + b) * U t +
          lam t * (a * dot (p t) x + b * dot (p t) y -
            (a + b) * dot (p t) (q t)) := by rw [hab]; ring
    _ = a * (U t + lam t * (dot (p t) x - dot (p t) (q t))) +
        b * (U t + lam t * (dot (p t) y - dot (p t) (q t))) := by ring

/-- Every support plane is affine and hence concave. -/
theorem globalAfriatSupport_concaveOn
    (U lam : T → ℝ) (p q : T → Bundle L) (t : T) :
    ConcaveOn ℝ Set.univ (globalAfriatSupport U lam p q t) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b _ha _hb hab
  rw [globalAfriatSupport_add_smul U lam p q t x y a b hab]
  simp only [smul_eq_mul]
  exact le_rfl

/-- A finite lower envelope of concave functions is concave. -/
theorem globalAfriatUtility_concaveOn [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L) :
    ConcaveOn ℝ Set.univ (globalAfriatUtility U lam p q) := by
  let envelope : Bundle L → ℝ :=
    Finset.univ.inf' Finset.univ_nonempty
      (fun t => globalAfriatSupport U lam p q t)
  have henvelope : ConcaveOn ℝ Set.univ envelope := by
    refine Finset.inf'_induction (s := Finset.univ)
      (H := Finset.univ_nonempty)
      (f := fun t => globalAfriatSupport U lam p q t) ?_ ?_
    · intro f hf g hg
      simpa using hf.inf hg
    · intro t _ht
      exact globalAfriatSupport_concaveOn U lam p q t
  have heq : envelope = globalAfriatUtility U lam p q := by
    funext x
    simp [envelope, globalAfriatUtility, Finset.inf'_apply]
  rw [← heq]
  exact henvelope

/-- A positive multiplier and strictly positive price vector make a global
support plane strictly increasing. -/
theorem globalAfriatSupport_strictlyIncreasing
    (D : Dataset L T) (U lam : T → ℝ) (hpos : PositiveMultipliers lam)
    (t : T) :
    StrictlyIncreasing (globalAfriatSupport U lam D.price D.choice t) := by
  intro x z hxz
  have hdot : dot (D.price t) z < dot (D.price t) x :=
    dot_strictlyIncreasing_of_pos (D.price_pos t) hxz
  have hscaled :
      lam t * (dot (D.price t) z - dot (D.price t) (D.choice t)) <
        lam t * (dot (D.price t) x - dot (D.price t) (D.choice t)) := by
    apply mul_lt_mul_of_pos_left _ (hpos t)
    linarith
  unfold globalAfriatSupport
  linarith

/-- The lower envelope remains strictly increasing because all of its finite
support planes increase strictly. -/
theorem globalAfriatUtility_strictlyIncreasing [Fintype T] [Nonempty T]
    (D : Dataset L T) (U lam : T → ℝ) (hpos : PositiveMultipliers lam) :
    StrictlyIncreasing (globalAfriatUtility U lam D.price D.choice) := by
  intro x z hxz
  unfold globalAfriatUtility
  rw [Finset.lt_inf'_iff]
  intro t _ht
  exact (Finset.inf'_le _ (Finset.mem_univ t)).trans_lt
    (globalAfriatSupport_strictlyIncreasing D U lam hpos t hxz)

/-- The Afriat envelope weakly maximizes at each observed choice on its
budget. -/
theorem globalAfriatUtility_rationalizes [Fintype T] [Nonempty T]
    (D : Dataset L T) (U lam : T → ℝ)
    (hA : AfriatInequalities U lam D.price D.choice)
    (hpos : PositiveMultipliers lam) :
    UtilityRationalizes D (globalAfriatUtility U lam D.price D.choice) := by
  intro t y hy
  have hgap : dot (D.price t) y - dot (D.price t) (D.choice t) ≤ 0 :=
    sub_nonpos.mpr hy.2
  have hscaled :
      lam t * (dot (D.price t) y - dot (D.price t) (D.choice t)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hpos t).le hgap
  calc
    globalAfriatUtility U lam D.price D.choice y ≤
        globalAfriatSupport U lam D.price D.choice t y :=
      globalAfriatUtility_le_support U lam D.price D.choice t y
    _ ≤ U t := by unfold globalAfriatSupport; linarith
    _ = globalAfriatUtility U lam D.price D.choice (D.choice t) :=
      (globalAfriatUtility_eq_observed U lam D.price D.choice hA t).symm

/-- The selected envelope ranks every strictly cheaper bundle strictly below
the observed choice, even without a nonnegativity assumption on that bundle. -/
theorem globalAfriatUtility_strictOnStrictlyAffordable
    [Fintype T] [Nonempty T]
    (D : Dataset L T) (U lam : T → ℝ)
    (hA : AfriatInequalities U lam D.price D.choice)
    (hpos : PositiveMultipliers lam) :
    ∀ t y, expenditure D t y < expenditure D t (D.choice t) →
      globalAfriatUtility U lam D.price D.choice y <
        globalAfriatUtility U lam D.price D.choice (D.choice t) := by
  intro t y hy
  have hscaled :
      lam t * (dot (D.price t) y - dot (D.price t) (D.choice t)) < 0 :=
    mul_neg_of_pos_of_neg (hpos t) (sub_neg.mpr hy)
  calc
    globalAfriatUtility U lam D.price D.choice y ≤
        globalAfriatSupport U lam D.price D.choice t y :=
      globalAfriatUtility_le_support U lam D.price D.choice t y
    _ < U t := by unfold globalAfriatSupport; linarith
    _ = globalAfriatUtility U lam D.price D.choice (D.choice t) :=
      (globalAfriatUtility_eq_observed U lam D.price D.choice hA t).symm

theorem directRP_monotone_of_utilityRationalization
    (D : Dataset L T) (u : Utility L) (hrat : UtilityRationalizes D u)
    {s t : T} (hst : DirectRP D.price D.choice s t) :
    u (D.choice t) ≤ u (D.choice s) := by
  apply hrat s (D.choice t)
  exact ⟨D.choice_nonneg t, hst⟩

theorem revealedPref_monotone_of_utilityRationalization
    (D : Dataset L T) (u : Utility L) (hrat : UtilityRationalizes D u)
    {s t : T} (hst : RevealedPref D.price D.choice s t) :
    u (D.choice t) ≤ u (D.choice s) := by
  refine Relation.ReflTransGen.head_induction_on hst ?_ ?_
  · exact le_rfl
  · intro a b hab _hbc ih
    exact ih.trans (directRP_monotone_of_utilityRationalization D u hrat hab)

/-- A strictly increasing ordinary utility rationalization satisfies GARP.
The proof makes local nonsatiation explicit using the interior-budget
perturbation lemma. -/
theorem garp_of_strictlyIncreasing_utilityRationalization
    (D : Dataset L T) (u : Utility L)
    (hinc : StrictlyIncreasing u) (hrat : UtilityRationalizes D u) :
    GARP D := by
  intro s t hst hcheap
  have hchain : u (D.choice t) ≤ u (D.choice s) :=
    revealedPref_monotone_of_utilityRationalization D u hrat hst
  have hgap : 0 < expenditureGap D t s :=
    (strictlyCheaperAt_dataset_iff D t s).1 hcheap
  obtain ⟨z, hzdom, hzbudget⟩ :=
    exists_strictDominating_affordable D t s hgap
  have hstrict : u (D.choice s) < u z := hinc hzdom
  have hbudget : u z ≤ u (D.choice t) := hrat t z hzbudget
  exact (not_lt_of_ge hchain) (hstrict.trans_le hbudget)

/-- Existence of a continuous, concave, strictly increasing ordinary utility
that rationalizes the finite dataset. -/
def HasRegularUtilityRationalization (D : Dataset L T) : Prop :=
  ∃ u : Utility L,
    Continuous u ∧
    ConcaveOn ℝ Set.univ u ∧
    StrictlyIncreasing u ∧
    UtilityRationalizes D u

/-- Constructive finite Afriat theorem: GARP yields a regular rationalizing
utility, selected as an explicit finite lower envelope. -/
theorem hasRegularUtilityRationalization_of_garp
    [Finite T] [Nonempty T] (D : Dataset L T) (hG : GARP D) :
    HasRegularUtilityRationalization D := by
  let := Fintype.ofFinite T
  obtain ⟨U, lam, hpos, hA⟩ :=
    graphGARP_implies_afriatInequalities D.price D.choice hG
  exact ⟨globalAfriatUtility U lam D.price D.choice,
    globalAfriatUtility_continuous U lam D.price D.choice,
    globalAfriatUtility_concaveOn U lam D.price D.choice,
    globalAfriatUtility_strictlyIncreasing D U lam hpos,
    globalAfriatUtility_rationalizes D U lam hA hpos⟩

/-- Full finite Afriat theorem in the dataset's economic language. -/
theorem garp_iff_hasRegularUtilityRationalization
    [Finite T] [Nonempty T] (D : Dataset L T) :
    GARP D ↔ HasRegularUtilityRationalization D := by
  constructor
  · exact hasRegularUtilityRationalization_of_garp D
  · rintro ⟨u, _hcontinuous, _hconcave, hinc, hrat⟩
    exact garp_of_strictlyIncreasing_utilityRationalization D u hinc hrat

/-- A single theorem exposing both finite Afriat certificates and the regular
rationalizing utility they generate. -/
theorem garp_iff_exists_afriatCertificate_and_regularUtility
    [Fintype T] [Nonempty T] (D : Dataset L T) :
    GARP D ↔
      (∃ U lam,
        PositiveMultipliers lam ∧
        AfriatInequalities U lam D.price D.choice ∧
        Continuous (globalAfriatUtility U lam D.price D.choice) ∧
        ConcaveOn ℝ Set.univ (globalAfriatUtility U lam D.price D.choice) ∧
        StrictlyIncreasing (globalAfriatUtility U lam D.price D.choice) ∧
        UtilityRationalizes D (globalAfriatUtility U lam D.price D.choice)) := by
  constructor
  · intro hG
    obtain ⟨U, lam, hpos, hA⟩ :=
      graphGARP_implies_afriatInequalities D.price D.choice hG
    exact ⟨U, lam, hpos, hA,
      globalAfriatUtility_continuous U lam D.price D.choice,
      globalAfriatUtility_concaveOn U lam D.price D.choice,
      globalAfriatUtility_strictlyIncreasing D U lam hpos,
      globalAfriatUtility_rationalizes D U lam hA hpos⟩
  · rintro ⟨_U, _lam, _hpos, _hA, _hcontinuous, _hconcave, hinc, hrat⟩
    exact garp_of_strictlyIncreasing_utilityRationalization D _ hinc hrat

end MathEconLib.RevealedPreference
