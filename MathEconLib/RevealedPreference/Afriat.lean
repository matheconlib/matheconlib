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

theorem directlyRevealedPreferred_mono_of_utilityRationalization
    (D : Dataset L T) (u : Utility L) (hrat : UtilityRationalizes D u)
    {s t : T} (hst : DirectlyRevealedPreferred D.price D.choice s t) :
    u (D.choice t) ≤ u (D.choice s) := by
  apply hrat s (D.choice t)
  exact ⟨D.choice_nonneg t, hst⟩

theorem revealedPreferred_mono_of_utilityRationalization
    (D : Dataset L T) (u : Utility L) (hrat : UtilityRationalizes D u)
    {s t : T} (hst : RevealedPreferred D.price D.choice s t) :
    u (D.choice t) ≤ u (D.choice s) := by
  exact revealedPreferred_mono D.price D.choice (fun t => u (D.choice t))
    (fun {_ _} h => directlyRevealedPreferred_mono_of_utilityRationalization D u hrat h) hst

/-- A strictly increasing ordinary utility rationalization satisfies GARP.
The proof makes local nonsatiation explicit using the interior-budget
perturbation lemma. -/
theorem garp_of_strictlyIncreasing_utilityRationalization
    (D : Dataset L T) (u : Utility L)
    (hinc : StrictlyIncreasing u) (hrat : UtilityRationalizes D u) :
    GARP D := by
  intro s t hst hcheap
  have hchain : u (D.choice t) ≤ u (D.choice s) :=
    revealedPreferred_mono_of_utilityRationalization D u hrat hst
  have hgap : 0 < expenditureGap D t s :=
    (strictlyCheaperAt_iff_expenditureGap_pos D t s).1 hcheap
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
    globalAfriatUtility_strictlyIncreasing U lam D.price D.choice D.price_pos hpos,
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
      globalAfriatUtility_strictlyIncreasing U lam D.price D.choice D.price_pos hpos,
      globalAfriatUtility_rationalizes D U lam hA hpos⟩
  · rintro ⟨_U, _lam, _hpos, _hA, _hcontinuous, _hconcave, hinc, hrat⟩
    exact garp_of_strictlyIncreasing_utilityRationalization D _ hinc hrat

end MathEconLib.RevealedPreference
