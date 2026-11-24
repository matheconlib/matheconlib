/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLib.RevealedPreference

/-!
# Finite revealed-preference API pins

These clients import the public umbrella. Graph/certificate equivalence needs finite
observations but no nonemptiness or price restrictions. Regular rationalization uses
the dataset's positive prices and nonnegative choices, with nonempty observations.
-/

-- This module only contains anonymous compile-time clients.
set_option linter.privateModule false

open MathEconLib.RevealedPreference

example {L : ℕ} {x z : Bundle L} : StrictDominates x z ↔ z < x :=
  strictDominates_iff_lt

example {L : ℕ} {u : Utility L} : StrictlyIncreasing u ↔ StrictMono u :=
  strictlyIncreasing_iff_strictMono

-- The certificate and utility converses do not assume finite observations.
example {L : ℕ} {T : Type*} (U lam : T → ℝ) (p q : T → Bundle L)
    (hA : AfriatInequalities U lam p q) (hpos : PositiveMultipliers lam) :
    GraphGARP p q :=
  afriatInequalities_imply_graphGARP U lam p q hA hpos

example {L : ℕ} {T : Type*} (D : Dataset L T) (u : Utility L)
    (hinc : StrictlyIncreasing u) (hrat : UtilityRationalizes D u) : GARP D :=
  garp_of_strictlyIncreasing_utilityRationalization D u hinc hrat

example {L : ℕ} {T : Type*} [Finite T] (p q : T → Bundle L) :
    GraphGARP p q ↔
      ∃ U lam, PositiveMultipliers lam ∧ AfriatInequalities U lam p q :=
  graphGARP_iff_exists_afriatInequalities p q

example {L : ℕ} {T : Type*} [Finite T] (D : Dataset L T) :
    GARP D ↔ ∃ U lam, PositiveMultipliers lam ∧
      AfriatInequalities U lam D.price D.choice :=
  garp_iff_exists_afriatInequalities D

example {L : ℕ} {T : Type*} [Finite T] [Nonempty T] (D : Dataset L T) :
    GARP D ↔ HasRegularUtilityRationalization D :=
  garp_iff_hasRegularUtilityRationalization D

example {L : ℕ} {T : Type*} [Fintype T] [Nonempty T] (D : Dataset L T) :
    GARP D ↔ ∃ U lam,
      PositiveMultipliers lam ∧ AfriatInequalities U lam D.price D.choice ∧
      Continuous (globalAfriatUtility U lam D.price D.choice) ∧
      ConcaveOn ℝ Set.univ (globalAfriatUtility U lam D.price D.choice) ∧
      StrictlyIncreasing (globalAfriatUtility U lam D.price D.choice) ∧
      UtilityRationalizes D (globalAfriatUtility U lam D.price D.choice) :=
  garp_iff_exists_afriatCertificate_and_regularUtility D

-- An empty observation type is admissible for graph/certificate equivalence.
example (p q : Fin 0 → Bundle 1) :
    ∃ U lam, PositiveMultipliers lam ∧ AfriatInequalities U lam p q := by
  apply (graphGARP_iff_exists_afriatInequalities p q).mp
  intro s
  exact Fin.elim0 s

-- These bridges need no finiteness or nonemptiness hypothesis on observations.
example {L : ℕ} {T : Type*} (D : Dataset L T) (u : Utility L) :
    UtilityRationalizes D u ↔ ∀ t, D.choice t ∈
      MathEconLib.Choice.maximizers (MathEconLib.Preferences.Preference.ofUtility u)
        (budgetSet D t) :=
  utilityRationalizes_iff_mem_maximizers D u

example {L : ℕ} {T : Type*} (D : Dataset L T) (u : Utility L) :
    UtilityRationalizes D u ↔ ∀ t, D.choice t ∈ utilityChoice u (budgetSet D t) :=
  utilityRationalizes_iff_mem_utilityChoice D u

example {L : ℕ} (u : Utility L) : MathEconLib.Choice.ChoiceFunction (Bundle L) :=
  utilityChoice u

example {L : ℕ} {T : Type*} [Finite T] [Nonempty T] (D : Dataset L T) :
    GARP D ↔ ∃ u : Utility L,
      Continuous u ∧ ConcaveOn ℝ Set.univ u ∧ StrictlyIncreasing u ∧
      ∀ t, D.choice t ∈ utilityChoice u (budgetSet D t) :=
  garp_iff_exists_regular_utilityChoice D

example {L : ℕ} {T : Type*} (D : Dataset L T) (u : Utility L)
    (h : UtilityRationalizes D u) (t : T) :
    (utilityChoice u (budgetSet D t)).Nonempty :=
  utilityChoice_budgetSet_nonempty D u h t

-- Constant utility retains every feasible alternative, including ties.
example {L : ℕ} (S : Set (Bundle L)) : utilityChoice (fun _ => 0) S = S := by
  ext x
  simp [mem_utilityChoice, isMaxOn_iff]

-- A nonempty unbounded menu need not attain its utility supremum.
example : utilityChoice (fun x : Bundle 1 => x 0) Set.univ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hmax := (mem_utilityChoice _ _ _).mp hx
  have h := isMaxOn_iff.mp hmax.2 (fun i => x i + 1) (Set.mem_univ _)
  linarith
