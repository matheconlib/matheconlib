/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Basic
public import MathEconLib.GameTheory.Strategic.Bayesian.Game
public import MathEconLib.Probability.FinDist.Simplex

/-!
# Finite pure Bayesian Nash equilibrium

Players choose actions contingent on their own types. A common finite prior determines interim
payoffs, and equilibrium requires every action deviation to weakly lower payoff at every
positive-probability type. Null types impose no incentive constraint; their conditional payoff is
totalized to zero.

## Main definitions

* `BayesianGame.interimPayoffFin`: Interim payoff under a strategy profile.
* `BayesianGame.interimPayoffActionFin`: Conditional payoff from an action.
* `BayesianGame.bnePredFin`: Player-type deviation problem.
* `BayesianGame.IsBNEFin`: Finite pure Bayesian Nash equilibrium.
* `BayesianGame.expandedGame`: Strategic game with player-type pairs as players.

## Main statements

* `BayesianGame.isBNEFin_iff`: Best-response characterization at positive-marginal types.
* `BayesianGame.isBNEFin_iff_isNash_expandedGame`: Equivalence with Nash equilibrium in the
  expanded game.
* `BayesianGame.isBNEFin_comapActions`: Preservation under action translation.

## Tags

bayesian games, finite types, bayesian nash equilibrium, conditional payoff
-/

@[expose] public noncomputable section

open Function BigOperators MathEconLib.Probability

namespace MathEconLib.GameTheory.BayesianGame

variable {I : Type*} {Θ : I → Type*} {A : I → Type*} {V : Type*}
    [AddCommMonoid V] [Module ℝ V]
    [Fintype I] [DecidableEq I] [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)]
    (G : BayesianGame I Θ A V) (d : FinDist (∀ i, Θ i))

/-- Interim expected payoff for player `i` of type `θ_i` under strategy profile `s`. -/
def interimPayoffFin (i : I) (θ_i : Θ i) (s : G.PureStrategy) : V :=
  ∑ θ ∈ Finset.univ.filter (fun θ : Π j, Θ j => θ i = θ_i),
    d.condProbD i θ_i θ • G.payoff i (G.actionProfile s θ) θ

/-- Interim payoff when player `i` of type `θ_i` deviates to action `a_i` while everyone else
follows `s`. -/
def interimPayoffActionFin (i : I) (θ_i : Θ i) (a_i : A i)
    (s : G.PureStrategy) : V :=
  ∑ θ ∈ Finset.univ.filter (fun θ : Π j, Θ j => θ i = θ_i),
    d.condProbD i θ_i θ •
      G.payoff i (Function.update (G.actionProfile s θ) i a_i) θ

/-- Interim payoff equals `interimPayoffActionFin` at the prescribed action. -/
lemma interimPayoffFin_eq_interimPayoffActionFin (i : I) (θ_i : Θ i)
    (s : ∀ j, Θ j → A j) :
    G.interimPayoffFin d i θ_i s = G.interimPayoffActionFin d i θ_i (s i θ_i) s := by
  unfold interimPayoffFin interimPayoffActionFin
  refine Finset.sum_congr rfl fun θ hθ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  have hupdate_eq : update (G.actionProfile s θ) i (s i θ_i) = G.actionProfile s θ := by
    have haction_eq : s i θ_i = G.actionProfile s θ i := by
      unfold actionProfile
      rw [hθ]
    rw [haction_eq]
    exact update_eq_self i (G.actionProfile s θ)
  rw [hupdate_eq]

/-- Deviating interim payoffs vanish at types with zero marginal probability. -/
lemma interimPayoffActionFin_eq_zero_of_marginal_not_pos (i : I) (θ_i : Θ i)
    (a_i : A i) (s : G.PureStrategy) (h : ¬ 0 < d.marginalD i θ_i) :
    G.interimPayoffActionFin d i θ_i a_i s = 0 := by
  unfold interimPayoffActionFin
  refine Finset.sum_eq_zero fun θ _ => ?_
  rw [d.condProbD_eq_zero_of_not_pos i θ_i θ h, zero_smul]

/-- The interim payoff action only depends on the strategy at player-type pairs other than
`(i, θ_i)`, because player `i`'s action is overwritten by `a_i`. -/
lemma interimPayoffActionFin_eq_of_agree (i : I) (θ_i : Θ i) (a_i : A i)
    (s₁ s₂ : ∀ j, Θ j → A j)
    (h : ∀ (j : I) (θ_j : Θ j),
      (⟨i, θ_i⟩ : Σ k, Θ k) ≠ ⟨j, θ_j⟩ →
        s₁ j θ_j = s₂ j θ_j) :
    G.interimPayoffActionFin d i θ_i a_i s₁ = G.interimPayoffActionFin d i θ_i a_i s₂ := by
  unfold interimPayoffActionFin actionProfile
  refine Finset.sum_congr rfl fun θ hθ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  congr 2
  ext j
  simp only [Function.update]
  split_ifs with hji
  · rfl
  · exact h j _ fun heq => hji (congr_arg Sigma.fst heq).symm

/-- With a point-mass prior, a positive-probability type knows the entire type profile. -/
lemma interimPayoffActionFin_pure (θ : ∀ i, Θ i) (i : I) (a : A i) (s : G.PureStrategy) :
    G.interimPayoffActionFin (FinDist.pure θ) i (θ i) a s =
      G.payoff i (update (G.actionProfile s θ) i a) θ := by
  unfold interimPayoffActionFin
  rw [Finset.sum_eq_single θ]
  · simp [FinDist.condProbD, FinDist.condProb, FinDist.probEvent]
  · intro θ' _ hne
    simp [FinDist.condProbD, FinDist.condProb, Ne.symm hne]
  · simp

/-- Convert a Bayesian strategy profile to an expanded-game strategy profile. -/
def toExpandedProfile (s : G.PureStrategy) :
    Π (p : Σ i, Θ i), A p.1 :=
  fun ⟨i, θ_i⟩ => s i θ_i

/-- Convert an expanded-game profile back to a Bayesian strategy profile. -/
def fromExpandedProfile (profile : Π (p : Σ i, Θ i), A p.1) :
    G.PureStrategy :=
  fun i θ_i => profile ⟨i, θ_i⟩

/-- The equilibrium problem associated with pure-strategy Bayesian Nash equilibrium. The deviator
index is a player–type pair `⟨i, θ_i⟩`; the deviation relation says the new strategy may differ
only at that pair; the value is the interim expected payoff. -/
noncomputable def bnePredFin : EquilibriumProblem G.PureStrategy (Σ i, Θ i) V where
  deviation := fun p s s' =>
    ∀ j θ_j, (⟨j, θ_j⟩ : Σ k, Θ k) ≠ p → s' j θ_j = s j θ_j
  value := fun p s => G.interimPayoffActionFin d p.1 p.2 (s p.1 p.2) s

/-- Pure Bayesian Nash equilibrium: Every player-type deviation weakly lowers its expected
payoff. -/
def IsBNEFin [LE V] (s : G.PureStrategy) : Prop :=
  (G.bnePredFin d).IsEquilibrium s

/-- An admissible deviation changes the strategy only at the specified player-type pair. -/
@[simp] lemma bnePredFin_deviation_iff (p : Σ i, Θ i) (s s' : G.PureStrategy) :
    (G.bnePredFin d).deviation p s s' ↔
      ∀ j θ_j, (⟨j, θ_j⟩ : Σ k, Θ k) ≠ p → s' j θ_j = s j θ_j := Iff.rfl

/-- The equilibrium problem evaluates a player-type pair at its prescribed action. -/
@[simp] lemma bnePredFin_value_eq (p : Σ i, Θ i) (s : G.PureStrategy) :
    (G.bnePredFin d).value p s = G.interimPayoffActionFin d p.1 p.2 (s p.1 p.2) s := rfl

/-- A profile is a Bayesian Nash equilibrium exactly when every action deviation weakly lowers
interim payoff at every type with positive marginal probability. Types with zero marginal
probability impose no incentive constraints. -/
theorem isBNEFin_iff [Preorder V] (s : G.PureStrategy) :
    G.IsBNEFin d s ↔
      ∀ (i : I) (θ_i : Θ i), 0 < d.marginalD i θ_i →
        ∀ (a_i : A i),
          G.interimPayoffActionFin d i θ_i (s i θ_i) s ≥
            G.interimPayoffActionFin d i θ_i a_i s := by
  unfold IsBNEFin
  dsimp only [bnePredFin, EquilibriumProblem.IsEquilibrium]
  refine ⟨?_, ?_⟩
  · intro h i θ_i _hpos a_i
    classical
    let s' : G.PureStrategy := fun j θ_j =>
      if h : (⟨j, θ_j⟩ : Σ k, Θ k) = ⟨i, θ_i⟩ then
        ((Sigma.mk.inj h).1 ▸ a_i : A j)
      else
        s j θ_j
    have hagree :
        ∀ j θ_j, (⟨j, θ_j⟩ : Σ k, Θ k) ≠ ⟨i, θ_i⟩ →
          s' j θ_j = s j θ_j := by
      intro j θ_j hne
      simp only [s', dite_eq_right hne]
    have hdeviating_action : s' i θ_i = a_i := by
      simp only [s', dite_eq_left rfl]
    have hequilibrium_payoff := h ⟨i, θ_i⟩ s' hagree
    have hpayoff_eq : G.interimPayoffActionFin d i θ_i (s' i θ_i) s' =
        G.interimPayoffActionFin d i θ_i a_i s := by
      rw [hdeviating_action]
      exact G.interimPayoffActionFin_eq_of_agree d i θ_i a_i s' s
        (fun j θ_j hne => hagree j θ_j (fun heq => hne heq.symm))
    rwa [hpayoff_eq] at hequilibrium_payoff
  · intro h p s' hagree
    have hpayoff_eq : G.interimPayoffActionFin d p.1 p.2 (s' p.1 p.2) s' =
        G.interimPayoffActionFin d p.1 p.2 (s' p.1 p.2) s :=
      G.interimPayoffActionFin_eq_of_agree d p.1 p.2 (s' p.1 p.2) s' s
        (fun j θ_j hne => hagree j θ_j (fun heq => hne heq.symm))
    rw [hpayoff_eq]
    by_cases hpos : 0 < d.marginalD p.1 p.2
    · exact h p.1 p.2 hpos (s' p.1 p.2)
    · rw [G.interimPayoffActionFin_eq_zero_of_marginal_not_pos d p.1 p.2 _ s hpos,
          G.interimPayoffActionFin_eq_zero_of_marginal_not_pos d p.1 p.2 _ s hpos]

/-- The strategic game whose players are player-type pairs and whose payoffs are interim expected
utilities. -/
def expandedGame : StrategicGame (Σ i, Θ i) (fun p => A p.1) V where
  payoff p s := G.interimPayoffActionFin d p.1 p.2 (s p) (G.fromExpandedProfile s)

/-- The forward `GameMorphism` from the pure BNE problem on `G` to the pure Nash problem on
`G.expandedGame`, with strategy map `toExpandedProfile`. -/
noncomputable def bayesianToStrategicMorphism :
    GameMorphism (G.bnePredFin d) (G.expandedGame d).nashProblem where
  toFun := G.toExpandedProfile
  deviatorMap := id
  deviation_lifts := by
    intro p s σ' ⟨a, hσ'⟩
    classical
    refine ⟨fun j θ_j =>
      if h : (⟨j, θ_j⟩ : Σ k, Θ k) = p then
        ((Sigma.mk.inj h).1 ▸ a : A j)
      else s j θ_j, ?_, ?_⟩
    · intro j θ_j hne
      have hne' : (⟨j, θ_j⟩ : Σ k, Θ k) ≠ p := hne
      change (if h : (⟨j, θ_j⟩ : Σ k, Θ k) = p then _ else s j θ_j) = s j θ_j
      rw [dite_eq_right hne']
    · subst hσ'
      funext q
      obtain ⟨j, θ_j⟩ := q
      by_cases hjp : (⟨j, θ_j⟩ : Σ k, Θ k) = p
      · subst hjp
        change (if h : (⟨j, θ_j⟩ : Σ k, Θ k) = ⟨j, θ_j⟩ then
            ((Sigma.mk.inj h).1 ▸ a : A j) else s j θ_j) =
          Function.update (G.toExpandedProfile s) ⟨j, θ_j⟩ a ⟨j, θ_j⟩
        rw [dite_eq_left rfl, Function.update_self]
      · change (if h : (⟨j, θ_j⟩ : Σ k, Θ k) = p then _ else s j θ_j) =
          Function.update (G.toExpandedProfile s) p a ⟨j, θ_j⟩
        rw [dite_eq_right hjp, Function.update_of_ne hjp]
        rfl
  value_eq := fun _ _ => rfl

/-- The reverse `GameMorphism` from pure Nash on `G.expandedGame` back to pure BNE on `G`, with
strategy map `fromExpandedProfile`, the inverse of `toExpandedProfile`. -/
noncomputable def strategicToBayesianMorphism :
    GameMorphism (G.expandedGame d).nashProblem (G.bnePredFin d) where
  toFun := G.fromExpandedProfile
  deviatorMap := id
  deviation_lifts := by
    intro p σ s' h
    refine ⟨Function.update σ p (s' p.1 p.2), ⟨_, rfl⟩, ?_⟩
    funext i θ_i
    by_cases hpair : (⟨i, θ_i⟩ : Σ k, Θ k) = p
    · subst hpair
      change (Function.update σ ⟨i, θ_i⟩ (s' i θ_i)) ⟨i, θ_i⟩ = s' i θ_i
      rw [Function.update_self]
    · have hupd : (Function.update σ p (s' p.1 p.2)) ⟨i, θ_i⟩ = σ ⟨i, θ_i⟩ :=
        Function.update_of_ne hpair (s' p.1 p.2) σ
      change (Function.update σ p (s' p.1 p.2)) ⟨i, θ_i⟩ = s' i θ_i
      rw [hupd]
      exact (h i θ_i hpair).symm
  value_eq := fun _ _ => rfl

/-- Pure BNE on `G` corresponds to pure Nash on `G.expandedGame`, via the Curry/uncurry strategy
maps `toExpandedProfile` and `fromExpandedProfile`. -/
theorem isBNEFin_iff_isNash_expandedGame [LE V] (s : ∀ i, Θ i → A i) :
    G.IsBNEFin d s ↔
      (G.expandedGame d).IsNash (G.toExpandedProfile s) :=
  ⟨(G.bayesianToStrategicMorphism d).transport, (G.strategicToBayesianMorphism d).transport⟩

/-- Translating an action and the opponents' strategies preserves the interim payoff. -/
lemma interimPayoffActionFin_comapActions {B : I → Type*} (κ : ∀ i, B i → A i)
    (i : I) (t : Θ i) (b : B i) (s : (G.comapActions κ).PureStrategy) :
    (G.comapActions κ).interimPayoffActionFin d i t b s =
      G.interimPayoffActionFin d i t (κ i b) (G.mapPureStrategy κ s) := by
  unfold interimPayoffActionFin
  apply Finset.sum_congr rfl
  intro θ _
  congr 1
  change G.payoff i _ θ = G.payoff i _ θ
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [actionProfile, mapPureStrategy, Function.update_of_ne h]

/-- Action translation maps admissible player-type deviations into admissible deviations. -/
def comapActionsFinComorphism {B : I → Type*} (κ : ∀ i, B i → A i) :
    GameComorphism ((G.comapActions κ).bnePredFin d) (G.bnePredFin d) where
  toFun := G.mapPureStrategy κ
  deviatorMap := id
  deviation_maps := by
    intro p s s' h j t hne
    change κ j (s' j t) = κ j (s j t)
    rw [h j t hne]
  value_eq := by
    intro p s
    exact (G.interimPayoffActionFin_comapActions d κ p.1 p.2 (s p.1 p.2) s).symm

/-- A translated strategy that is a Bayesian equilibrium in the original game gives an equilibrium
in the game with translated actions. -/
theorem isBNEFin_comapActions [LE V] {B : I → Type*} (κ : ∀ i, B i → A i)
    (s : (G.comapActions κ).PureStrategy) (h : G.IsBNEFin d (G.mapPureStrategy κ s)) :
    (G.comapActions κ).IsBNEFin d s :=
  (G.comapActionsFinComorphism d κ).pullback h

end MathEconLib.GameTheory.BayesianGame
