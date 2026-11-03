/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Matching.Contracts.CumulativeOffer.Policies
public import Mathlib.Data.Set.Card

/-!
# Finite termination of cumulative offers

Every productive round adds a fresh contract. Therefore every valid history has at most
as many rounds as contracts, regardless of history-dependent scheduling or tie selection.
A valid deterministic policy reaches economic exhaustion within that bound. No fairness,
substitutability, IRC, or feasibility assumption is used. The selected raw outcome need not
be a feasible matching.
-/

@[expose] public section

namespace MathEconLib.Matching.CumulativeOffer.CumulativeOfferProcess

variable {B S X : Type*} (P : CumulativeOfferProcess B S X)

/-- Productive history length is bounded by the number of accumulated offers. -/
theorem Run.length_le_ncard [Finite X] {h : List (Set X)} (hr : P.Run h) :
    h.length ≤ (offers h).ncard := by
  induction hr with
  | nil => simp
  | @cons h Q _ hQ ih =>
    have hg := Set.ncard_lt_ncard (hQ.ssubset P)
    change h.length + 1 ≤ (offers h ∪ Q).ncard
    exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hg)

/-- No productive run can exceed the number of contracts. -/
theorem Run.length_le_card [Finite X] {h : List (Set X)} (hr : P.Run h) :
    h.length ≤ Nat.card X :=
  (hr.length_le_ncard P).trans (Set.ncard_le_card _)

/-- Run a policy for a bounded number of rounds, stopping at economic exhaustion.
Terminal repetitions do not add empty batches to the history. -/
noncomputable def execute (P : CumulativeOfferProcess B S X) (π : Policy X) : ℕ → List (Set X)
  | 0 => []
  | n + 1 => by
      classical
      let h := P.execute π n
      exact if P.Terminal (offers h) then h else π h :: h

@[simp] theorem execute_zero (π : Policy X) : P.execute π 0 = [] := rfl

/-- A terminal execution remains at the same history. -/
theorem execute_succ_of_terminal (π : Policy X) (n : ℕ)
    (ht : P.Terminal (offers (P.execute π n))) :
    P.execute π (n + 1) = P.execute π n := by
  classical
  simp only [execute, ite_eq_left ht]

/-- A nonterminal execution appends the policy's productive batch. -/
theorem execute_succ_of_not_terminal (π : Policy X) (n : ℕ)
    (ht : ¬ P.Terminal (offers (P.execute π n))) :
    P.execute π (n + 1) = π (P.execute π n) :: P.execute π n := by
  classical
  simp only [execute, ite_eq_right ht]

/-- Execution of a valid policy produces a valid run. -/
theorem execute_run {π : Policy X} (hp : P.ValidPolicy π) (n : ℕ) :
    P.Run (P.execute π n) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    classical
    by_cases ht : P.Terminal (offers (P.execute π n))
    · rw [P.execute_succ_of_terminal π n ht]
      exact ih
    · rw [P.execute_succ_of_not_terminal π n ht]
      exact .cons ih (hp _ ih ht)

/-- Execution uses the policy's own choices. -/
theorem execute_follows (π : Policy X) (n : ℕ) :
    Follows π (P.execute π n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    classical
    by_cases ht : P.Terminal (offers (P.execute π n))
    · rw [P.execute_succ_of_terminal π n ht]
      exact ih
    · rw [P.execute_succ_of_not_terminal π n ht]
      exact ⟨ih, rfl⟩

/-- Before exhaustion, execution has performed every requested round. -/
theorem execute_length_or_terminal (π : Policy X) (n : ℕ) :
    n ≤ (P.execute π n).length ∨ P.Terminal (offers (P.execute π n)) := by
  induction n with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ n ih =>
    classical
    by_cases ht : P.Terminal (offers (P.execute π n))
    · rw [P.execute_succ_of_terminal π n ht]
      exact Or.inr ht
    · rw [P.execute_succ_of_not_terminal π n ht]
      exact Or.inl (Nat.succ_le_succ (ih.resolve_right ht))

/-- Every valid policy terminates after at most the number of contracts in productive rounds. -/
theorem execute_terminal [Finite X] {π : Policy X} (hp : P.ValidPolicy π) :
    P.Terminal (offers (P.execute π (Nat.card X))) := by
  classical
  by_contra ht
  have hn := (P.execute_length_or_terminal π (Nat.card X)).resolve_right ht
  have hr := P.execute_run hp (Nat.card X)
  have hnext : P.Run (π (P.execute π (Nat.card X)) :: P.execute π (Nat.card X)) :=
    .cons hr (hp _ hr ht)
  have hb := hnext.length_le_card P
  simp only [List.length_cons] at hb
  exact (Nat.not_succ_le_self (Nat.card X)) ((Nat.succ_le_succ hn).trans hb)

/-- The policy-indexed raw output; feasibility is a separate economic theorem. -/
noncomputable def rawOutcome [Finite X] (π : Policy X) : Set X :=
  P.heldContracts (offers (P.execute π (Nat.card X)))

/-- The finite policy construction realizes the terminal outcome relation. -/
theorem rawOutcome_isOutcome [Finite X] {π : Policy X} (hp : P.ValidPolicy π) :
    P.Outcome (P.rawOutcome π) :=
  ⟨P.execute π (Nat.card X), P.execute_run hp _, P.execute_terminal hp, rfl⟩

/-- Every valid history following a policy is reproduced by executing that many rounds.
No global validity assumption on the policy or finiteness assumption is needed. -/
theorem Run.execute_length {π : Policy X} {h : List (Set X)} (hr : P.Run h) :
    Follows π h → P.execute π h.length = h := by
  induction hr with
  | nil => intro _; rfl
  | @cons h Q _ hQ ih =>
    intro hf
    have he := ih hf.1
    have ht : ¬ P.Terminal (offers (P.execute π h.length)) := by
      rw [he]
      exact hQ.not_terminal P
    rw [List.length_cons, P.execute_succ_of_not_terminal π h.length ht, he, ← hf.2]

/-- Once execution is terminal, any additional number of rounds leaves the history unchanged. -/
theorem execute_add_of_terminal (π : Policy X) (n : ℕ)
    (ht : P.Terminal (offers (P.execute π n))) (k : ℕ) :
    P.execute π (n + k) = P.execute π n := by
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
    have hterminal : P.Terminal (offers (P.execute π (n + k))) := by
      rw [ih]
      exact ht
    rw [Nat.add_succ, P.execute_succ_of_terminal π (n + k) hterminal, ih]

/-- Any terminal run following a fixed policy is the finite execution of that policy.
This is uniqueness for one policy, not independence across different proposal policies. -/
theorem Run.execute_card_eq [Finite X] {π : Policy X} {h : List (Set X)}
    (hr : P.Run h) (hf : Follows π h) (ht : P.Terminal (offers h)) :
    P.execute π (Nat.card X) = h := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hr.length_le_card P)
  have he := hr.execute_length P hf
  have hterminal : P.Terminal (offers (P.execute π h.length)) := by
    rw [he]
    exact ht
  rw [hk, P.execute_add_of_terminal π h.length hterminal k, he]

/-- Terminal runs following the same deterministic policy have identical batch histories. -/
theorem Run.eq_of_terminal_of_follows [Finite X] {π : Policy X}
    {h k : List (Set X)} (hr : P.Run h) (kr : P.Run k)
    (hf : Follows π h) (kf : Follows π k)
    (ht : P.Terminal (offers h)) (kt : P.Terminal (offers k)) : h = k :=
  (hr.execute_card_eq P hf ht).symm.trans (kr.execute_card_eq P kf kt)

/-- The held contracts of any terminal run following a policy equal its selected raw outcome. -/
theorem Run.heldContracts_eq_rawOutcome [Finite X] {π : Policy X}
    {h : List (Set X)} (hr : P.Run h) (hf : Follows π h)
    (ht : P.Terminal (offers h)) :
    P.heldContracts (offers h) = P.rawOutcome π := by
  unfold rawOutcome
  rw [hr.execute_card_eq P hf ht]

/-- A valid finite policy's raw outcome is exactly the outcome of a terminal run following it.
The unrestricted `Outcome` relation may still contain outcomes from other policies. -/
theorem rawOutcome_eq_iff [Finite X] {π : Policy X} (hp : P.ValidPolicy π) (Z : Set X) :
    P.rawOutcome π = Z ↔
      ∃ h, P.Run h ∧ Follows π h ∧ P.Terminal (offers h) ∧
        P.heldContracts (offers h) = Z := by
  constructor
  · intro hZ
    exact ⟨P.execute π (Nat.card X), P.execute_run hp _, P.execute_follows π _,
      P.execute_terminal hp, hZ⟩
  · rintro ⟨h, hr, hf, ht, hZ⟩
    exact (hr.heldContracts_eq_rawOutcome P hf ht).symm.trans hZ

end MathEconLib.Matching.CumulativeOffer.CumulativeOfferProcess

