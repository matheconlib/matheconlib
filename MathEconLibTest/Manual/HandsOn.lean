import MathEconLib.BidderProblem.Basic

/-!
# Hands-on exercises from the Beginner's Manual

Every runnable Lean snippet from the ✍️ blocks in
[`docs/BeginnersManual.md`](../../docs/BeginnersManual.md), collected so that
`lake build` checks them. If the library or the toolchain moves and a snippet
in the manual stops working, this file goes red and the manual gets fixed.

Three kinds of snippet in the manual are **not** here:

* examples that are *meant* to fail. They appear below as comments, each
  labelled with the error the reader should see on uncommenting.
* fragments quoted from the library itself — structure fields, `namespace`
  openers, the real `BidderProblem` declaration — which are not standalone
  and would collide with the definitions they are quoting.
* the module-system header lines from §4.0, which only make sense at the top
  of a file. This file's own header is the working example.

Declarations live in the `Manual` namespace so the throwaway names here cannot
clash with anything in the library.

Unlike the rest of the library, this file deliberately omits the `module`
header. A reader following the manual works in a plain scratch file, and some
of the commands the manual uses — `#print axioms` among them — are rejected
inside a module. Omitting it keeps this file faithful to the reader's setup.
-/

-- The manual writes `(0:ℝ)` throughout, which the project's whitespace linter
-- would rather see as `(0 : ℝ)`. Snippets are reproduced as the manual spells
-- them, so the check tests what a reader would actually type.
set_option linter.style.whitespace false

namespace Manual

open MathEconLib

open Set

/-! ## Part 1 — meet the kernel -/

example : (2:ℝ) + 2 = 4 := by norm_num

-- Meant to fail: `unsolved goals ⊢ False`
-- example : (2:ℝ) + 2 = 5 := by norm_num

#print axioms Nat.add_comm
#print axioms Real.sqrt_nonneg

/-! ## Part 2.1 — define, then interrogate -/

def double (x : ℝ) : ℝ := 2 * x

#check double

def doubleN (n : ℕ) : ℕ := 2 * n

#eval doubleN 5

#eval double 5

-- Meant to fail: `:` where `:=` belongs
-- def bad (x : ℝ) : ℝ : 2 * x

def alsoFine (x : ℝ) := 2 * x

#check alsoFine

/-! ## Part 2.2 — application binds tightest -/

def f (n : ℕ) : ℕ := n * 10

#eval f 2 + 1
#eval f (2 + 1)

#check fun (x : ℝ) => x + 1
#eval (fun (n : ℕ) => n + 1) 5
#check fun (_ : ℝ) => (1:ℝ) / 2

/-! ## Part 2.3 — type the symbols -/

example : ∀ x : ℝ, x ≤ x := fun x => le_refl x

#check @le_refl

example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ x ∧ x ≤ 1 := h
example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ x := h.1
example : (0:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 2 := ⟨by norm_num, by norm_num⟩

/-! ## Part 2.4 — named versus anonymous -/

theorem my_two_pos : (0:ℝ) < 2 := by norm_num

example : (0:ℝ) < 2 := by norm_num

#check my_two_pos

-- Meant to fail: `two_pos` has already been declared (Mathlib got there first)
-- theorem two_pos : (0:ℝ) < 2 := by norm_num

/-! ## Part 2.5 — a first taste of tactics -/

example (x : ℝ) : 0 ≤ x ^ 2 := by positivity
example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
example (x : ℝ) (h : 0 ≤ x) : 0 ≤ 2 * x := by linarith
example : ∀ x : ℝ, x + 0 = x := by intro x; ring

-- Meant to fail: `linarith failed to find a contradiction` (x ^ 2 is nonlinear)
-- example (x : ℝ) (h : 0 ≤ x) : 0 ≤ x ^ 2 := by linarith

/-! ## Part 3.1 — `#check` everything -/

#check (3 : ℝ)
#check fun (x : ℝ) => x ^ 2
#check ℕ
#check (2 + 2 = 4)
#check Set.Icc (0:ℝ) 1
#check @Nat.add_comm

/-! ## Part 3.2 — the two worlds side by side -/

#check (true : Bool)
#eval (2 + 2 == 4 : Bool)
#check (2 + 2 = 4)
#check (2 + 2 = 5)

#check (1 < 2)
#eval decide ((1:ℕ) < 2)
#eval (2 + 2 = 4)

/-! ## Part 3.3 — fill some boxes -/

example : (3:ℝ) * 3 = 9 := by norm_num
example (x : ℝ) : x ^ 2 - x ^ 2 = 0 := by ring

theorem my_fact : (2:ℝ) + 2 = 4 := by norm_num

example : (2:ℝ) + 2 = 4 := my_fact
example : (4:ℝ) = 2 + 2 := my_fact.symm

#check @Eq.symm

/-! ## Part 3.4 — watch a type get computed -/

#check Fin 3
#check fun n => Fin n
#check fun (n : ℕ) => (Fin n → ℝ)

/-! ## Part 3.5 — build one, then try to cheat -/

noncomputable def coinFlip : BidderProblem where
  lowestType    := 0
  highestType   := 1
  winProb       := fun _ => 1 / 2
  winProb_range := by intro x; norm_num [Set.mem_Icc]
  cost          := fun b => b
  strategy      := id

noncomputable def alwaysWins : BidderProblem where
  lowestType    := 0
  highestType   := 10
  winProb       := fun _ => 1
  winProb_range := by intro x; norm_num [Set.mem_Icc]
  cost          := fun b => b
  strategy      := id

#check alwaysWins.winProb_range

-- Cheat 1, an impossible probability: error lands on the proof field,
-- `unsolved goals ⊢ False`.
-- Cheat 2, deleting `winProb_range`: `error: Fields missing: 'winProb_range'`

/-! ## Part 3.6 — apply proofs like functions -/

example (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) : 0 ≤ g 3 := hg 3
example (P Q : Prop) (h : P → Q) (hp : P) : Q := h hp
example (B : BidderProblem) : B.q 5 ∈ Set.Icc 0 1 := B.winProb_range (B.strategy 5)

-- Meant to fail: type mismatch, the `∀` was never applied to an argument
-- example (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) : 0 ≤ g 3 := hg

/-! ## Part 3.7 — proofs interchangeable, data not -/

example (h₁ h₂ : ∀ x, coinFlip.winProb x ∈ Icc 0 1) : h₁ = h₂ := rfl
example (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl
example (x : ℝ) (h₁ h₂ : 0 ≤ x) : h₁ = h₂ := rfl

-- Meant to fail: data is data, `rfl` cannot prove `a = b`
-- example (a b : ℝ) : a = b := rfl

/-! ## Part 3.8 — state a property no ordinary type system can -/

#check ∀ (l : List ℕ), l.Pairwise (· ≤ ·)
#check ∀ (g : ℝ → ℝ), Monotone g
#check ∀ (g : ℝ → ℝ), ∀ x, g x ∈ Set.Icc (0:ℝ) 1

def BoundedFn : Type := { g : ℝ → ℝ // ∀ x, g x ∈ Set.Icc (0:ℝ) 1 }

#check BoundedFn

/-! ## Part 4.1 — open the real thing -/

#check BidderProblem.winProb
#check BidderProblem.cost
#check BidderProblem.strategy
#check BidderProblem.payoff

/-! ## Part 4.2 — your own record with a proof field -/

structure UnitReal where
  val : ℝ
  property : val ∈ Set.Icc (0:ℝ) 1

noncomputable def half : UnitReal where
  val      := 1 / 2
  property := by norm_num [Set.mem_Icc]

#check half.val
#check half.property
#check UnitReal.mk

noncomputable def halfAnon : UnitReal := ⟨1/2, by norm_num [Set.mem_Icc]⟩

/-! ## Part 4.3 — intervals, and the junk values -/

#check Set.Icc (0:ℝ) 1

example : (0.5 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num [Set.mem_Icc]
example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : x ≤ 1 := h.2

example : (1:ℝ) / 0 = 0 := by simp
example : Real.log 0 = 0 := by simp

/-! ## Part 4.4 — dot notation is just a lookup rule -/

example (B : BidderProblem) (v : ℝ) : 0 ≤ B.q v := (B.q_range v).1
example (B : BidderProblem) (v : ℝ) : 0 ≤ B.q v := (BidderProblem.q_range B v).1

example (a b : ℝ) (h : a = b) : b = a := h.symm
example (a b c : ℝ) (h : a = b) (h' : b = c) : a = c := h.trans h'
example (P Q : Prop) (h : P ∧ Q) : Q := h.2

/-! ## Part 4.5 — feel why the `simp` lemma is needed -/

def myPayoff (v b : ℝ) : ℝ := v * b - b

@[simp] lemma myPayoff_eq (v b : ℝ) : myPayoff v b = v * b - b := rfl

example (v : ℝ) : myPayoff v 0 = 0 := by simp
example (v : ℝ) : myPayoff v 1 = v - 1 := by simp

example (v : ℝ) : myPayoff v 0 = 0 := by simp [myPayoff_eq]
example (v : ℝ) : myPayoff v 0 = 0 := by unfold myPayoff; ring

/-! ## Part 4.6 — assumptions that arrive by themselves -/

example (B : BidderProblem) [h : B.IsRegular] : Monotone B.winProb := h.winProb_mono
example (B : BidderProblem) [h : B.IsRegular] : Continuous B.cost := h.cost_continuous

/-! ## Part 4.7 — the two monotonicities -/

example (g : ℝ → ℝ) (hg : Monotone g) : MonotoneOn g (Set.Icc 0 1) := hg.monotoneOn _
example (g : ℝ → ℝ) (hg : Monotone g) (a b : ℝ) (hab : a ≤ b) : g a ≤ g b := hg hab

-- Meant to fail: `MonotoneOn` on `[0,1]` says nothing about `x = 7`
-- example (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Icc 0 1)) : Monotone g := hg

/-! ## Part 5 — watching a proof happen -/

example (B : BidderProblem) (v : ℝ) (hv : 0 ≤ v)
    (hcost : B.cost (B.strategy v) = 0) : 0 ≤ B.U v := by
  rw [BidderProblem.U_eq]
  rw [hcost, sub_zero]
  apply mul_nonneg hv
  exact (B.winProb_range _).1

-- The manual shows this shorter variant alongside the four-line proof above,
-- making the point that brevity hides the reasoning. The flexible-tactic
-- linter makes the same complaint, so it is silenced rather than obeyed here.
set_option linter.flexible false in
example (B : BidderProblem) (v : ℝ) (hv : 0 ≤ v)
    (hcost : B.cost (B.strategy v) = 0) : 0 ≤ B.U v := by
  simp [BidderProblem.U_eq, hcost]
  exact mul_nonneg hv (B.winProb_range _).1

/-! ## Part 6 — spring each trap deliberately -/

example : (2:ℕ) + 2 = 4 := rfl

-- Meant to fail: reals do not reduce, so `rfl` has nothing to unfold
-- example : (2:ℝ) + 2 = 4 := rfl

-- Meant to fail without `noncomputable`: real division has no executable form
-- def aHalf : ℝ := 1 / 2
noncomputable def aHalf : ℝ := 1 / 2

example (P : Prop) : P ↔ P := Iff.rfl
example (a : ℝ) : a = a := rfl

/-! ## Part 7 / Part 8 — letting the tools find things -/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := mul_nonneg ha hb

-- `exact?` in the manual; the suggestion it reports is spelled out here so the
-- file does not run a search on every build.
example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : x ≤ 1 := h.2

#check @add_comm
#check @mul_nonneg

/-! ## Part 8 — exercise solutions -/

noncomputable def clamped : BidderProblem where
  lowestType    := 0
  highestType   := 1
  winProb       := fun b => min 1 (max 0 b)
  winProb_range := by
    intro x
    rw [Set.mem_Icc]
    constructor
    · exact le_min zero_le_one (le_max_left 0 x)
    · exact min_le_left 1 _
  cost          := fun b => b / 2
  strategy      := id

example (B : BidderProblem) (v : ℝ) : B.q v ≤ 1 := (B.q_range v).2

end Manual
