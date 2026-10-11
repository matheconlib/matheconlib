import MathEconLib.Mechanism

/-!
# First-and-second-pay interface and boundary checks

These clients import the mechanism umbrella. They exercise the specification, revenue theorem,
economic counterexamples, and the distinction between a top tie and a tie for second place.
-/

open MathEconLib MathEconLib.Mechanism MathEconLib.Mechanism.Auctions
open MathEconLib.Mechanism.Auctions.FirstAndSecondPay

namespace MathEconLib.Tests.FirstAndSecondPay

example : IsFirstAndSecondPay (firstAndSecondPay 3) := firstAndSecondPay_spec

example {n : ℕ} [Nontrivial (Fin n)] {b : Fin n → ℝ} (hb : NoTies b) :
    (firstAndSecondPay n).revenue b = b hb.winner + b hb.runnerUp := by
  rw [Mechanism.revenue_eq_sum_payment]
  exact hb.sum_payment_eq (firstAndSecondPay n) firstAndSecondPay_spec

example : ¬DirectMechanism.IsDSIC (privateValues 2) (firstAndSecondPay 2) :=
  not_isDSIC _ firstAndSecondPay_spec

example : ¬DirectMechanism.IsExPostIR (privateValues 2) (firstAndSecondPay 2) :=
  not_isExPostIR _ firstAndSecondPay_spec

-- Lower ties do not prevent allocation to a unique highest bidder.
example : IsWinner (![5, 3, 3] : Fin 3 → ℝ) 0 := by
  norm_num [IsWinner, Fin.forall_fin_succ]

example : (firstAndSecondPay 3).outcome ![5, 3, 3] 0 = 1 := by
  apply allocation_eq_one_of_isWinner _ firstAndSecondPay_spec.allocation
  norm_num [IsWinner, Fin.forall_fin_succ]

-- Both bidders tied for second are charged, so top-two revenue requires the no-ties guard.
example : (firstAndSecondPay 3).payment 1 ![5, 3, 3] = 3 ∧
    (firstAndSecondPay 3).payment 2 ![5, 3, 3] = 3 := by
  constructor
  · exact payment_of_isRunnerUp _ firstAndSecondPay_spec
      (by norm_num [IsRunnerUp, Fin.forall_fin_succ, Fin.exists_fin_succ, Matrix.cons_val_two])
  · exact payment_of_isRunnerUp _ firstAndSecondPay_spec
      (by norm_num [IsRunnerUp, Fin.forall_fin_succ, Fin.exists_fin_succ, Matrix.cons_val_two])

-- At a top tie, no bidder wins or pays under this particular total rule.
example (i : Fin 3) : (firstAndSecondPay 3).outcome ![5, 5, 3] i = 0 ∧
    (firstAndSecondPay 3).payment i ![5, 5, 3] = 0 := by
  fin_cases i <;>
    norm_num [firstAndSecondPay, Mechanism.payment, IsWinner, IsRunnerUp,
      Set.indicator_apply, Fin.forall_fin_succ, Fin.exists_fin_succ, Matrix.cons_val_two]

-- With a single bidder, that bidder wins and pays their bid; no runner-up is asserted.
example : (firstAndSecondPay 1).outcome ![2] 0 = 1 ∧
    (firstAndSecondPay 1).payment 0 ![2] = 2 := by
  norm_num [firstAndSecondPay, Mechanism.payment, IsWinner, IsRunnerUp,
    Set.indicator_apply, Fin.forall_fin_succ, Fin.exists_fin_succ, Matrix.cons_val_two]

#print axioms firstAndSecondPay_spec
#print axioms sum_allocation_le_one
#print axioms NoTies.sum_payment_eq
#print axioms not_isDSIC
#print axioms not_isExPostIR

end MathEconLib.Tests.FirstAndSecondPay
