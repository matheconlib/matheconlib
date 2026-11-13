/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
import MathEconLib.ForMathlib.Data.List.BoundedChunks

/-!
# Bounded chunks

These clients import only the list module. They check concrete splits, the zero case
that differs from `List.toChunks`, and the general block lemmas.
-/

namespace MathEconLibTest.ListChunks

open MathEconLib.ListChunks

example : chunks 2 [1, 2, 3, 4, 5] = [[1, 2], [3, 4], [5]] := by decide

example : chunks 3 ([] : List Nat) = [] := by decide

-- Size zero discards every block, whereas `List.toChunks 0` keeps the input.
example : chunks 0 [1, 2, 3] = [] := chunks_zero _

example : [1, 2, 3].toChunks 0 = [[1, 2, 3]] := by decide

example {α : Type*} (D : Nat) (hD : 0 < D) (input : List α) :
    (chunks D input).flatten = input :=
  flatten_chunks D hD input

example {α : Type*} {D : Nat} {input block : List α} (h : block ∈ chunks D input) :
    block ≠ [] ∧ block.length ≤ D ∧ block.Sublist input :=
  ⟨nonempty_of_mem h, length_le_of_mem h, sublist_of_mem h⟩

example {α : Type*} (D : Nat) (input : List α) :
    (chunks D input).length * D ≤ input.length + D :=
  count_mul_le D input

end MathEconLibTest.ListChunks
