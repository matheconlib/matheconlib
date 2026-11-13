/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import Mathlib.Data.List.SplitLengths
public import Init.Data.List.Sublist
public import Mathlib.Tactic.Linarith

/-!
# Executable nonempty chunks of bounded length

`chunks D input` splits `input` into consecutive nonempty blocks of length at
most `D`, using `List.splitLengths`.

Batteries' `List.toChunks` computes the same blocks for `0 < D`, but its
accumulator-based implementation has no proved API in our dependency. Because
`chunks` is defined through `List.splitLengths`, it inherits Mathlib's lemmas
about that function directly: concatenation (`flatten_chunks`), the length
bound on each block (`length_le_of_mem`), and the block count (`count_le`).
We do not prove an equivalence bridge with `List.toChunks`.

The zero case differs: `chunks 0 input = []` (`chunks_zero`), whereas
`input.toChunks 0 = [input]` for nonempty `input`. Use `flatten_chunks` only
under `0 < D`.
-/

@[expose] public section

namespace MathEconLib.ListChunks

variable {α : Type*}

/-- Split into at most `length / D + 1` blocks, discarding empty blocks. -/
def chunks (D : Nat) (input : List α) : List (List α) :=
  ((List.replicate (input.length / D + 1) D).splitLengths input).filter
    (fun block => !block.isEmpty)

/-- With block size zero every block is empty and is discarded. -/
@[simp] theorem chunks_zero (input : List α) : chunks 0 input = [] := by
  simp [chunks]

theorem flatten_nonempty_filter (blocks : List (List α)) :
    (blocks.filter (fun block => !block.isEmpty)).flatten = blocks.flatten := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
      cases block <;> simp [ih]

theorem flatten_chunks (D : Nat) (hD : 0 < D) (input : List α) :
    (chunks D input).flatten = input := by
  unfold chunks
  rw [flatten_nonempty_filter]
  apply List.flatten_splitLengths
  have hcover : input.length ≤ (input.length / D + 1) * D := by
    have hmod := Nat.mod_lt input.length hD
    have hdecomp := Nat.mod_add_div input.length D
    nlinarith
  simpa using hcover

theorem nonempty_of_mem {D : Nat} {input : List α} {block : List α}
    (h : block ∈ chunks D input) : block ≠ [] := by
  have hn := (List.mem_filter.mp h).2
  intro he
  simp [he] at hn

theorem length_le_of_mem {D : Nat} {input : List α} {block : List α}
    (h : block ∈ chunks D input) : block.length ≤ D := by
  have hraw := (List.mem_filter.mp h).1
  exact List.length_mem_splitLengths input (List.replicate (input.length / D + 1) D) D
    (by intro k hk; simp only [List.mem_replicate] at hk; omega) block hraw

theorem splitLengths_sublist (sizes : List Nat) (input block : List α)
    (h : block ∈ sizes.splitLengths input) : block.Sublist input := by
  induction sizes generalizing input with
  | nil => simp at h
  | cons size sizes ih =>
      simp only [List.splitLengths_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.take_sublist _ _
      · exact (ih (input.drop size) h).trans (List.drop_sublist _ _)

theorem sublist_of_mem {D : Nat} {input : List α} {block : List α}
    (h : block ∈ chunks D input) : block.Sublist input :=
  splitLengths_sublist _ _ _ (List.mem_filter.mp h).1

theorem count_le (D : Nat) (input : List α) :
    (chunks D input).length ≤ input.length / D + 1 := by
  have h := List.length_filter_le (fun block : List α => !block.isEmpty)
    ((List.replicate (input.length / D + 1) D).splitLengths input)
  simpa only [chunks, List.length_splitLengths, List.length_replicate] using h

/-- A division-free bound convenient for summing over a family of rows. -/
theorem count_mul_le (D : Nat) (input : List α) :
    (chunks D input).length * D ≤ input.length + D := by
  calc
    (chunks D input).length * D ≤ (input.length / D + 1) * D :=
      Nat.mul_le_mul_right D (count_le D input)
    _ = input.length / D * D + D := by simp only [Nat.add_mul, Nat.one_mul]
    _ ≤ input.length + D := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

end MathEconLib.ListChunks
