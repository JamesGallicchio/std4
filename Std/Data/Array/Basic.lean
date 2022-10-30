/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Floris van Doorn
-/
import Std.Data.Array.Init.Basic
import Std.Classes.Collections.Iterable

/-!
## Definitions on Arrays

This file contains various definitions on `Array`. It does not contain
proofs about these definitions, those are contained in other files in `Std.Data.Array`.
-/

namespace Array

/-- The array `#[0, 1, ..., n - 1]`. -/
def range (n : Nat) : Array Nat :=
  n.fold (flip Array.push) #[]

/-- Drop `none`s from a Array, and replace each remaining `some a` with `a`. -/
def reduceOption (l : Array (Option α)) : Array α :=
  l.filterMap id

/-- Turns `#[#[a₁, a₂, ⋯], #[b₁, b₂, ⋯], ⋯]` into `#[a₁, a₂, ⋯, b₁, b₂, ⋯]` -/
def flatten (arr : Array (Array α)) : Array α :=
  arr.foldl (init := #[]) fun acc a => acc.append a

instance : Std.WFIterable (Array α) α where
  ρ := Array α × Nat
  toIterator A := (A, 0)
  step  := fun (A, i) => if h : i < A.size then some (A[i], (A, i+1)) else none
  wf    := invImage (α := Array α × Nat) (fun (A, i) => A.size - i) (Nat.lt_wfRel)
  dom   := (fun _ => True)
  h_toIterator _ := by simp
  h_step := by
    intro r1
    match r1 with
    | (A, i) =>
    intro _
    intro x r2
    match r2 with
    | (A', i') =>
    intro ih
    simp [WellFoundedRelation.rel, InvImage, Nat.lt_wfRel]
    simp [Std.Iterable.step] at ih
    split at ih <;> simp at ih
    have ⟨a,b,c⟩ := ih
    subst_vars
    apply Nat.sub_succ_lt_self
    assumption
