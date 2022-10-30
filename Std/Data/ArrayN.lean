/-
Copyright (c) 2022 James Gallicchio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Gallicchio
-/
import Std.Classes.Collections.Iterable

namespace Std

/-- Fixed-length arrays. -/
structure ArrayN (α n) where
  /-- Underlying data (just a variable-length array). -/
  data : Array α
  /-- The size invariant. -/
  h_size : data.size = n

namespace ArrayN

/-- Get the `i`th element of `A`. -/
def get (i : Fin n) (A : ArrayN α n) : α := A.data.get (A.h_size.symm ▸ i)

/-- Set the `i`th element of `A`. -/
def set (i : Fin n) (x : α) (A : ArrayN α n) : ArrayN α n :=
  ⟨A.data.set (A.h_size.symm ▸ i) x, by simp [A.h_size]⟩

/-- The range of indices for the given array. -/
def indices (_ : ArrayN α n) : Range := [0:n]

instance : Std.WFIterable (ArrayN α n) α where
  ρ := Array α × Nat
  toIterator A := (A.data, 0)
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
