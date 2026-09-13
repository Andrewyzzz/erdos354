/-
Copyright 2025 The Formal Conjectures Authors.
Licensed under Apache-2.0; see LICENSE.upstream.

Exact definition blocks from google-deepmind/formal-conjectures at
a748dd915c908b21c4d864abf239f61049fa9d96. Only imports and section/namespace
scaffolding are adapted for the pinned local Lean 4.27.0 environment.
scripts/check_upstream.py checks these blocks against the frozen source snapshots.
No upstream theorem or answer wrapper is imported.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Floor.Ring

section

variable {M : Type*} [AddCommMonoid M]

def subsetSums (A : Set M) : Set M :=
  {n | ∃ B : Finset M, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

def subseqSums' (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

variable [Preorder M]

def IsAddComplete (A : Set M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subsetSums A

def IsAddStronglyComplete (A : Set M) : Prop :=
  ∀ ⦃B : Set M⦄, B.Finite → IsAddComplete (A \ B)

def IsAddCompleteNatSeq' (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A

end

namespace Erdos354

noncomputable def FloorMultiples (a γ : ℝ) (n : ℕ) : ℤ := ⌊γ ^ n * a⌋

noncomputable def FloorMultiples.interleave (a b γ : ℝ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then
    FloorMultiples a γ (n / 2)
  else
    FloorMultiples b γ (n / 2)

end Erdos354
