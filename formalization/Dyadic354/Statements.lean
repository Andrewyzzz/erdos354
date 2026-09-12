/-
Definitions adapted from The Formal Conjectures Authors, copyright 2025,
Apache-2.0. See UPSTREAM.md and LICENSE.upstream.
Reference commit a748dd915c908b21c4d864abf239f61049fa9d96.
Only definitions are reproduced; no upstream conjecture theorem is imported.
-/
import Dyadic354.Basic
import Mathlib.NumberTheory.Real.Irrational

namespace Dyadic354

noncomputable def floorMultiples (a γ : ℝ) (n : ℕ) : ℤ := ⌊γ ^ n * a⌋

noncomputable def interleave (a b γ : ℝ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then floorMultiples a γ (n / 2)
  else floorMultiples b γ (n / 2)

/-- The definition of IsAddCompleteNatSeq' at the pinned upstream revision. -/
def IndexedComplete (w : ℕ → ℤ) : Prop :=
  ∀ᶠ k in Filter.atTop, IsSubsetSum w k

/-- The right-hand side of the pinned upstream part (i), without answer wrappers. -/
def PartI : Prop :=
  ∀ α β : ℝ, 0 < α → 0 < β → Irrational (α / β) →
    IndexedComplete (interleave α β 2)

def SetComplete (A : Set ℤ) : Prop :=
  ∀ᶠ k in Filter.atTop, ∃ s : Finset ℤ, (s : Set ℤ) ⊆ A ∧ k = ∑ x ∈ s, x

def SetStronglyComplete (A : Set ℤ) : Prop :=
  ∀ B : Set ℤ, B.Finite → SetComplete (A \ B)

noncomputable def dyadicValueSet (α β : ℝ) : Set ℤ :=
  Set.range (interleave α β 2) \ {0}

/-- The manuscript's stronger set statement, with arbitrary finite value deletions. -/
def StrongCompleteness : Prop :=
  ∀ α β : ℝ, 0 < α → 0 < β → Irrational (α / β) →
    SetStronglyComplete (dyadicValueSet α β)

theorem indexedComplete_iff (w : ℕ → ℤ) :
    IndexedComplete w ↔ ∃ N : ℤ, ∀ k ≥ N, ∃ s : Finset ℕ, k = ∑ i ∈ s, w i := by
  exact Filter.eventually_atTop

end Dyadic354
