import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Dyadic354

/-- A representation chooses a finite set of original indices, once each. -/
def IsSubsetSum {ι : Type*} (w : ι → ℤ) (z : ℤ) : Prop :=
  ∃ s : Finset ι, z = ∑ i ∈ s, w i

abbrev OriginalIndex := ℕ × Bool

/-- Distinct sum values, rather than the number of masks. -/
def finiteSubsetSums {ι : Type*} [DecidableEq ι] (w : ι → ℤ) (s : Finset ι) : Finset ℤ :=
  s.powerset.image (fun t => ∑ i ∈ t, w i)

theorem mem_finiteSubsetSums {ι : Type*} [DecidableEq ι]
    (w : ι → ℤ) (s : Finset ι) (z : ℤ) :
    z ∈ finiteSubsetSums w s ↔ ∃ t ⊆ s, z = ∑ i ∈ t, w i := by
  simp only [finiteSubsetSums, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, ht, hz.symm⟩
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, ht, hz.symm⟩

/-- Homogeneous integer linear forms in the endpoint coordinates p and q. -/
structure Linear where
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr, Inhabited

namespace Linear

def eval (v : Linear) (p q : ℤ) : ℤ := v.a * p + v.b * q
def add (v w : Linear) : Linear := ⟨v.a + w.a, v.b + w.b⟩
def sub (v w : Linear) : Linear := ⟨v.a - w.a, v.b - w.b⟩
def Nonneg (v : Linear) : Prop := 0 ≤ 2 * v.a + v.b ∧ 0 ≤ v.a + v.b
def Positive (v : Linear) : Prop := Nonneg v ∧ (v.a ≠ 0 ∨ v.b ≠ 0)

instance (v : Linear) : Decidable (Nonneg v) := inferInstanceAs (Decidable (_ ∧ _))
instance (v : Linear) : Decidable (Positive v) := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem eval_add (v w : Linear) (p q : ℤ) :
    (v.add w).eval p q = v.eval p q + w.eval p q := by
  simp only [eval, add]
  ring

@[simp] theorem eval_sub (v w : Linear) (p q : ℤ) :
    (v.sub w).eval p q = v.eval p q - w.eval p q := by
  simp only [eval, sub]
  ring

theorem cone_identity (v : Linear) (p q : ℤ) :
    v.eval p q = (2 * v.a + v.b) * (p - q) + (v.a + v.b) * (2 * q - p) := by
  unfold eval
  ring

/-- Closed-cone nonnegativity; no sampling of p or q occurs. -/
theorem nonneg_on_cone (v : Linear) (h : v.Nonneg) (p q : ℤ)
    (hqp : q ≤ p) (hpq : p ≤ 2 * q) : 0 ≤ v.eval p q := by
  rw [cone_identity]
  exact add_nonneg (mul_nonneg h.1 (by omega)) (mul_nonneg h.2 (by omega))

/-- Strict positivity throughout the open cone. -/
theorem positive_on_cone (v : Linear) (h : v.Positive) (p q : ℤ)
    (hqp : q < p) (hpq : p < 2 * q) : 0 < v.eval p q := by
  rw [cone_identity]
  have hx : 0 < p - q := by omega
  have hy : 0 < 2 * q - p := by omega
  have hn := h.1
  change 0 ≤ 2 * v.a + v.b ∧ 0 ≤ v.a + v.b at hn
  have hz : 0 < 2 * v.a + v.b ∨ 0 < v.a + v.b := by
    rcases h.2 with h | h <;> omega
  rcases hz with hz | hz
  · exact add_pos_of_pos_of_nonneg (mul_pos hz hx) (mul_nonneg hn.2 (le_of_lt hy))
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hn.1 (le_of_lt hx)) (mul_pos hz hy)

end Linear
end Dyadic354
