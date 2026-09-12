import Dyadic354.BGSparseCompact
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Dyadic354.BGBinaryRatio

open BGSparseCompact

theorem normalize_power (h m j : ℕ) (hmj : m ≤ j) (hj : j < h) :
    (2 : ℝ) ^ (h - 1 - j) = (2 : ℝ) ^ (h - 1 - m) * (1 / 2 : ℝ) ^ (j - m) := by
  have he : (h - 1 - j) + (j - m) = h - 1 - m := by omega
  rw [one_div_pow, ← he, pow_add]
  field_simp

/-- A ratio of two legitimate binary polynomials with at most k joint
positions lies in the compact bounded-complexity ratio set. -/
theorem ratio_mem (S : Finset ℕ) (hS : S.Nonempty) (h k : ℕ)
    (hbound : ∀ j ∈ S, j < h) (hcard : S.card ≤ k)
    (a b : ℕ → ℝ) (ha : ∀ j ∈ S, a j = 0 ∨ a j = 1)
    (hb : ∀ j ∈ S, b j = 0 ∨ b j = 1)
    (hab : ∀ j ∈ S, a j = 1 ∨ b j = 1)
    (r : ℝ) (hr1 : 1 < r) (hr2 : r < 2)
    (he : (∑ j ∈ S, (2 : ℝ) ^ (h - 1 - j) * a j) =
      r * (∑ j ∈ S, (2 : ℝ) ^ (h - 1 - j) * b j)) : r ∈ ratios k := by
  classical
  let m := S.min' hS
  let A := ∑ j ∈ S, (1 / 2 : ℝ) ^ (j - m) * a j
  let B := ∑ j ∈ S, (1 / 2 : ℝ) ^ (j - m) * b j
  have ha0 (j : ℕ) (hj : j ∈ S) : 0 ≤ a j := by rcases ha j hj with h | h <;> simp [h]
  have hb0 (j : ℕ) (hj : j ∈ S) : 0 ≤ b j := by rcases hb j hj with h | h <;> simp [h]
  have hAmem : A ∈ sums k := by
    apply finset_sum_mem S _ k _ hcard
    intro j hj
    rcases ha j hj with hz | ho
    · simp [hz, atoms]
    · simp only [ho, mul_one]
      exact Set.mem_insert_of_mem _ ⟨j - m, rfl⟩
  have hBmem : B ∈ sums k := by
    apply finset_sum_mem S _ k _ hcard
    intro j hj
    rcases hb j hj with hz | ho
    · simp [hz, atoms]
    · simp only [ho, mul_one]
      exact Set.mem_insert_of_mem _ ⟨j - m, rfl⟩
  have hAp : (∑ j ∈ S, (2 : ℝ) ^ (h - 1 - j) * a j) = (2 : ℝ) ^ (h - 1 - m) * A := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [normalize_power h m j (S.min'_le j hj) (hbound j hj)]
    ring
  have hBp : (∑ j ∈ S, (2 : ℝ) ^ (h - 1 - j) * b j) = (2 : ℝ) ^ (h - 1 - m) * B := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [normalize_power h m j (S.min'_le j hj) (hbound j hj)]
    ring
  have hp : (0 : ℝ) < 2 ^ (h - 1 - m) := by positivity
  have hAB : A = r * B := by rw [hAp, hBp] at he; nlinarith
  have hma : a m ≤ A := by
    have h := Finset.single_le_sum (f := fun j => (1 / 2 : ℝ) ^ (j - m) * a j)
      (fun j hj => mul_nonneg (by positivity) (ha0 j hj)) (S.min'_mem hS)
    simpa [A, m] using h
  have hmb : b m ≤ B := by
    have h := Finset.single_le_sum (f := fun j => (1 / 2 : ℝ) ^ (j - m) * b j)
      (fun j hj => mul_nonneg (by positivity) (hb0 j hj)) (S.min'_mem hS)
    simpa [B, m] using h
  have hden : (1 / 2 : ℝ) ≤ B := by
    rcases hab m (S.min'_mem hS) with hm | hm
    · rw [hm] at hma
      nlinarith
    · rw [hm] at hmb
      linarith
  refine ⟨(A, B), ⟨⟨hAmem, hBmem⟩, hden⟩, ?_⟩
  dsimp
  exact (div_eq_iff (by linarith : B ≠ 0)).mpr hAB

end Dyadic354.BGBinaryRatio
