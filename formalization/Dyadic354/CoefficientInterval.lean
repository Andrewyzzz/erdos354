import Dyadic354.Basic
import Mathlib.RingTheory.Coprime.Basic

/-!
The bounded two-generator interval in §3.1 of the manuscript. All parameters
are integers; coprimality is the ordinary Bézout property, not an oracle for
the representation claimed below.
-/

namespace Dyadic354.CoefficientInterval

theorem lower_interval (p q K z : ℤ) (hq : 0 < q) (hqp : q < p)
    (hK : p ≤ K) (hcop : IsCoprime p q)
    (hzlo : q * (p - 1) ≤ z) (hzhi : z ≤ p * (K - 1)) :
    ∃ x y : ℤ, 0 ≤ x ∧ x < K ∧ 0 ≤ y ∧ y < K ∧ p * x + q * y = z := by
  obtain ⟨a, b, hab⟩ := hcop
  let y := (b * z) % p
  let x := a * z + q * ((b * z) / p)
  have hp : 0 < p := lt_trans hq hqp
  have hy0 : 0 ≤ y := Int.emod_nonneg _ (ne_of_gt hp)
  have hyp : y < p := Int.emod_lt_of_pos _ hp
  have heq : p * x + q * y = z := by
    have hr := Int.mul_ediv_add_emod (b * z) p
    dsimp [x, y]
    calc
      p * (a * z + q * (b * z / p)) + q * (b * z % p) =
          a * p * z + q * (p * (b * z / p) + b * z % p) := by ring
      _ = (a * p + b * q) * z := by rw [hr]; ring
      _ = z := by rw [hab, one_mul]
  have hx0 : 0 ≤ x := by
    have : q * y ≤ q * (p - 1) := mul_le_mul_of_nonneg_left (by omega) (le_of_lt hq)
    nlinarith
  have hxK : x < K := by
    have : 0 ≤ q * y := mul_nonneg (le_of_lt hq) hy0
    nlinarith
  exact ⟨x, y, hx0, hxK, hy0, lt_of_lt_of_le hyp hK, heq⟩

/-- Every integer in the full, reflected coefficient interval is attained. -/
theorem bounded_interval (p q K z : ℤ) (hq : 0 < q) (hqp : q < p)
    (hK : p ≤ K) (hcop : IsCoprime p q)
    (hzlo : q * (p - 1) ≤ z)
    (hzhi : z ≤ (p + q) * (K - 1) - q * (p - 1)) :
    ∃ x y : ℤ, 0 ≤ x ∧ x < K ∧ 0 ≤ y ∧ y < K ∧ p * x + q * y = z := by
  by_cases hlow : z ≤ p * (K - 1)
  · exact lower_interval p q K z hq hqp hK hcop hzlo hlow
  · have hK0 : 0 ≤ K - 1 := by omega
    have hcompare : q * (K - 1) ≤ p * (K - 1) :=
      mul_le_mul_of_nonneg_right (le_of_lt hqp) hK0
    obtain ⟨x, y, hx0, hxK, hy0, hyK, heq⟩ :=
      lower_interval p q K ((p + q) * (K - 1) - z) hq hqp hK hcop
        (by omega) (by nlinarith)
    refine ⟨K - 1 - x, K - 1 - y, by omega, by omega, by omega, by omega, ?_⟩
    nlinarith

/-- Binary digits use distinct positions, as expressed by a finite index set. -/
theorem binary_sum_exists (ℓ x : ℕ) (hx : x < 2 ^ ℓ) :
    ∃ s : Finset ℕ, s ⊆ Finset.range ℓ ∧ x = ∑ i ∈ s, 2 ^ i := by
  induction ℓ generalizing x with
  | zero =>
      have : x = 0 := by simpa using hx
      exact ⟨∅, Finset.empty_subset _, by simp [this]⟩
  | succ ℓ ih =>
      by_cases hsmall : x < 2 ^ ℓ
      · obtain ⟨s, hs, heq⟩ := ih x hsmall
        exact ⟨s, hs.trans (Finset.range_mono (Nat.le_succ ℓ)), heq⟩
      · have hrem : x - 2 ^ ℓ < 2 ^ ℓ := by
          rw [pow_succ] at hx
          omega
        obtain ⟨s, hs, heq⟩ := ih (x - 2 ^ ℓ) hrem
        have hn : ℓ ∉ s := fun h => (Finset.mem_range.mp (hs h)).false
        refine ⟨insert ℓ s, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
          · exact Finset.range_mono (Nat.le_succ ℓ) (hs hi)
        · rw [Finset.sum_insert hn, ← heq]
          omega

end Dyadic354.CoefficientInterval
