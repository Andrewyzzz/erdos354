import Dyadic354.BG
import Mathlib.Algebra.Order.Archimedean.Basic

namespace Dyadic354.Normalization

open FloorSequence

theorem term_shift (γ : ℝ) (u n : ℕ) :
    term ((2 : ℝ) ^ u * γ) n = term γ (n + u) := by
  simp [term, floorMultiples, pow_add, mul_assoc]

theorem shifted_irrational (α β : ℝ) (h : Irrational (α / β)) (u v : ℕ) :
    Irrational (((2 : ℝ) ^ u * α) / ((2 : ℝ) ^ v * β)) := by
  have hh := (h.natCast_mul (show (2 : ℕ) ^ u ≠ 0 by positivity)).div_natCast
    (show (2 : ℕ) ^ v ≠ 0 by positivity)
  push_cast at hh
  convert hh using 1
  ring

theorem balance_larger (α β : ℝ) (hβ : 0 < β) (hba : β ≤ α)
    (hirr : Irrational (α / β)) :
    ∃ n : ℕ, (2 : ℝ) ^ n * β < α ∧ α < 2 * ((2 : ℝ) ^ n * β) := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((le_div_iff₀ hβ).mpr (by simpa using hba))
    (by norm_num : (1 : ℝ) < 2)
  have hne : α / β ≠ (2 : ℝ) ^ n := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hirr.ne_nat (2 ^ n)
  have hlo := (lt_div_iff₀ hβ).mp (lt_of_le_of_ne hn hne.symm)
  have hhi := (div_lt_iff₀ hβ).mp hn'
  rw [pow_succ] at hhi
  exact ⟨n, hlo, by nlinarith⟩

/-- Independent upward dyadic shifts put any positive irrational ratio
strictly between one and two; no downward scaling is used. -/
theorem balance (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hirr : Irrational (α / β)) :
    ∃ u v : ℕ, (2 : ℝ) ^ v * β < (2 : ℝ) ^ u * α ∧
      (2 : ℝ) ^ u * α < 2 * ((2 : ℝ) ^ v * β) := by
  by_cases hba : β ≤ α
  · obtain ⟨n, hn, hn'⟩ := balance_larger α β hβ hba hirr
    exact ⟨0, n, by simpa using hn, by simpa using hn'⟩
  · have hi : Irrational (β / α) := by simpa only [inv_div] using hirr.inv
    obtain ⟨n, hn, hn'⟩ := balance_larger β α hα (by linarith) hi
    refine ⟨n + 1, 0, ?_, ?_⟩ <;> simp only [pow_zero, one_mul, pow_succ] <;> nlinarith

/-- A common upward shift overcomes both bounded floor errors and any
prescribed deleted-value bound. -/
theorem common_shift (α β : ℝ) (hβ : 0 < β) (hba : β < α) (hab : α < 2 * β) (B : ℤ) :
    ∃ T : ℕ, B < term ((2 : ℝ) ^ T * β) 0 ∧ 0 < term ((2 : ℝ) ^ T * β) 0 ∧
      term ((2 : ℝ) ^ T * β) 0 < term ((2 : ℝ) ^ T * α) 0 ∧
      term ((2 : ℝ) ^ T * α) 0 < 2 * term ((2 : ℝ) ^ T * β) 0 := by
  let δ := min β (min (α - β) (2 * β - α))
  have hδ : 0 < δ := lt_min hβ (lt_min (by linarith) (by linarith))
  have hδb : δ ≤ β := min_le_left _ _
  have hδa : δ ≤ α - β := (min_le_left _ _).trans' (min_le_right _ _)
  have hδab : δ ≤ 2 * β - α := (min_le_right _ _).trans' (min_le_right _ _)
  obtain ⟨T, hT⟩ := pow_unbounded_of_one_lt ((|(B : ℝ)| + 3) / δ) (by norm_num : (1 : ℝ) < 2)
  have hp : (0 : ℝ) < 2 ^ T := by positivity
  have hbig := (div_lt_iff₀ hδ).mp hT
  have hb := mul_le_mul_of_nonneg_left hδb hp.le
  have ha := mul_le_mul_of_nonneg_left hδa hp.le
  have hab' := mul_le_mul_of_nonneg_left hδab hp.le
  have hflb := Int.floor_le ((2 : ℝ) ^ T * β)
  have hfub := Int.lt_floor_add_one ((2 : ℝ) ^ T * β)
  have hfla := Int.floor_le ((2 : ℝ) ^ T * α)
  have hfua := Int.lt_floor_add_one ((2 : ℝ) ^ T * α)
  refine ⟨T, ?_, ?_, ?_, ?_⟩ <;> simp only [term, floorMultiples, pow_zero, one_mul]
  · have hh : (B : ℝ) < (⌊(2 : ℝ) ^ T * β⌋ : ℝ) := by nlinarith [le_abs_self (B : ℝ)]
    exact_mod_cast hh
  · have hh : (0 : ℝ) < (⌊(2 : ℝ) ^ T * β⌋ : ℝ) := by nlinarith [abs_nonneg (B : ℝ)]
    exact_mod_cast hh
  · have hh : (⌊(2 : ℝ) ^ T * β⌋ : ℝ) < (⌊(2 : ℝ) ^ T * α⌋ : ℝ) := by nlinarith [abs_nonneg (B : ℝ)]
    exact_mod_cast hh
  · have hh : (⌊(2 : ℝ) ^ T * α⌋ : ℝ) < 2 * (⌊(2 : ℝ) ^ T * β⌋ : ℝ) := by nlinarith [abs_nonneg (B : ℝ)]
    exact_mod_cast hh

/-- Actual retained tails meet the normalized theorem and lie beyond B. -/
theorem above_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hirr : Irrational (α / β)) (B : ℤ) :
    ∃ u v : ℕ, B < term ((2 : ℝ) ^ v * β) 0 ∧ 0 < term ((2 : ℝ) ^ v * β) 0 ∧
      term ((2 : ℝ) ^ v * β) 0 < term ((2 : ℝ) ^ u * α) 0 ∧
      term ((2 : ℝ) ^ u * α) 0 < 2 * term ((2 : ℝ) ^ v * β) 0 := by
  obtain ⟨u, v, hba, hab⟩ := balance α β hα hβ hirr
  obtain ⟨T, hT⟩ := common_shift ((2 : ℝ) ^ u * α) ((2 : ℝ) ^ v * β) (by positivity) hba hab B
  refine ⟨T + u, T + v, ?_⟩
  simpa only [pow_add, mul_assoc] using hT

end Dyadic354.Normalization
