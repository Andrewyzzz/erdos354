import Dyadic354.FloorDescent

namespace Dyadic354.BlockLength

open FloorSequence FloorDescent

theorem threshold_le_square (p q : ℤ) (hqp : q < p) (hpq : p < 2 * q) :
    InitialMesh.threshold p q ≤ 16 * p ^ 2 := by
  have hp : 3 ≤ p := by omega
  have hm := mul_le_mul_of_nonneg_left (show q ≤ p - 1 by omega) (show 0 ≤ p by omega)
  have hs := mul_nonneg (show 0 ≤ p - 3 by omega) (show 0 ≤ p by omega)
  unfold InitialMesh.threshold
  nlinarith

theorem floor_upper (α : ℝ) (n : ℕ) :
    term α n < (term α 0 + 1) * (2 : ℤ) ^ n := by
  have h0 : α < (term α 0 : ℝ) + 1 := by
    simp [floorMultiples]
  have hn : (term α n : ℝ) ≤ (2 : ℝ) ^ n * α := Int.floor_le _
  have hm := mul_lt_mul_of_pos_left h0 (pow_pos (show (0 : ℝ) < 2 by norm_num) n)
  have hr : (term α n : ℝ) < (((term α 0 + 1) * (2 : ℤ) ^ n : ℤ) : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hr

theorem coordinate_upper (α β : ℝ) (n : ℕ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0) :
    0 < pCoord α β n ∧ pCoord α β n ≤ term α n ∧
      pCoord α β n < (term α 0 + 1) * (2 : ℤ) ^ n := by
  have hn := normalized_bounds α β hb0 hba0 hab0 n
  obtain ⟨hq, hqp, _, _, ha, _⟩ := gcd_coordinates α β n hn.1 hn.2.1 hn.2.2
  have hp : 0 < pCoord α β n := lt_trans hq hqp
  have hd : (1 : ℤ) ≤ modulus α β n := by
    have h := modulus_positive α β n hn.1
    omega
  have hle : pCoord α β n ≤ term α n := by nlinarith
  exact ⟨hp, hle, lt_of_le_of_lt hle (floor_upper α n)⟩

/-- An explicit, intentionally non-optimal constant depending only on the
initial first floor. No future digit, event time, or modulus enters it. -/
noncomputable def growthConstant (α : ℝ) : ℕ := (16 * (term α 0 + 1) ^ 2).toNat

theorem growthConstant_bound (α : ℝ) :
    16 * (term α 0 + 1) ^ 2 ≤ (2 : ℤ) ^ growthConstant α := by
  have hz : 0 ≤ 16 * (term α 0 + 1) ^ 2 := by positivity
  have hN : (16 * (term α 0 + 1) ^ 2).toNat <
      2 ^ (16 * (term α 0 + 1) ^ 2).toNat := Nat.lt_two_pow_self
  have hZ : ((16 * (term α 0 + 1) ^ 2).toNat : ℤ) <
      (2 : ℤ) ^ (16 * (term α 0 + 1) ^ 2).toNat := by exact_mod_cast hN
  rw [Int.toNat_of_nonneg hz] at hZ
  exact le_of_lt hZ

theorem threshold_of_length (α β : ℝ) (n ℓ : ℕ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hℓ : 2 * n + growthConstant α ≤ ℓ) :
    InitialMesh.threshold (pCoord α β n) (qCoord α β n) ≤ (2 : ℤ) ^ ℓ := by
  have hn := normalized_bounds α β hb0 hba0 hab0 n
  obtain ⟨_, hqp, hpq, _, _, _⟩ := gcd_coordinates α β n hn.1 hn.2.1 hn.2.2
  have hp := coordinate_upper α β n hb0 hba0 hab0
  have hA : 0 ≤ (term α 0 + 1) * (2 : ℤ) ^ n :=
    mul_nonneg (by omega) (by positivity)
  have hs : (pCoord α β n) ^ 2 ≤ ((term α 0 + 1) * (2 : ℤ) ^ n) ^ 2 := by nlinarith
  have hexp : ((2 : ℤ) ^ n) ^ 2 = (2 : ℤ) ^ (2 * n) := by
    rw [← pow_mul, Nat.mul_comm]
  calc
    InitialMesh.threshold (pCoord α β n) (qCoord α β n) ≤ 16 * (pCoord α β n) ^ 2 :=
      threshold_le_square _ _ hqp hpq
    _ ≤ 16 * (term α 0 + 1) ^ 2 * ((2 : ℤ) ^ n) ^ 2 := by nlinarith [hs]
    _ = 16 * (term α 0 + 1) ^ 2 * (2 : ℤ) ^ (2 * n) := by rw [hexp]
    _ ≤ (2 : ℤ) ^ growthConstant α * (2 : ℤ) ^ (2 * n) :=
      mul_le_mul_of_nonneg_right (growthConstant_bound α) (by positivity)
    _ = (2 : ℤ) ^ (2 * n + growthConstant α) := by rw [← pow_add, Nat.add_comm]
    _ ≤ (2 : ℤ) ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ

/-- The manuscript's length criterion yields actual permanent gap descent.
This theorem does not assert the existence of such event gaps. -/
theorem next_event_length_descent (α β : ℝ) (n m : ℕ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hnm : n < m) (hno : ∀ t, n < t → t < m → ¬ ExactBlock.IsEvent α β t)
    (hm : ExactBlock.IsEvent α β m) (hlen : 2 * n + growthConstant α ≤ m - n) :
    ∀ t, m + 3 ≤ t →
      gapAt α β t (normalized_bounds α β hb0 hba0 hab0 t).1 ≤
        gapAt α β n (normalized_bounds α β hb0 hba0 hab0 n).1 - 1 := by
  exact next_event_descent α β n m hb0 hba0 hab0 hnm hno hm
    (threshold_of_length α β n (m - n) hb0 hba0 hab0 hlen)

end Dyadic354.BlockLength
