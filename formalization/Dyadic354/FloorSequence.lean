import Dyadic354.Statements
import Dyadic354.Certificate
import Mathlib.Algebra.Order.Floor.Ring

namespace Dyadic354.FloorSequence

noncomputable abbrev term (α : ℝ) (n : ℕ) : ℤ := floorMultiples α 2 n

noncomputable def correction (α : ℝ) (n : ℕ) : ℤ := term α (n + 1) - 2 * term α n

/-- The actual floor error is a binary digit, for every real parameter. -/
theorem correction_bounds (α : ℝ) (n : ℕ) :
    0 ≤ correction α n ∧ correction α n ≤ 1 := by
  have h0 := Int.floor_le ((2 : ℝ) ^ n * α)
  have h1 := Int.lt_floor_add_one ((2 : ℝ) ^ n * α)
  have h2 := Int.floor_le ((2 : ℝ) ^ (n + 1) * α)
  have h3 := Int.lt_floor_add_one ((2 : ℝ) ^ (n + 1) * α)
  have hpow : (2 : ℝ) ^ (n + 1) * α = 2 * ((2 : ℝ) ^ n * α) := by
    rw [pow_succ]
    ring
  have hlo : (2 : ℤ) * ⌊(2 : ℝ) ^ n * α⌋ ≤ ⌊(2 : ℝ) ^ (n + 1) * α⌋ := by
    have hr : (2 : ℝ) * (⌊(2 : ℝ) ^ n * α⌋ : ℝ) <
        (⌊(2 : ℝ) ^ (n + 1) * α⌋ : ℝ) + 1 := by nlinarith
    have hz : (2 : ℤ) * ⌊(2 : ℝ) ^ n * α⌋ < ⌊(2 : ℝ) ^ (n + 1) * α⌋ + 1 := by
      exact_mod_cast hr
    omega
  have hhi : ⌊(2 : ℝ) ^ (n + 1) * α⌋ < (2 : ℤ) * ⌊(2 : ℝ) ^ n * α⌋ + 2 := by
    have hr : (⌊(2 : ℝ) ^ (n + 1) * α⌋ : ℝ) <
        (2 : ℝ) * (⌊(2 : ℝ) ^ n * α⌋ : ℝ) + 2 := by nlinarith
    exact_mod_cast hr
  change 0 ≤ ⌊(2 : ℝ) ^ (n + 1) * α⌋ - 2 * ⌊(2 : ℝ) ^ n * α⌋ ∧
    ⌊(2 : ℝ) ^ (n + 1) * α⌋ - 2 * ⌊(2 : ℝ) ^ n * α⌋ ≤ 1
  omega

noncomputable def bit (α : ℝ) (n : ℕ) : Bool := decide (correction α n = 1)

theorem digit_bit (α : ℝ) (n : ℕ) : Certificate.digit (bit α n) = correction α n := by
  have hb := correction_bounds α n
  by_cases h : correction α n = 1
  · simp [bit, Certificate.digit, h]
  · have hz : correction α n = 0 := by omega
    simp [bit, Certificate.digit, hz]

theorem recurrence (α : ℝ) (n : ℕ) :
    term α (n + 1) = 2 * term α n + Certificate.digit (bit α n) := by
  rw [digit_bit]
  unfold correction
  ring

theorem next_bounds (α : ℝ) (n : ℕ) :
    2 * term α n ≤ term α (n + 1) ∧ term α (n + 1) ≤ 2 * term α n + 1 := by
  have h := correction_bounds α n
  unfold correction at h
  omega

/-- Once normalized floor endpoints are separated, the strict ordering persists. -/
theorem normalized_bounds (α β : ℝ)
    (hb : 0 < term β 0) (hba : term β 0 < term α 0) (hab : term α 0 < 2 * term β 0) :
    ∀ n, 0 < term β n ∧ term β n < term α n ∧ term α n < 2 * term β n := by
  intro n
  induction n with
  | zero => exact ⟨hb, hba, hab⟩
  | succ n ih =>
      have ha := next_bounds α n
      have hb := next_bounds β n
      omega

theorem prefix_deficit (α : ℝ) (n : ℕ) :
    term α n - ∑ i ∈ Finset.range n, term α i =
      term α 0 + ∑ i ∈ Finset.range n, correction α i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      unfold correction
      unfold correction at ih
      linarith

theorem prefix_sum_lt (α : ℝ) (hα : 0 < term α 0) (n : ℕ) :
    (∑ i ∈ Finset.range n, term α i) < term α n := by
  have hd := prefix_deficit α n
  have hc : 0 ≤ ∑ i ∈ Finset.range n, correction α i :=
    Finset.sum_nonneg (fun i _ => (correction_bounds α i).1)
  omega

theorem interleave_even (α β γ : ℝ) (n : ℕ) :
    interleave α β γ (2 * n) = floorMultiples α γ n := by
  simp [interleave]

theorem interleave_odd (α β γ : ℝ) (n : ℕ) :
    interleave α β γ (2 * n + 1) = floorMultiples β γ n := by
  simp [interleave, Nat.add_div]

theorem paired_prefix_sum (α β γ : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (2 * n), interleave α β γ i) =
      ∑ i ∈ Finset.range n, (floorMultiples α γ i + floorMultiples β γ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, interleave_even, interleave_odd]
      ring

theorem paired_prefix_lt (α β : ℝ) (hα : 0 < term α 0) (hβ : 0 < term β 0) (n : ℕ) :
    (∑ i ∈ Finset.range (2 * n), interleave α β 2 i) < term α n + term β n := by
  rw [paired_prefix_sum, Finset.sum_add_distrib]
  exact add_lt_add (prefix_sum_lt α hα n) (prefix_sum_lt β hβ n)

end Dyadic354.FloorSequence
