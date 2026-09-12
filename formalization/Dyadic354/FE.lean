import Dyadic354.FERecurrence
import Dyadic354.EventDecay

namespace Dyadic354.FE

open FloorSequence FECounting FERecurrence

noncomputable def decayRate (β : ℝ) : ℝ := 1 / (64 * (term β 0 : ℝ))
noncomputable def constant (α β : ℝ) : ℝ := 2 * ((term α 0 : ℝ) + (term β 0 : ℝ) + 10)

theorem potential_zero (α β : ℝ) :
    potential α β 0 = (term α 0 : ℝ) + (term β 0 : ℝ) + 8 := by
  simp [potential, normalized, deficit_zero]
  ring

theorem normalized_power_bound (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : normalized α β n ≤
      2 * potential α β 0 * (sigma β) ^ eventCount α β n := by
  have hs := sigma_bounds β (initial_second_ge_two α β hba0 hab0)
  have h := EventDecay.block_bound (normalized α β) (potential α β) (eventCount α β)
    (fun i => digitSum α β i ≠ 0) (sigma β) hs.1 hs.2.1
    (potential_nonneg α β hb0 hba0 hab0) (normalized_le_potential α β)
    (normalized_step_le_potential α β hb0 hba0 hab0)
    (fun i => by
      rw [eventCount_step]
      by_cases he : digitSum α β i = 0 <;> simp [he])
    (fun i he => potential_zero_step α β hb0 hba0 hab0 i (by simpa using he))
    (fun i he => potential_two_step α β hb0 hba0 hab0 i ((digitSum_event_iff α β i).mp he)) 0 n
  simpa [eventCount, Finset.sum_range_zero] using h

theorem rate_positive (β : ℝ) (hb0 : 0 < term β 0) : 0 < decayRate β := by
  have : (0 : ℝ) < term β 0 := by exact_mod_cast hb0
  unfold decayRate
  positivity

theorem constant_positive (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) : 0 < constant α β := by
  have hN : (0 : ℝ) < term β 0 := by exact_mod_cast hb0
  have hM : (term β 0 : ℝ) < term α 0 := by exact_mod_cast hba0
  unfold constant
  linarith

/-- Manuscript FE, with the stated constants, for all actual finite prefixes.
All local boundary and recurrence obligations are proved dependencies. -/
theorem deficit_exponential_bound (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : (deficit α β n : ℝ) ≤ constant α β * (2 : ℝ) ^ n *
      Real.exp (-decayRate β * eventCount α β n) := by
  have h := normalized_power_bound α β hb0 hba0 hab0 n
  have hv := potential_nonneg α β hb0 hba0 hab0 0
  have hs := sigma_bounds β (initial_second_ge_two α β hba0 hab0)
  have he : (sigma β) ^ eventCount α β n ≤ Real.exp (-decayRate β * eventCount α β n) := by
    exact EventDecay.power_le_exp (decayRate β) (by change 0 ≤ sigma β; linarith [hs.1]) _
  have hc : 2 * potential α β 0 ≤ constant α β := by
    rw [potential_zero]
    unfold constant
    linarith
  have hnorm : normalized α β n ≤ constant α β * Real.exp (-decayRate β * eventCount α β n) :=
    h.trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans
      (mul_le_mul_of_nonneg_right hc (le_of_lt (Real.exp_pos _))))
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hout := (div_le_iff₀ hp).mp hnorm
  nlinarith

end Dyadic354.FE
