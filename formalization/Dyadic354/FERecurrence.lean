import Dyadic354.EventBoundary
import Dyadic354.FEMissingRuns
import Dyadic354.EventInfinitude
import Mathlib.Tactic.FieldSimp

namespace Dyadic354.FERecurrence

open FloorSequence FECounting

open scoped Classical

noncomputable def eventCount (α β : ℝ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if digitSum α β i = 0 then 0 else 1

theorem eventCount_card (α β : ℝ) (n : ℕ) :
    eventCount α β n = ((Finset.range n).filter (fun i => ExactBlock.IsEvent α β (i + 1))).card := by
  rw [Finset.card_filter]
  unfold eventCount
  apply Finset.sum_congr rfl
  intro i _
  rw [← digitSum_event_iff]
  by_cases h : digitSum α β i = 0 <;> simp [h]

theorem eventCount_step (α β : ℝ) (n : ℕ) :
    eventCount α β (n + 1) = eventCount α β n + if digitSum α β n = 0 then 0 else 1 := by
  exact Finset.sum_range_succ _ n

theorem eventCount_step_bounds (α β : ℝ) (n : ℕ) :
    eventCount α β n ≤ eventCount α β (n + 1) ∧ eventCount α β (n + 1) ≤ eventCount α β n + 1 := by
  rw [eventCount_step]
  split_ifs <;> omega

theorem eventCount_mono (α β : ℝ) : Monotone (eventCount α β) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (eventCount_step_bounds α β n).1

theorem eventCount_le (α β : ℝ) (n : ℕ) : eventCount α β n ≤ n := by
  induction n with
  | zero => simp [eventCount]
  | succ n ih => have h := eventCount_step_bounds α β n; omega

theorem eventCount_unbounded (α β : ℝ) (hi : Irrational (α / β)) :
    ∀ k, ∃ n, k ≤ eventCount α β n := by
  intro k
  induction k with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨t, ht, he⟩ := EventInfinitude.events_unbounded α β hi n
      have hh := eventCount_mono α β (show n ≤ t - 1 by omega)
      have he' : ExactBlock.IsEvent α β ((t - 1) + 1) := by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using he
      have hw := (digitSum_event_iff α β (t - 1)).mpr he'
      have hstep := eventCount_step α β (t - 1)
      rw [if_neg hw, Nat.sub_add_cancel (by omega : 1 ≤ t)] at hstep
      exact ⟨t, by omega⟩

theorem initial_second_ge_two (α β : ℝ)
    (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0) : 2 ≤ term β 0 := by omega

/-- The exact integer-scaled two-step estimate, with every boundary estimate
discharged for the actual sequence. -/
theorem two_step_scaled (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) (he : ExactBlock.IsEvent α β (n + 1)) :
    8 * term β 0 * deficit α β (n + 2) ≤
      (32 * term β 0 - 1) * deficit α β n + padding α β n + 52 * term β 0 := by
  have hb := FEMissingRuns.actual_holes_boundary_bound α β hb0 hba0 hab0 n
  have hj := EventBoundary.actual_nonzero_boundary α β hb0 hba0 hab0 n he
  have hg := growth_nonneg α β hb0 hba0 hab0 n
  have hg' := growth_nonneg α β hb0 hba0 hab0 (n + 1)
  have hw := digitSum_bounds α β n
  have hw' := digitSum_bounds α β (n + 1)
  have h0 := deficit_step α β n
  have h1 := deficit_step α β (n + 1)
  have hcost : deficit α β n - padding α β n - 4 * term β 0 ≤
      8 * term β 0 * (growth α β n + growth α β (n + 1)) := by
    nlinarith
  have hq : deficit α β (n + 2) ≤ 4 * deficit α β n + 6 - (growth α β n + growth α β (n + 1)) := by
    change deficit α β (n + 2) = _ at h1
    omega
  nlinarith

noncomputable def rho (β : ℝ) : ℝ := 1 - 1 / (32 * (term β 0 : ℝ))
noncomputable def sigma (β : ℝ) : ℝ := 1 - 1 / (64 * (term β 0 : ℝ))
noncomputable def normalized (α β : ℝ) (n : ℕ) : ℝ := (deficit α β n : ℝ) / (2 : ℝ) ^ n

/-- An explicit decaying correction absorbs all two-step errors. This
potential will replace the manuscript's summation of accumulated errors. -/
noncomputable def potential (α β : ℝ) (n : ℕ) : ℝ :=
  normalized α β n + 9 * ((n : ℝ) + 1) / (2 : ℝ) ^ n

theorem normalized_nonneg (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : 0 ≤ normalized α β n := by
  apply div_nonneg
  · exact_mod_cast deficit_nonneg α β hb0 hba0 hab0 n
  · positivity

theorem normalized_zero_step (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) (hw : digitSum α β n = 0) : normalized α β (n + 1) ≤ normalized α β n := by
  have h := deficit_step α β n
  have hg := growth_nonneg α β hb0 hba0 hab0 n
  rw [hw] at h
  have hr : (deficit α β (n + 1) : ℝ) ≤ 2 * (deficit α β n : ℝ) := by exact_mod_cast (show deficit α β (n + 1) ≤ 2 * deficit α β n by omega)
  unfold normalized
  rw [pow_succ]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * 2)).mpr
  have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  nlinarith

theorem rho_bounds (β : ℝ) (hN : 2 ≤ term β 0) :
    (63 : ℝ) / 64 ≤ rho β ∧ rho β ≤ 1 := by
  have h : (2 : ℝ) ≤ term β 0 := by exact_mod_cast hN
  unfold rho
  constructor
  · have hdiv : 1 / (32 * (term β 0 : ℝ)) ≤ (1 : ℝ) / 64 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      nlinarith
    linarith
  · have : 0 ≤ 1 / (32 * (term β 0 : ℝ)) := by positivity
    linarith

theorem sigma_bounds (β : ℝ) (hN : 2 ≤ term β 0) :
    (1 : ℝ) / 2 ≤ sigma β ∧ sigma β ≤ 1 ∧ rho β ≤ (sigma β) ^ 2 := by
  have h : (2 : ℝ) ≤ term β 0 := by exact_mod_cast hN
  have he : 0 ≤ 1 / (64 * (term β 0 : ℝ)) := by positivity
  have he' : 1 / (64 * (term β 0 : ℝ)) ≤ (1 : ℝ) / 2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  have hr : rho β = 1 - 2 * (1 / (64 * (term β 0 : ℝ))) := by
    unfold rho
    ring
  rw [hr]
  unfold sigma
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith [sq_nonneg (1 / (64 * (term β 0 : ℝ)))]

theorem normalized_step (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : normalized α β (n + 1) ≤ normalized α β n + 1 / (2 : ℝ) ^ n := by
  have h := deficit_step α β n
  have hg := growth_nonneg α β hb0 hba0 hab0 n
  have hw := digitSum_bounds α β n
  have hr : (deficit α β (n + 1) : ℝ) ≤ 2 * (deficit α β n : ℝ) + 2 := by
    exact_mod_cast (show deficit α β (n + 1) ≤ 2 * deficit α β n + 2 by omega)
  unfold normalized
  rw [pow_succ]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * 2)).mpr
  field_simp
  nlinarith

theorem normalized_two_step (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) (he : ExactBlock.IsEvent α β (n + 1)) :
    normalized α β (n + 2) ≤ rho β * normalized α β n +
      2 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
  have hN : (2 : ℝ) ≤ term β 0 := by exact_mod_cast initial_second_ge_two α β hba0 hab0
  have hs : 8 * (term β 0 : ℝ) * (deficit α β (n + 2) : ℝ) ≤
      (32 * (term β 0 : ℝ) - 1) * (deficit α β n : ℝ) +
        (padding α β n : ℝ) + 52 * (term β 0 : ℝ) := by
    exact_mod_cast two_step_scaled α β hb0 hba0 hab0 n he
  have hb : (padding α β n : ℝ) < 3 * (term β 0 : ℝ) + 2 * (n : ℝ) := by
    exact_mod_cast (padding_bound α β hba0 hab0 n).2
  have hn : (0 : ℝ) ≤ n := by positivity
  have hq : (deficit α β (n + 2) : ℝ) / 4 ≤
      rho β * (deficit α β n : ℝ) + 2 * ((n : ℝ) + 1) := by
    unfold rho
    apply (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < 32 * (term β 0 : ℝ))).mp
    field_simp
    nlinarith
  unfold normalized
  rw [pow_add]
  norm_num
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * 4)).mpr
  field_simp
  nlinarith

theorem potential_nonneg (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : 0 ≤ potential α β n := by
  have h := normalized_nonneg α β hb0 hba0 hab0 n
  unfold potential
  positivity

theorem normalized_le_potential (α β : ℝ) (n : ℕ) :
    normalized α β n ≤ potential α β n := by
  unfold potential
  have : 0 ≤ 9 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by positivity
  linarith

theorem potential_zero_step (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) (hw : digitSum α β n = 0) : potential α β (n + 1) ≤ potential α β n := by
  have h := normalized_zero_step α β hb0 hba0 hab0 n hw
  have herr : 9 * ((n : ℝ) + 1 + 1) / (2 : ℝ) ^ (n + 1) ≤
      9 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
    rw [pow_succ]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * 2)).mpr
    field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  unfold potential
  push_cast
  linarith

theorem potential_two_step (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) (he : ExactBlock.IsEvent α β (n + 1)) :
    potential α β (n + 2) ≤ (sigma β) ^ 2 * potential α β n := by
  have hz := normalized_two_step α β hb0 hba0 hab0 n he
  have hr := rho_bounds β (initial_second_ge_two α β hba0 hab0)
  have hs := sigma_bounds β (initial_second_ge_two α β hba0 hab0)
  have hv := potential_nonneg α β hb0 hba0 hab0 n
  have herr : 2 * ((n : ℝ) + 1) / (2 : ℝ) ^ n +
      9 * ((n : ℝ) + 2 + 1) / (2 : ℝ) ^ (n + 2) ≤
      rho β * (9 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) := by
    rw [pow_add]
    norm_num
    apply (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ n)).mp
    field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hmain : potential α β (n + 2) ≤ rho β * potential α β n := by
    unfold potential
    push_cast
    nlinarith
  exact hmain.trans (mul_le_mul_of_nonneg_right hs.2.2 hv)

theorem normalized_step_le_potential (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : normalized α β (n + 1) ≤ potential α β n := by
  have h := normalized_step α β hb0 hba0 hab0 n
  have hc : 1 / (2 : ℝ) ^ n ≤ 9 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  unfold potential
  linarith

end Dyadic354.FERecurrence
