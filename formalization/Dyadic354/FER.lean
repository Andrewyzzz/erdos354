import Dyadic354.FE
import Dyadic354.ContiguousSeed

namespace Dyadic354.FER

open FloorSequence PrefixBounds FECounting FERecurrence FE

noncomputable def seedWidth (α β : ℝ) (n : ℕ) : ℕ := ContiguousSeed.width (values α β n)
noncomputable def seedConstant (α β : ℝ) : ℝ :=
  ((term α 0 : ℝ) + (term β 0 : ℝ)) / (2 * (constant α β + 1))

theorem term_lower (α : ℝ) (n : ℕ) : (2 : ℤ) ^ n * term α 0 ≤ term α n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (next_bounds α n).1
    rw [pow_succ]
    nlinarith

theorem total_lower (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) (hn : 1 ≤ n) :
    ((term α 0 : ℝ) + (term β 0 : ℝ)) * (2 : ℝ) ^ n / 2 ≤ (total α β n : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have he := actual_prefix_encloses α β hb0 hba0 hab0 m
  have ht : 0 ≤ total α β m := (he.2.2 _ he.1).2
  have ha := term_lower α m
  have hb := term_lower β m
  have hsum : ((term α 0 + term β 0) * (2 : ℤ) ^ m) ≤ total α β (m + 1) := by
    rw [total_step, period]
    nlinarith
  have hr : ((term α 0 : ℝ) + (term β 0 : ℝ)) * (2 : ℝ) ^ m ≤ (total α β (m + 1) : ℝ) := by
    exact_mod_cast hsum
  rw [pow_succ]
  nlinarith

theorem exp_count_le_pow (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : Real.exp (decayRate β * eventCount α β n) ≤ (2 : ℝ) ^ n := by
  have hs := sigma_bounds β (initial_second_ge_two α β hba0 hab0)
  have hr := rate_positive β hb0
  have he : (1 : ℝ) / 2 ≤ Real.exp (-decayRate β) := by
    have hex := Real.add_one_le_exp (-decayRate β)
    have hsame : sigma β = 1 - decayRate β := rfl
    rw [hsame] at hs
    linarith
  have hprod : Real.exp (decayRate β) * Real.exp (-decayRate β) = 1 := by
    rw [← Real.exp_add]; simp
  have htwo : Real.exp (decayRate β) ≤ 2 := by
    nlinarith [Real.exp_pos (decayRate β)]
  have hcount : (eventCount α β n : ℝ) ≤ n := by exact_mod_cast eventCount_le α β n
  calc
    Real.exp (decayRate β * eventCount α β n) ≤ Real.exp (decayRate β * n) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hcount hr.le
    _ = Real.exp (decayRate β) ^ n := by rw [mul_comm, Real.exp_nat_mul]
    _ ≤ (2 : ℝ) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le htwo n

theorem seed_constant_positive (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) : 0 < seedConstant α β := by
  have hN : (0 : ℝ) < term β 0 := by exact_mod_cast hb0
  have hM : (term β 0 : ℝ) < term α 0 := by exact_mod_cast hba0
  have hc := constant_positive α β hb0 hba0
  unfold seedConstant
  apply div_pos <;> linarith

/-- Manuscript FE-R for the width of an actual contiguous integer interval,
not for a multiset or a density surrogate. -/
theorem seed_exponential_bound (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) (hn : 1 ≤ n) :
    seedConstant α β * Real.exp (decayRate β * eventCount α β n) ≤ (seedWidth α β n : ℝ) + 2 := by
  let e := (Finset.Icc 0 (total α β n) \ values α β n).card
  let E := Real.exp (decayRate β * eventCount α β n)
  have hE : 0 < E := Real.exp_pos _
  have he := actual_prefix_encloses α β hb0 hba0 hab0 n
  have ht : 0 ≤ total α β n := (he.2.2 _ he.1).2
  have hS : values α β n ⊆ Finset.Icc 0 (total α β n) := by
    intro x hx
    exact Finset.mem_Icc.mpr (he.2.2 x hx)
  have hr := ContiguousSeed.width_count_bound (values α β n) (total α β n) ht hS
  have hr' : (total α β n : ℝ) + 2 ≤ ((e : ℝ) + 1) * ((seedWidth α β n : ℝ) + 2) := by
    exact_mod_cast hr
  have hsubset : Finset.Icc 0 (total α β n) \ values α β n ⊆ holes α β n := by
    intro x hx
    obtain ⟨hx, hxnot⟩ := Finset.mem_sdiff.mp hx
    have hx' := Finset.mem_Icc.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr ⟨hx'.1,
      lt_of_le_of_lt hx'.2 (total_lt_period α β (lt_trans hb0 hba0) hb0 n)⟩, hxnot⟩
  have heq : (e : ℝ) ≤ (deficit α β n : ℝ) := by
    rw [deficit_eq_holes α β hb0 hba0 hab0 n]
    exact_mod_cast Finset.card_le_card hsubset
  have hQ := deficit_exponential_bound α β hb0 hba0 hab0 n
  have hcancel : Real.exp (-decayRate β * eventCount α β n) * E = 1 := by
    dsimp [E]
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hQ' : (deficit α β n : ℝ) * E ≤ constant α β * (2 : ℝ) ^ n := by
    have h := mul_le_mul_of_nonneg_right hQ hE.le
    simpa only [mul_assoc, hcancel, mul_one] using h
  have hEP := exp_count_le_pow α β hb0 hba0 hab0 n
  change E ≤ (2 : ℝ) ^ n at hEP
  have heE : ((e : ℝ) + 1) * E ≤ (constant α β + 1) * (2 : ℝ) ^ n := by
    have h := mul_le_mul_of_nonneg_right heq hE.le
    nlinarith
  have hwidth : 0 ≤ (seedWidth α β n : ℝ) + 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hr' hE.le
  have hmul' := mul_le_mul_of_nonneg_right heE hwidth
  have htotal := total_lower α β hb0 hba0 hab0 n hn
  have htotal' := mul_le_mul_of_nonneg_right htotal hE.le
  have hscaled : (((term α 0 : ℝ) + (term β 0 : ℝ)) * E) * (2 : ℝ) ^ n ≤
      (2 * (constant α β + 1) * ((seedWidth α β n : ℝ) + 2)) * (2 : ℝ) ^ n := by
    nlinarith
  have hc := constant_positive α β hb0 hba0
  have hfinal := (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ n)).mp hscaled
  unfold seedConstant
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by linarith : 0 < 2 * (constant α β + 1))).mpr
  nlinarith

theorem seed_interval_exists (α β : ℝ) (n : ℕ) :
    ∃ x y : ℤ, x ≤ y ∧ Finset.Icc x y ⊆ values α β n ∧ y - x = (seedWidth α β n : ℤ) :=
  ContiguousSeed.width_attained _ (PermanentMesh.prefix_nonempty _ _)

end Dyadic354.FER
