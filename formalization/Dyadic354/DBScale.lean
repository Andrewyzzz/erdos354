import Dyadic354.DB
import Dyadic354.RationalWindows
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Dyadic354.CubicGrowth

namespace Dyadic354.DBScale

open FloorSequence FECounting FERecurrence FER RationalWindows

noncomputable def matching (β : ℝ) (q : ℕ) : ℕ := ⌊Real.logb 2 ((q : ℝ) / β)⌋₊
def blockLength (q : ℕ) : ℕ := Nat.clog 2 (8 * q)
noncomputable def scaleConstant (β : ℝ) : ℕ := Nat.clog 2 ⌈16 * β⌉₊
noncomputable def threshold (β : ℝ) (n : ℕ) : ℕ := ⌈(2 : ℝ) ^ n * β⌉₊

theorem block_sufficient (q : ℕ) : 8 * (q : ℤ) ≤ (2 : ℤ) ^ blockLength q := by
  exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (8 * q)

theorem matching_bounds (β : ℝ) (hβ : 0 < β) (q : ℕ) (hq : β ≤ q) :
    (2 : ℝ) ^ matching β q * β ≤ q ∧ (q : ℝ) < (2 : ℝ) ^ (matching β q + 1) * β := by
  have hr : 1 ≤ (q : ℝ) / β := (le_div_iff₀ hβ).mpr (by simpa using hq)
  have hpos : 0 < (q : ℝ) / β := by linarith
  have hl : 0 ≤ Real.logb 2 ((q : ℝ) / β) := Real.logb_nonneg (by norm_num) hr
  have hlow := Nat.floor_le hl
  have hhigh := Nat.lt_floor_add_one (Real.logb 2 ((q : ℝ) / β))
  change (matching β q : ℝ) ≤ _ at hlow
  change Real.logb 2 ((q : ℝ) / β) < (matching β q : ℝ) + 1 at hhigh
  have hlo := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos).mp hlow
  have hhi := (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hpos).mp hhigh
  rw [Real.rpow_natCast] at hlo
  have hp : (2 : ℝ) ^ ((matching β q : ℝ) + 1) = (2 : ℝ) ^ (matching β q + 1) := by
    rw [← Real.rpow_natCast]
    norm_cast
  rw [hp] at hhi
  exact ⟨(le_div_iff₀ hβ).mp hlo, (div_lt_iff₀ hβ).mp hhi⟩

theorem block_matching_bound (β : ℝ) (hβ : 0 < β) (q : ℕ) (hq : β ≤ q) :
    blockLength q ≤ matching β q + scaleConstant β := by
  have hb := (matching_bounds β hβ q hq).2
  have hc : 16 * β ≤ (2 : ℝ) ^ scaleConstant β := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) ⌈16 * β⌉₊
    have h' : (⌈16 * β⌉₊ : ℝ) ≤ (2 : ℝ) ^ scaleConstant β := by exact_mod_cast h
    exact (Nat.le_ceil _).trans h'
  have hp : 0 < (2 : ℝ) ^ matching β q := by positivity
  have hbound : 8 * (q : ℝ) ≤ (2 : ℝ) ^ (matching β q + scaleConstant β) := by
    rw [pow_add]
    rw [pow_succ] at hb
    nlinarith
  exact Nat.clog_le_of_le_pow (by exact_mod_cast hbound)

theorem threshold_bounds (β : ℝ) (n : ℕ) :
    (2 : ℝ) ^ n * β ≤ (threshold β n : ℝ) ∧ threshold β n ≤ 2 ^ n * ⌈β⌉₊ := by
  refine ⟨Nat.le_ceil _, ?_⟩
  apply Nat.ceil_le.mpr
  have hβ := Nat.le_ceil β
  have h := mul_le_mul_of_nonneg_left hβ (by positivity : (0 : ℝ) ≤ 2 ^ n)
  exact_mod_cast h

theorem threshold_ge_two (β : ℝ) (hβ : 2 ≤ β) (n : ℕ) : 2 ≤ threshold β n := by
  have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h := (threshold_bounds β n).1
  have hh : (2 : ℝ) ≤ threshold β n := by nlinarith
  exact_mod_cast hh

noncomputable def advance (α β : ℝ) (hirr : Irrational (α / β)) (n : ℕ) : ℕ :=
  n + blockLength (crossingDen (α / β) hirr (threshold β n))

/-- DB at a defined crossing: the approximation and finite-block hypotheses
are constructed, not supplied as premises of the final event increment. -/
theorem advance_increment (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hi : ¬ IndexedComplete (interleave α β 2)) (hirr : Irrational (α / β))
    (n : ℕ) (hn : 1 ≤ n) :
    (eventCount α β n : ℝ) + seedConstant α β / 2 * Real.exp (FE.decayRate β * eventCount α β n) - 3 ≤
      (eventCount α β (advance α β hirr n) : ℝ) := by
  let q := crossingDen (α / β) hirr (threshold β n)
  let r := crossingRat (α / β) hirr (threshold β n)
  have hr := crossingRat_spec (α / β) hirr (threshold β n)
  change r.den = q ∧ Good (α / β) r at hr
  have hq := crossing_spec (α / β) hirr (threshold β n)
  have h2 := threshold_ge_two β (DBCover.real_normalization α β hba0 hab0).1 n
  have hq2 : 2 ≤ q := h2.trans hq.1
  have hscale : (2 : ℝ) ^ n * β ≤ (q : ℝ) :=
    (threshold_bounds β n).1.trans (by exact_mod_cast hq.1)
  have hc := r.isCoprime_num_den
  rw [hr.1] at hc
  have hratio : (r.num : ℝ) / (q : ℝ) = (r : ℝ) := by rw [← hr.1, Rat.cast_def]
  exact DB.digit_propagation α β hb0 hba0 hab0 hi n (blockLength q) hn r.num q
    (by exact_mod_cast hq2) (block_sufficient q) hc (by
      simp only [Int.cast_natCast, hratio]
      simpa only [Good, hr.1] using hr.2) hscale

theorem matching_exp_bound (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hi : ¬ IndexedComplete (interleave α β 2)) (r : ℚ) (hr : Good (α / β) r)
    (hq : β ≤ (r.den : ℝ)) (hn : 1 ≤ matching β r.den) :
    seedConstant α β * Real.exp (FE.decayRate β * eventCount α β (matching β r.den)) ≤
      2 * (matching β r.den : ℝ) + 2 * (scaleConstant β : ℝ) + 5 := by
  have hnorm := DBCover.real_normalization α β hba0 hab0
  have hβ : 0 < β := by linarith [hnorm.1]
  have hq2 : 2 ≤ r.den := by exact_mod_cast hnorm.1.trans hq
  have hratio : (r.num : ℝ) / (r.den : ℝ) = (r : ℝ) := by rw [Rat.cast_def]
  have hs := DB.incomplete_seed_lt_error α β hb0 hba0 hab0 hi (matching β r.den) (blockLength r.den)
    r.num r.den (by exact_mod_cast hq2) (block_sufficient r.den) r.isCoprime_num_den (by
      simp only [Int.cast_natCast, hratio]
      exact hr)
  simp only [Int.cast_natCast] at hs
  have hscale := (matching_bounds β hβ r.den hq).1
  have hqpos : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hfrac : 3 * ((2 : ℝ) ^ matching β r.den * β) / r.den ≤ 3 := by
    apply (div_le_iff₀ hqpos).mpr
    linarith
  have he := DBDigits.error_le_length α β (matching β r.den) (blockLength r.den)
  have hk := block_matching_bound β hβ r.den hq
  have hkR : (blockLength r.den : ℝ) ≤ (matching β r.den : ℝ) + scaleConstant β := by exact_mod_cast hk
  have hf := seed_exponential_bound α β hb0 hba0 hab0 (matching β r.den) hn
  nlinarith

theorem arbitrarily_large_advance (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hi : ¬ IndexedComplete (interleave α β 2)) (hirr : Irrational (α / β)) :
    ∀ N, ∃ n, N ≤ n ∧ n ^ 3 < advance α β hirr n := by
  apply CubicGrowth.no_eventual_cubic_advance (eventCount α β) (advance α β hirr)
    (eventCount_mono α β) (eventCount_le α β) (eventCount_unbounded α β hirr)
    (FE.decayRate β) (seedConstant α β / 2) (FE.rate_positive β hb0)
    (by have h := seed_constant_positive α β hb0 hba0; positivity)
  exact (Filter.eventually_ge_atTop 1).mono (fun n hn => advance_increment α β hb0 hba0 hab0 hi hirr n hn)

theorem large_advance_matching (α β : ℝ)
    (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hirr : Irrational (α / β)) (n : ℕ)
    (hn : scaleConstant β + 4 ≤ n) (hlarge : n ^ 3 < advance α β hirr n) :
    n ^ 2 ≤ matching β (crossingDen (α / β) hirr (threshold β n)) - 1 := by
  let q := crossingDen (α / β) hirr (threshold β n)
  have hnorm := DBCover.real_normalization α β hba0 hab0
  have hβ : 0 < β := by linarith [hnorm.1]
  have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hscale := (threshold_bounds β n).1
  have hq := (crossing_spec (α / β) hirr (threshold β n)).1
  have hqR : (threshold β n : ℝ) ≤ q := by exact_mod_cast hq
  have hβq : β ≤ (q : ℝ) := by nlinarith
  have hk := block_matching_bound β hβ q hβq
  change n ^ 3 < n + blockLength q at hlarge
  have hpoly : n ^ 2 + n + scaleConstant β + 1 ≤ n ^ 3 := by
    have hprod : 0 ≤ (n - 2 : ℕ) * (n - 2) * n := Nat.zero_le _
    have hn2 : 2 ≤ n := by omega
    have he : (n - 2 : ℕ) + 2 = n := by omega
    nlinarith
  change n ^ 2 ≤ matching β q - 1
  omega

end Dyadic354.DBScale
