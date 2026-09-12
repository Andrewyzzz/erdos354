import Dyadic354.BGWindowBounds

namespace Dyadic354.BGWindows

open FloorSequence FERecurrence FER DBScale RationalWindows BGExactLayers BGWindowBounds

theorem inverse_scale_small (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n, N ≤ n → 1 / ((2 : ℝ) ^ n * β) < δ := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 / (β * δ)) (by norm_num : (1 : ℝ) < 2)
  refine ⟨N, ?_⟩
  intro n hn
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  have hm := (div_lt_iff₀ (mul_pos hβ hδ)).mp hN
  have hmp := mul_le_mul_of_nonneg_right hp (mul_pos hβ hδ).le
  apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ n * β)).mpr
  nlinarith

/-- Actual long windows under incompleteness. The event sparsity, small
height, rational accuracy, and all-layer error bounds are simultaneous
conclusions, not independent hypotheses in the later BG contradiction. -/
theorem arbitrarily_large_windows (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hi : ¬ IndexedComplete (interleave α β 2)) (hirr : Irrational (α / β))
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ T : ℕ, ∃ r : ℚ, N ≤ T ∧ (height r) ^ 2 ≤ 4 * T ∧
      (1 : ℝ) < r ∧ (r : ℝ) < 2 ∧ |α / β - (r : ℝ)| < ε ∧
      (∀ i, i ≤ T → |delta α β r.num r.den i| < (2 : ℤ) ^ height r) ∧
      seedConstant α β * Real.exp (FE.decayRate β * eventCount α β T) ≤
        2 * (T : ℝ) + 2 * (scaleConstant β : ℝ) + 7 := by
  have hnorm := DBCover.real_normalization α β hba0 hab0
  have hβ : 0 < β := by linarith [hnorm.1]
  let δ := min ε (min (α / β - 1) (2 - α / β))
  have hδ : 0 < δ := lt_min hε (lt_min (by linarith [hnorm.2.1]) (by linarith [hnorm.2.2]))
  obtain ⟨n0, hn0⟩ := inverse_scale_small β δ hβ hδ
  obtain ⟨n, hn, hlarge⟩ := arbitrarily_large_advance α β hb0 hba0 hab0 hi hirr
    (max N (max n0 (max (heightConstant β) (scaleConstant β + 4))))
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnn0 : n0 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnh : heightConstant β ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hns : scaleConstant β + 4 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  let D := crossingDen (α / β) hirr (threshold β n)
  let m := matching β D
  let T := m - 1
  have hnT : n ^ 2 ≤ T := large_advance_matching α β hba0 hab0 hirr n hns hlarge
  have hm : 1 ≤ m := by
    have hnsq : 1 ≤ n ^ 2 := by nlinarith
    dsimp [T] at hnT
    omega
  have hTplus : T + 1 = m := by dsimp [T]; omega
  obtain ⟨r, hrden, hrprec, hrnear⟩ := crossing_close α β hnorm.1 hirr n
  have hnear := hrnear.trans_lt (hn0 n hnn0)
  have heps : |α / β - (r : ℝ)| < ε := hnear.trans_le (min_le_left _ _)
  have hleft : |α / β - (r : ℝ)| < α / β - 1 :=
    hnear.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hright : |α / β - (r : ℝ)| < 2 - α / β :=
    hnear.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hr1 : (1 : ℝ) < r := by have h := (abs_lt.mp hleft).2; linarith
  have hr2 : (r : ℝ) < 2 := by have h := (abs_lt.mp hright).1; linarith
  have hheight := height_bound β n r hr1 hr2 hrden
  have hheight' : (height r) ^ 2 ≤ 4 * T := by nlinarith
  have hD := (crossing_spec (α / β) hirr (threshold β n)).1
  have hD2 := (threshold_ge_two β hnorm.1 n).trans hD
  have hDR : (threshold β n : ℝ) ≤ D := by exact_mod_cast hD
  have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hscale0 := (threshold_bounds β n).1
  have hβD : β ≤ (D : ℝ) := by nlinarith
  have hscale := (matching_bounds β hβ D hβD).1
  have hdelta := precision_to_delta α β hβ D (by omega) r hr1 hr2 hrprec m hm hscale
  have hcross := crossingRat_spec (α / β) hirr (threshold β n)
  let s := crossingRat (α / β) hirr (threshold β n)
  change s.den = D ∧ Good (α / β) s at hcross
  have hsexp := matching_exp_bound α β hb0 hba0 hab0 hi s hcross.2 (by simpa [hcross.1] using hβD)
    (by simpa [hcross.1] using hm)
  rw [hcross.1] at hsexp
  change seedConstant α β * Real.exp (FE.decayRate β * eventCount α β m) ≤
    2 * (m : ℝ) + 2 * (scaleConstant β : ℝ) + 5 at hsexp
  have hK : (eventCount α β T : ℝ) ≤ eventCount α β m := by
    exact_mod_cast eventCount_mono α β (show T ≤ m by omega)
  have ha := FE.rate_positive β hb0
  have hc := seed_constant_positive α β hb0 hba0
  have he := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hK ha.le)) hc.le
  have hfinal := he.trans hsexp
  have hmR : (m : ℝ) = (T : ℝ) + 1 := by exact_mod_cast hTplus.symm
  refine ⟨T, r, by nlinarith, hheight', hr1, hr2, heps, hdelta, ?_⟩
  rw [hmR] at hfinal
  linarith

end Dyadic354.BGWindows
