import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Dyadic354.BGCapacity

open Filter Asymptotics

theorem logarithmic_bound (a c d : ℝ) (ha : 0 < a) (hc : 0 < c) (hd : 0 ≤ d) :
    ∃ L : ℝ, 0 < L ∧ ∀ T X : ℝ, 1 ≤ T → 1 ≤ Real.log T →
      c * Real.exp (a * X) ≤ 2 * T + d → X ≤ L * Real.log T := by
  let C := (d + 2) / c
  let L := (1 + |Real.log C|) / a
  have hC : 0 < C := by dsimp [C]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro T X hT hlog hbound
  have hCT : Real.exp (a * X) ≤ C * T := by
    apply (mul_le_mul_iff_of_pos_left hc).mp
    dsimp [C]
    field_simp
    nlinarith
  have h := Real.log_le_log (Real.exp_pos _) hCT
  rw [Real.log_exp, Real.log_mul hC.ne' (by linarith : T ≠ 0)] at h
  have habs := le_abs_self (Real.log C)
  have hprod := mul_le_mul_of_nonneg_left hlog (abs_nonneg (Real.log C))
  have hmul : a * X ≤ (1 + |Real.log C|) * Real.log T := by nlinarith
  dsimp [L]
  apply (mul_le_mul_iff_of_pos_left ha).mp
  field_simp
  nlinarith

theorem seed_size_eventually (L : ℝ) (hL : 0 < L) (N : ℕ) :
    ∀ᶠ T : ℝ in atTop, ∀ H K : ℕ,
      (H : ℝ) ^ 2 ≤ 4 * T → (K : ℝ) ≤ L * Real.log T →
      (max (N + 1) (H * (K + 1) + 1) : ℝ) ≤ T ^ (3 / 4 : ℝ) := by
  have hlog : (fun x : ℝ => L * Real.log x + 1) =o[atTop] (fun x => x ^ (1 / 4 : ℝ)) := by
    have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul_left L
    have h2 : (fun _x : ℝ => (1 : ℝ)) =o[atTop] (fun x => x ^ (1 / 4 : ℝ)) :=
      (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto (tendsto_rpow_atTop (by norm_num))
    exact h1.add h2
  have hconst : (fun _x : ℝ => (N : ℝ) + 1) =o[atTop] (fun x => x ^ (3 / 4 : ℝ)) :=
    (isLittleO_const_id_atTop ((N : ℝ) + 1)).comp_tendsto (tendsto_rpow_atTop (by norm_num))
  filter_upwards [hlog.bound (by norm_num : (0 : ℝ) < 1 / 4),
    hconst.bound (by norm_num : (0 : ℝ) < 1 / 2), eventually_ge_atTop (1 : ℝ)] with T hlog hconst hT
  have hTpos : 0 < T := by linarith
  have hl0 : 0 ≤ Real.log T := Real.log_nonneg hT
  simp only [Real.norm_eq_abs] at hlog hconst
  rw [abs_of_nonneg (by positivity : 0 ≤ L * Real.log T + 1),
    abs_of_nonneg (Real.rpow_nonneg hTpos.le _)] at hlog
  rw [abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) + 1),
    abs_of_nonneg (Real.rpow_nonneg hTpos.le _)] at hconst
  intro H K hH hK
  have hroot : (H : ℝ) ≤ 2 * Real.sqrt T := by
    nlinarith [Real.sq_sqrt hTpos.le, Real.sqrt_nonneg T, Nat.cast_nonneg (α := ℝ) H]
  have hp : Real.sqrt T * T ^ (1 / 4 : ℝ) = T ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hTpos]
    norm_num
  have hHK := mul_le_mul hroot (show (K : ℝ) + 1 ≤ (1 / 4 : ℝ) * T ^ (1 / 4 : ℝ) by linarith)
    (by positivity) (by positivity)
  have hmax : (max (N + 1) (H * (K + 1) + 1) : ℝ) ≤ (N : ℝ) + 1 + (H : ℝ) * ((K : ℝ) + 1) := by
    apply max_le <;> nlinarith [Nat.cast_nonneg (α := ℝ) H, Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) N]
  nlinarith

theorem event_power_bound (B k : ℕ) (hB : 1 < B) (hk : 0 < k)
    (L T : ℝ) (hT : 1 ≤ T) (hcost : 8 * L * Real.log (B : ℝ) ≤ k)
    (K : ℕ) (hK : (K : ℝ) ≤ L * Real.log T) :
    (B : ℝ) ^ (K / k + 1) ≤ (B : ℝ) * T ^ (1 / 8 : ℝ) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hB)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hdiv : ((K / k : ℕ) : ℝ) * (k : ℝ) ≤ K := by exact_mod_cast Nat.div_mul_le_self K k
  have hmul := mul_le_mul_of_nonneg_right hdiv hlogB.le
  have hKmul := mul_le_mul_of_nonneg_right hK hlogB.le
  have hcmul := mul_le_mul_of_nonneg_right hcost hlogT
  have hscale : ((K / k : ℕ) : ℝ) * Real.log (B : ℝ) ≤ Real.log T / 8 := by
    apply (mul_le_mul_iff_of_pos_right hkR).mp
    nlinarith
  have hbound : ((K / k + 1 : ℕ) : ℝ) * Real.log (B : ℝ) ≤
      Real.log (B : ℝ) + Real.log T * (1 / 8 : ℝ) := by
    push_cast
    linarith
  calc
    (B : ℝ) ^ (K / k + 1) = Real.exp (((K / k + 1 : ℕ) : ℝ) * Real.log (B : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hBpos]
    _ ≤ Real.exp (Real.log (B : ℝ) + Real.log T * (1 / 8 : ℝ)) := Real.exp_le_exp.mpr hbound
    _ = (B : ℝ) * T ^ (1 / 8 : ℝ) := by
      rw [Real.exp_add, Real.exp_log hBpos, Real.rpow_def_of_pos (by linarith : 0 < T)]

/-- For sufficiently large T, the number of geometric returns required to
exceed K fits inside T whenever K is logarithmically sparse and H² ≤ 4T. -/
theorem eventual_capacity (L : ℝ) (hL : 0 < L) (B N : ℕ) (hB : 1 < B) :
    ∃ k : ℕ, 0 < k ∧ ∀ᶠ T : ℕ in atTop, ∀ H K : ℕ,
      H ^ 2 ≤ 4 * T → (K : ℝ) ≤ L * Real.log (T : ℝ) →
      2 * B ^ (K / k + 1) * max (N + 1) (H * (K + 1) + 1) ≤ T := by
  let k : ℕ := ⌈8 * L * Real.log (B : ℝ)⌉₊ + 1
  have hk : 0 < k := by dsimp [k]; omega
  have hcost : 8 * L * Real.log (B : ℝ) ≤ k := by
    have h := Nat.le_ceil (8 * L * Real.log (B : ℝ))
    dsimp [k]
    push_cast
    linarith
  refine ⟨k, hk, ?_⟩
  have hseed := tendsto_natCast_atTop_atTop.eventually (seed_size_eventually L hL N)
  have hbig := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually_ge_atTop (2 * (B : ℝ))
  have hbigN := tendsto_natCast_atTop_atTop.eventually hbig
  filter_upwards [hseed, hbigN, eventually_ge_atTop 1] with T hs hb hT
  intro H K hH hK
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hx := hs H K (by exact_mod_cast hH) hK
  have hp := event_power_bound B k hB hk L T (by exact_mod_cast hT) hcost K hK
  have hresult : (2 : ℝ) * (B : ℝ) ^ (K / k + 1) *
      (max (N + 1) (H * (K + 1) + 1) : ℝ) ≤ (T : ℝ) := by
    calc
      _ ≤ 2 * ((B : ℝ) * (T : ℝ) ^ (1 / 8 : ℝ)) * (T : ℝ) ^ (3 / 4 : ℝ) := by gcongr
      _ = (2 * (B : ℝ)) * (T : ℝ) ^ (7 / 8 : ℝ) := by
        rw [mul_assoc, mul_assoc, ← Real.rpow_add hTpos]
        norm_num
        ring
      _ ≤ (T : ℝ) ^ (1 / 8 : ℝ) * (T : ℝ) ^ (7 / 8 : ℝ) := by gcongr
      _ = (T : ℝ) := by rw [← Real.rpow_add hTpos]; norm_num
  exact_mod_cast hresult

end Dyadic354.BGCapacity
