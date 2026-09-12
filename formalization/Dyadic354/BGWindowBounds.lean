import Dyadic354.DBScale
import Dyadic354.BGReturns

namespace Dyadic354.BGWindowBounds

open FloorSequence FERecurrence FER DBScale RationalWindows BGExactLayers

noncomputable def heightConstant (β : ℝ) : ℕ := Nat.clog 2 (3 * ⌈β⌉₊)
def height (r : ℚ) : ℕ := Nat.clog 2 (r.num.natAbs + r.den + 1)

theorem height_bound (β : ℝ) (n : ℕ) (r : ℚ) (hr1 : (1 : ℝ) < r) (hr2 : (r : ℝ) < 2)
    (hq : r.den < threshold β n) : height r ≤ n + heightConstant β := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have he := cast_mul_den r
  have hn0 : 0 < r.num := by
    have : (0 : ℝ) < r.num := by nlinarith
    exact_mod_cast this
  have hn2 : r.num < 2 * (r.den : ℤ) := by
    have : (r.num : ℝ) < 2 * (r.den : ℝ) := by nlinarith
    exact_mod_cast this
  have habs : (r.num.natAbs : ℤ) = r.num := by omega
  have hsize : r.num.natAbs + r.den + 1 ≤ 3 * r.den := by omega
  have hb := (threshold_bounds β n).2
  have hc := Nat.le_pow_clog (by decide : 1 < 2) (3 * ⌈β⌉₊)
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  have hh := Nat.mul_le_mul_left (2 ^ n) hc
  change 2 ^ n * (3 * ⌈β⌉₊) ≤ 2 ^ n * 2 ^ heightConstant β at hh
  nlinarith

theorem precision_to_delta (α β : ℝ) (hβ : 0 < β) (D : ℕ) (hD : 0 < D)
    (r : ℚ) (hr1 : (1 : ℝ) < r) (hr2 : (r : ℝ) < 2)
    (happrox : |α / β - (r : ℝ)| ≤ 1 / ((D : ℝ) * r.den))
    (m : ℕ) (hm : 1 ≤ m) (hscale : (2 : ℝ) ^ m * β ≤ D) :
    ∀ i, i ≤ m - 1 → |delta α β r.num r.den i| < (2 : ℤ) ^ height r := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hp : 0 < r.num := by
    have he := cast_mul_den r
    have hh : (0 : ℝ) < r.num := by nlinarith
    exact_mod_cast hh
  have herr : |(r.den : ℝ) * α - (r.num : ℝ) * β| ≤ β / D := by
    have hid : (r.den : ℝ) * α - (r.num : ℝ) * β = β * r.den * (α / β - (r : ℝ)) := by
      have he := cast_mul_den r
      field_simp
      nlinarith
    rw [hid, abs_mul, abs_of_pos (mul_pos hβ hq)]
    have hh := mul_le_mul_of_nonneg_left happrox (mul_pos hβ hq).le
    convert hh using 1
    field_simp
  have hprec : (2 : ℝ) ^ (m - 1) * |(r.den : ℝ) * α - (r.num : ℝ) * β| < 1 := by
    have hh := mul_le_mul_of_nonneg_left herr (by positivity : (0 : ℝ) ≤ 2 ^ (m - 1))
    have he : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [he] at hscale
    have hhalf : (2 : ℝ) ^ (m - 1) * (β / D) ≤ 1 / 2 := by
      apply (mul_le_mul_iff_of_pos_right hDR).mp
      field_simp
      nlinarith
    linarith
  have hheight : r.num + (r.den : ℤ) + 1 ≤ (2 : ℤ) ^ height r := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) (r.num.natAbs + r.den + 1)
    have hz : (r.num.natAbs : ℤ) = r.num := by omega
    rw [← hz]
    exact_mod_cast h
  intro i hi
  exact (delta_error_bound α β r.num r.den hp (by exact_mod_cast r.pos) (m - 1) i hi hprec).trans_le hheight

theorem crossing_close (α β : ℝ) (hβ : 2 ≤ β) (hirr : Irrational (α / β)) (n : ℕ) :
    ∃ r : ℚ, r.den < threshold β n ∧
      |α / β - (r : ℝ)| ≤ 1 / ((crossingDen (α / β) hirr (threshold β n) : ℝ) * r.den) ∧
      |α / β - (r : ℝ)| ≤ 1 / ((2 : ℝ) ^ n * β) := by
  obtain ⟨r, hr, _, he⟩ := before_crossing (α / β) hirr (threshold β n) (threshold_ge_two β hβ n)
  let D := crossingDen (α / β) hirr (threshold β n)
  have hD : (2 : ℝ) ^ n * β ≤ D :=
    (threshold_bounds β n).1.trans (by exact_mod_cast (crossing_spec (α / β) hirr (threshold β n)).1)
  have hs : 0 < (2 : ℝ) ^ n * β := by
    have : 0 < β := by linarith
    positivity
  have hq : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hh : (2 : ℝ) ^ n * β ≤ (D : ℝ) * r.den := by nlinarith
  exact ⟨r, hr, he, he.trans (one_div_le_one_div_of_le hs hh)⟩

end Dyadic354.BGWindowBounds
