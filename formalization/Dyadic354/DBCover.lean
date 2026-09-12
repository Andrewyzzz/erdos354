import Dyadic354.DBWindows
import Dyadic354.DBDigits
import Dyadic354.FER
import Dyadic354.UnitMesh

namespace Dyadic354.DBCover

open FloorSequence FECounting

theorem real_normalization (α β : ℝ)
    (hba : term β 0 < term α 0) (hab : term α 0 < 2 * term β 0) :
    2 ≤ β ∧ 1 < α / β ∧ α / β < 2 := by
  have hN := FERecurrence.initial_second_ge_two α β hba hab
  have hb0 := Int.floor_le β
  have hb1 := Int.lt_floor_add_one β
  have ha0 := Int.floor_le α
  have ha1 := Int.lt_floor_add_one α
  have ht (γ : ℝ) : term γ 0 = ⌊γ⌋ := by simp [floorMultiples]
  rw [ht, ht] at hba hab
  rw [ht] at hN
  have hN' : (2 : ℝ) ≤ (⌊β⌋ : ℝ) := by exact_mod_cast hN
  have hba' : (⌊β⌋ : ℝ) + 1 ≤ (⌊α⌋ : ℝ) := by exact_mod_cast hba
  have hab' : (⌊α⌋ : ℝ) + 1 ≤ 2 * (⌊β⌋ : ℝ) := by exact_mod_cast hab
  have hβ : 0 < β := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · apply (lt_div_iff₀ hβ).mpr
    linarith
  · apply (div_lt_iff₀ hβ).mpr
    linarith

theorem coefficient_approximation (α β : ℝ) (hβ : β ≠ 0) (n k : ℕ) (x y : ℤ)
    (hx0 : 0 ≤ x) (hx : x < (2 : ℤ) ^ k) (hy0 : 0 ≤ y) (hy : y < (2 : ℤ) ^ k) :
    ∃ z ∈ finiteSubsetSums (interleave α β 2) (Finset.Ico (2 * n) (2 * (n + k))),
      (2 : ℝ) ^ n * β * (α / β * x + y) - DBDigits.error α β n k ≤ (z : ℝ) ∧
      (z : ℝ) ≤ (2 : ℝ) ^ n * β * (α / β * x + y) := by
  have hx' : x.toNat < 2 ^ k := by exact_mod_cast (show (x.toNat : ℤ) < (2 : ℤ) ^ k by simpa using hx)
  have hy' : y.toNat < 2 ^ k := by exact_mod_cast (show (y.toNat : ℤ) < (2 : ℤ) ^ k by simpa using hy)
  obtain ⟨z, hz, hlo, hhi⟩ := DBDigits.suffix_approximation α β n k x.toNat y.toNat hx' hy'
  have hxc : (x.toNat : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hx0
  have hyc : (y.toNat : ℝ) = (y : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hy0
  rw [hxc, hyc] at hlo hhi
  have hid : (2 : ℝ) ^ n * β * (α / β * x + y) = (2 : ℝ) ^ n * (α * x + β * y) := by
    field_simp
  rw [hid]
  exact ⟨z, hz, by linarith, by linarith⟩

/-- A seed meeting the digit-error budget produces a new genuine integer
interval longer than the next unused beta weight. Ceiling/floor losses
are included explicitly. -/
theorem propagated_interval (α β : ℝ)
    (hba : term β 0 < term α 0) (hab : term α 0 < 2 * term β 0)
    (n k : ℕ) (p q : ℤ) (hq : 2 ≤ q) (hK : 8 * q ≤ (2 : ℤ) ^ k)
    (hc : IsCoprime p q) (happrox : |α / β - (p : ℝ) / q| < 1 / (q : ℝ) ^ 2)
    (a b : ℤ) (hseed : Finset.Icc a b ⊆ values α β n)
    (hwidth : 3 * ((2 : ℝ) ^ n * β) / q + DBDigits.error α β n k ≤ (b - a : ℤ)) :
    ∃ c d : ℤ, c ≤ d ∧ Finset.Icc c d ⊆ values α β (n + k) ∧ term β (n + k) < d - c := by
  let θ := α / β
  let K : ℤ := 2 ^ k
  let scale := (2 : ℝ) ^ n * β
  let E := DBDigits.error α β n k
  have hnorm := real_normalization α β hba hab
  have hβ : 0 < β := by linarith [hnorm.1]
  have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hscale : 2 ≤ scale := by dsimp [scale]; nlinarith [hnorm.1]
  have hscale_pos : 0 < scale := by linarith
  let A : ℝ := scale * DBWindows.start θ q + b - E
  let B : ℝ := scale * DBWindows.finish θ q K + b - E
  let c : ℤ := ⌈A⌉
  let d : ℤ := ⌊B⌋
  have hspan := DBWindows.span_large θ q K hnorm.2.1 hnorm.2.2 hq hK
  have hc0 : A ≤ (c : ℝ) := Int.le_ceil A
  have hc1 : (c : ℝ) < A + 1 := Int.ceil_lt_add_one A
  have hd0 : (d : ℝ) ≤ B := Int.floor_le B
  have hd1 : B < (d : ℝ) + 1 := Int.lt_floor_add_one B
  have hgap : scale * (K : ℝ) < (d : ℝ) - c := by
    have hmul := mul_lt_mul_of_pos_left hspan hscale_pos
    dsimp [A, B] at hc1 hd1
    nlinarith
  have hKpos : (0 : ℝ) < K := by dsimp [K]; positivity
  have hcd : c ≤ d := by
    have : (c : ℝ) < d := by nlinarith
    exact_mod_cast this.le
  refine ⟨c, d, hcd, ?_, ?_⟩
  · intro z hz
    obtain ⟨hcz, hzd⟩ := Finset.mem_Icc.mp hz
    have hczR : (c : ℝ) ≤ z := by exact_mod_cast hcz
    have hzdR : (z : ℝ) ≤ d := by exact_mod_cast hzd
    let t : ℝ := ((z : ℝ) - b + E) / scale
    have htlo : (DBWindows.start θ q : ℝ) ≤ t := by
      apply (le_div_iff₀ hscale_pos).mpr
      dsimp [A] at hc0
      nlinarith
    have hthi : t ≤ DBWindows.finish θ q K := by
      apply (div_le_iff₀ hscale_pos).mpr
      dsimp [B] at hd0
      nlinarith
    obtain ⟨x, y, hx0, hx, hy0, hy, hlo, hhi⟩ :=
      DBWindows.global_at_or_after θ p q K hnorm.2.1 hnorm.2.2 hq hK hc happrox t htlo hthi
    obtain ⟨v, hv, hvlo, hvhi⟩ := coefficient_approximation α β hβ.ne' n k x y hx0 hx hy0 hy
    change scale * (θ * x + y) - E ≤ (v : ℝ) at hvlo
    change (v : ℝ) ≤ scale * (θ * x + y) at hvhi
    have ht : t * scale = (z : ℝ) - b + E := div_mul_cancel₀ _ hscale_pos.ne'
    have hlo' := mul_le_mul_of_nonneg_right hlo hscale_pos.le
    have hhi' := mul_lt_mul_of_pos_right hhi hscale_pos
    have hw : 3 * scale / q + E ≤ (b : ℝ) - a := by simpa only [Int.cast_sub] using hwidth
    have hident : (3 / (q : ℝ)) * scale = 3 * scale / q := by ring
    have ha : (a : ℝ) ≤ (z : ℝ) - v := by nlinarith
    have hb : (z : ℝ) - v ≤ (b : ℝ) := by nlinarith
    have habZ : a ≤ z - v ∧ z - v ≤ b := by exact_mod_cast (show (a : ℝ) ≤ (z : ℝ) - v ∧ (z : ℝ) - v ≤ (b : ℝ) from ⟨ha, hb⟩)
    have h := DBDigits.prefix_suffix_add α β n k (z - v) v (hseed (Finset.mem_Icc.mpr habZ)) hv
    simpa only [sub_add_cancel] using h
  · have hf := Int.floor_le ((2 : ℝ) ^ (n + k) * β)
    have hid : (2 : ℝ) ^ (n + k) * β = scale * (K : ℝ) := by
      dsimp [scale, K]
      push_cast
      rw [pow_add]
      ring
    rw [hid] at hf
    have hh : (term β (n + k) : ℝ) < (d : ℝ) - c := by
      change (⌊(2 : ℝ) ^ (n + k) * β⌋ : ℝ) < _
      rw [hid]
      exact hf.trans_lt hgap
    exact_mod_cast hh

end Dyadic354.DBCover
