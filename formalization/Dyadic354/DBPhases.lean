import Dyadic354.CoefficientInterval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace Dyadic354.DBPhases

theorem residue_lift (p q r : ℤ) (hq : 0 < q) (hc : IsCoprime p q) :
    ∃ j m : ℤ, 0 ≤ j ∧ j < q ∧ p * j + q * m = r := by
  obtain ⟨a, b, hab⟩ := hc
  refine ⟨(a * r) % q, b * r + p * ((a * r) / q),
    Int.emod_nonneg _ (ne_of_gt hq), Int.emod_lt_of_pos _ hq, ?_⟩
  have he := Int.mul_ediv_add_emod (a * r) q
  calc
    _ = p * (q * ((a * r) / q) + (a * r) % q) + q * b * r := by ring
    _ = (a * p + b * q) * r := by rw [he]; ring
    _ = r := by rw [hab, one_mul]

/-- Every real location is followed, within 3/q, by a point of one of the
q phases. The integer lift m is subsequently restricted by finite windows. -/
theorem phase_after (θ : ℝ) (p q : ℤ) (hq : 0 < q) (hc : IsCoprime p q)
    (happrox : |θ - (p : ℝ) / q| < 1 / (q : ℝ) ^ 2) (t : ℝ) :
    ∃ j m : ℤ, 0 ≤ j ∧ j < q ∧ t < θ * j + m ∧ θ * j + m < t + 3 / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let r : ℤ := ⌈(q : ℝ) * t⌉ + 1
  obtain ⟨j, m, hj0, hjq, he⟩ := residue_lift p q r hq hc
  have hj0R : (0 : ℝ) ≤ j := by exact_mod_cast hj0
  have hjqR : (j : ℝ) < q := by exact_mod_cast hjq
  have heR : (p : ℝ) * j + (q : ℝ) * m = r := by exact_mod_cast he
  have hr0 : (q : ℝ) * t + 1 ≤ (r : ℝ) := by
    have h := Int.le_ceil ((q : ℝ) * t)
    dsimp [r]
    push_cast
    linarith
  have hr1 : (r : ℝ) < (q : ℝ) * t + 2 := by
    have h := Int.ceil_lt_add_one ((q : ℝ) * t)
    dsimp [r]
    push_cast
    linarith
  have herror : |(q : ℝ) * (θ * j + m) - r| < 1 := by
    have hid : (q : ℝ) * (θ * j + m) - r = (q : ℝ) * j * (θ - (p : ℝ) / q) := by
      rw [← heR]
      field_simp
      ring
    rw [hid, abs_mul, abs_of_nonneg (mul_nonneg hqR.le hj0R)]
    have heps := abs_nonneg (θ - (p : ℝ) / q)
    have hsmall : (q : ℝ) ^ 2 * |θ - (p : ℝ) / q| < 1 := by
      have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ 2)).mp happrox
      nlinarith
    nlinarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp herror
  refine ⟨j, m, hj0, hjq, ?_, ?_⟩
  · nlinarith
  · apply (mul_lt_mul_iff_of_pos_right hqR).mp
    field_simp
    nlinarith

end Dyadic354.DBPhases
