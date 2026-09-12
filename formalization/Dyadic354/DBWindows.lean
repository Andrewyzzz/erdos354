import Dyadic354.DBPhases

namespace Dyadic354.DBWindows

noncomputable def start (θ : ℝ) (q : ℤ) : ℤ := ⌈((q : ℝ) - 1) * θ⌉
noncomputable def finish (θ : ℝ) (q K : ℤ) : ℝ := θ * ((K : ℝ) - q) + K - 1

theorem start_bounds (θ : ℝ) (q : ℤ) (hθ : 1 < θ) (hθ2 : θ < 2) (hq : 2 ≤ q) :
    0 ≤ start θ q ∧ (start θ q : ℝ) < 2 * (q : ℝ) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlow := Int.le_ceil (((q : ℝ) - 1) * θ)
  have hhigh := Int.ceil_lt_add_one (((q : ℝ) - 1) * θ)
  change ((q : ℝ) - 1) * θ ≤ (start θ q : ℝ) at hlow
  change (start θ q : ℝ) < ((q : ℝ) - 1) * θ + 1 at hhigh
  constructor
  · have : (0 : ℝ) ≤ start θ q := by nlinarith
    exact_mod_cast this
  · nlinarith

theorem window_after (θ : ℝ) (p q K ℓ : ℤ)
    (hθ : 1 < θ) (hθ2 : θ < 2) (hq : 2 ≤ q)
    (hc : IsCoprime p q) (happrox : |θ - (p : ℝ) / q| < 1 / (q : ℝ) ^ 2)
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ K - q) (t : ℝ)
    (htlo : θ * ℓ + start θ q ≤ t) (hthi : t < θ * ℓ + K - 1) :
    ∃ x y : ℤ, 0 ≤ x ∧ x < K ∧ 0 ≤ y ∧ y < K ∧
      t < θ * x + y ∧ θ * x + y < t + 3 / q := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hθ0 : 0 ≤ θ := by linarith
  obtain ⟨j, m, hj0, hjq, ht, ht'⟩ := DBPhases.phase_after θ p q (by omega) hc happrox (t - θ * ℓ)
  have hj0R : (0 : ℝ) ≤ j := by exact_mod_cast hj0
  have hjR : (j : ℝ) ≤ (q : ℝ) - 1 := by exact_mod_cast (show j ≤ q - 1 by omega)
  have hs := Int.le_ceil (((q : ℝ) - 1) * θ)
  change ((q : ℝ) - 1) * θ ≤ (start θ q : ℝ) at hs
  by_cases hcap : θ * j + m ≤ (K : ℝ) - 1
  · refine ⟨ℓ + j, m, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · have : (0 : ℝ) ≤ m := by nlinarith
      exact_mod_cast this
    · have : (m : ℝ) < K := by nlinarith
      exact_mod_cast this
    · push_cast; nlinarith
    · push_cast; nlinarith
  · refine ⟨ℓ, K - 1, hℓ0, by omega, by omega, by omega, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith

/-- The finite windows cover their full union; their coefficient supports
never extend beyond the K by K square. -/
theorem global_after (θ : ℝ) (p q K : ℤ)
    (hθ : 1 < θ) (hθ2 : θ < 2) (hq : 2 ≤ q) (hK : 8 * q ≤ K)
    (hc : IsCoprime p q) (happrox : |θ - (p : ℝ) / q| < 1 / (q : ℝ) ^ 2)
    (t : ℝ) (htlo : (start θ q : ℝ) ≤ t) (hthi : t < finish θ q K) :
    ∃ x y : ℤ, 0 ≤ x ∧ x < K ∧ 0 ≤ y ∧ y < K ∧
      t < θ * x + y ∧ θ * x + y < t + 3 / q := by
  let ℓ : ℤ := min ⌊(t - start θ q) / θ⌋ (K - q)
  have hθpos : 0 < θ := by linarith
  have hf0 : 0 ≤ ⌊(t - start θ q) / θ⌋ := by
    exact Int.floor_nonneg.mpr (div_nonneg (by linarith) hθpos.le)
  have hℓ0 : 0 ≤ ℓ := le_min hf0 (by omega)
  have hℓ : ℓ ≤ K - q := min_le_right _ _
  have hlf : ℓ ≤ ⌊(t - start θ q) / θ⌋ := min_le_left _ _
  have hlfR : (ℓ : ℝ) ≤ ⌊(t - start θ q) / θ⌋ := by exact_mod_cast hlf
  have hlo : θ * ℓ + start θ q ≤ t := by
    have hf := Int.floor_le ((t - start θ q) / θ)
    have hdiv := (le_div_iff₀ hθpos).mp (hlfR.trans hf)
    nlinarith
  have hhi : t < θ * ℓ + K - 1 := by
    by_cases heq : ℓ = K - q
    · rw [heq]
      push_cast
      exact hthi
    · have heq' : ℓ = ⌊(t - start θ q) / θ⌋ := by dsimp [ℓ] at *; omega
      have hf := Int.lt_floor_add_one ((t - start θ q) / θ)
      rw [← heq'] at hf
      have hmul := (div_lt_iff₀ hθpos).mp hf
      have hs := (start_bounds θ q hθ hθ2 hq).2
      have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
      have hKR : 8 * (q : ℝ) ≤ K := by exact_mod_cast hK
      nlinarith
  exact window_after θ p q K ℓ hθ hθ2 hq hc happrox hℓ0 hℓ t hlo hhi

theorem span_large (θ : ℝ) (q K : ℤ)
    (hθ : 1 < θ) (hθ2 : θ < 2) (hq : 2 ≤ q) (hK : 8 * q ≤ K) :
    (K : ℝ) + 1 < finish θ q K - start θ q := by
  have hs := (start_bounds θ q hθ hθ2 hq).2
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hKR : 8 * (q : ℝ) ≤ K := by exact_mod_cast hK
  unfold finish
  nlinarith

theorem endpoints_legal (θ : ℝ) (q K : ℤ)
    (hθ : 1 < θ) (hθ2 : θ < 2) (hq : 2 ≤ q) (hK : 8 * q ≤ K) :
    (0 ≤ start θ q ∧ start θ q < K) ∧
    (0 ≤ K - q ∧ K - q < K ∧ 0 ≤ K - 1 ∧ K - 1 < K) := by
  have hs := start_bounds θ q hθ hθ2 hq
  have hs' : start θ q < 2 * q := by exact_mod_cast hs.2
  omega

theorem global_at_or_after (θ : ℝ) (p q K : ℤ)
    (hθ : 1 < θ) (hθ2 : θ < 2) (hq : 2 ≤ q) (hK : 8 * q ≤ K)
    (hc : IsCoprime p q) (happrox : |θ - (p : ℝ) / q| < 1 / (q : ℝ) ^ 2)
    (t : ℝ) (htlo : (start θ q : ℝ) ≤ t) (hthi : t ≤ finish θ q K) :
    ∃ x y : ℤ, 0 ≤ x ∧ x < K ∧ 0 ≤ y ∧ y < K ∧
      t ≤ θ * x + y ∧ θ * x + y < t + 3 / q := by
  rcases lt_or_eq_of_le hthi with ht | rfl
  · obtain ⟨x, y, hx0, hx, hy0, hy, hlo, hhi⟩ := global_after θ p q K hθ hθ2 hq hK hc happrox t htlo ht
    exact ⟨x, y, hx0, hx, hy0, hy, hlo.le, hhi⟩
  · have hleg := (endpoints_legal θ q K hθ hθ2 hq hK).2
    refine ⟨K - q, K - 1, hleg.1, hleg.2.1, hleg.2.2.1, hleg.2.2.2, ?_, ?_⟩
    · simp only [finish, Int.cast_sub, Int.cast_one]; linarith
    · have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hd : (0 : ℝ) < 3 / (q : ℝ) := by positivity
      simp only [finish, Int.cast_sub, Int.cast_one]
      linarith

end Dyadic354.DBWindows
