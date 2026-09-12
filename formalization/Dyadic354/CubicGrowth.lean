import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace Dyadic354.CubicGrowth

open Filter

theorem no_eventual_quartic (K : ℕ → ℕ) (hmono : Monotone K)
    (hupper : ∀ n, K n ≤ n) (hunbounded : ∀ k, ∃ n, k ≤ K n) :
    ¬ ∃ N, ∀ n, N ≤ n → (K n) ^ 4 ≤ K (n ^ 3) := by
  rintro ⟨N, hN⟩
  obtain ⟨i, hi⟩ := hunbounded 2
  let n := max N (max 2 i)
  have hnN : N ≤ n := le_max_left _ _
  have hn2 : 2 ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hni : i ≤ n := (le_max_right _ _).trans (le_max_right _ _)
  have hKn : 2 ≤ K n := hi.trans (hmono hni)
  have hiter : ∀ r : ℕ, (K n) ^ (4 ^ r) ≤ K (n ^ (3 ^ r)) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      have hsmall : n ≤ n ^ (3 ^ r) := le_self_pow₀ (by omega) (by positivity)
      have hstep := hN (n ^ (3 ^ r)) (hnN.trans hsmall)
      calc
        (K n) ^ (4 ^ (r + 1)) = ((K n) ^ (4 ^ r)) ^ 4 := by rw [pow_succ, pow_mul]
        _ ≤ (K (n ^ (3 ^ r))) ^ 4 := Nat.pow_le_pow_left ih 4
        _ ≤ K ((n ^ (3 ^ r)) ^ 3) := hstep
        _ = K (n ^ (3 ^ (r + 1))) := by rw [pow_succ (3 : ℕ) r, pow_mul]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hbound (r : ℕ) : (4 / 3 : ℝ) ^ r ≤ Real.log (n : ℝ) / Real.log 2 := by
    have hnat : (2 : ℕ) ^ (4 ^ r) ≤ n ^ (3 ^ r) :=
      (Nat.pow_le_pow_left hKn (4 ^ r)).trans ((hiter r).trans (hupper _))
    have hreal : (2 : ℝ) ^ (4 ^ r) ≤ (n : ℝ) ^ (3 ^ r) := by exact_mod_cast hnat
    have hlog := Real.log_le_log (by positivity) hreal
    rw [Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog
    apply (le_div_iff₀ hlog2).mpr
    rw [div_pow]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ r)).mpr
    nlinarith
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt (Real.log (n : ℝ) / Real.log 2)
    (by norm_num : (1 : ℝ) < 4 / 3)
  exact (not_lt_of_ge (hbound r)) hr

theorem exponential_eventually_dominates (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x ^ 4 ≤ x + c * Real.exp (a * x) - 3 := by
  have h := (isLittleO_pow_exp_pos_mul_atTop 4 ha).bound (show 0 < c / 2 by positivity)
  filter_upwards [h, eventually_ge_atTop (3 : ℝ)] with x hx hx3
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ x ^ 4),
    abs_of_pos (Real.exp_pos _)] at hx
  have he : 0 < Real.exp (a * x) := Real.exp_pos _
  nlinarith

theorem no_eventual_cubic_advance (K f : ℕ → ℕ) (hmono : Monotone K)
    (hupper : ∀ n, K n ≤ n) (hunbounded : ∀ k, ∃ n, k ≤ K n)
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hinc : ∀ᶠ n in atTop, (K n : ℝ) + c * Real.exp (a * K n) - 3 ≤ (K (f n) : ℝ)) :
    ∀ N, ∃ n, N ≤ n ∧ n ^ 3 < f n := by
  have htK : Tendsto K atTop atTop := hmono.tendsto_atTop_atTop hunbounded
  have htR : Tendsto (fun n => (K n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp htK
  have hdom := htR.eventually (exponential_eventually_dominates a c ha hc)
  intro N
  by_contra hh
  push_neg at hh
  have hsmall : ∀ᶠ n in atTop, f n ≤ n ^ 3 :=
    (eventually_ge_atTop N).mono (fun n hn => hh n hn)
  have hquart : ∀ᶠ n in atTop, (K n) ^ 4 ≤ K (n ^ 3) := by
    filter_upwards [hinc, hdom, hsmall] with n hn hd hs
    have hm : (K (f n) : ℝ) ≤ K (n ^ 3) := by exact_mod_cast hmono hs
    have h : (K n : ℝ) ^ 4 ≤ (K (n ^ 3) : ℝ) := hd.trans (hn.trans hm)
    exact_mod_cast h
  exact no_eventual_quartic K hmono hupper hunbounded (eventually_atTop.mp hquart)

end Dyadic354.CubicGrowth
