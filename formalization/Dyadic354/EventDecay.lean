import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Dyadic354.EventDecay

open scoped Classical

/-- A disjoint-block accumulation lemma. A nonzero step consumes two
positions, so consecutive events are never charged twice. The last
unpaired position is paid for by the factor two. -/
theorem block_bound (z V : ℕ → ℝ) (K : ℕ → ℕ) (e : ℕ → Prop)
    (s : ℝ) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1)
    (hV : ∀ n, 0 ≤ V n) (hz : ∀ n, z n ≤ V n)
    (hstep : ∀ n, z (n + 1) ≤ V n)
    (hK : ∀ n, K (n + 1) = K n + if e n then 1 else 0)
    (hzero : ∀ n, ¬ e n → V (n + 1) ≤ V n)
    (htwo : ∀ n, e n → V (n + 2) ≤ s ^ 2 * V n)
    (m d : ℕ) : z (m + d) ≤ 2 * V m * s ^ (K (m + d) - K m) := by
  classical
  have hs0 : 0 ≤ s := by linarith
  have hmono : Monotone K := by
    apply monotone_nat_of_le_succ
    intro i
    rw [hK]
    split_ifs <;> omega
  induction d using Nat.strong_induction_on generalizing m with
  | h d ih =>
    by_cases hd : d = 0
    · subst d
      simpa using (hz m).trans (show V m ≤ 2 * V m by linarith [hV m])
    by_cases he : e m
    · have hk1 : K (m + 1) = K m + 1 := by simpa [he] using hK m
      by_cases hd1 : d = 1
      · subst d
        rw [hk1]
        simp only [Nat.add_sub_cancel_left, pow_one]
        exact (hstep m).trans (by nlinarith [hV m])
      have hd2 : 2 ≤ d := by omega
      have hsmall : d - 2 < d := by omega
      have hrec := ih (d - 2) hsmall (m + 2)
      have hind : m + 2 + (d - 2) = m + d := by omega
      rw [hind] at hrec
      have h2 : K (m + 2) ≤ K m + 2 := by
        have hh := hK (m + 1)
        change K (m + 2) = _ at hh
        split_ifs at hh <;> omega
      have hkn : K (m + 2) ≤ K (m + d) := hmono (by omega)
      have hkm : K m ≤ K (m + d) := hmono (by omega)
      have hpow : s ^ (2 + (K (m + d) - K (m + 2))) ≤ s ^ (K (m + d) - K m) :=
        pow_le_pow_of_le_one hs0 hs1 (by omega)
      calc
        z (m + d) ≤ 2 * V (m + 2) * s ^ (K (m + d) - K (m + 2)) := hrec
        _ ≤ 2 * (s ^ 2 * V m) * s ^ (K (m + d) - K (m + 2)) := by
          gcongr
          exact htwo m he
        _ = 2 * V m * s ^ (2 + (K (m + d) - K (m + 2))) := by rw [pow_add]; ring
        _ ≤ 2 * V m * s ^ (K (m + d) - K m) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) (hV m))
    · have hk1 : K (m + 1) = K m := by simpa [he] using hK m
      have hsmall : d - 1 < d := by omega
      have hrec := ih (d - 1) hsmall (m + 1)
      have hind : m + 1 + (d - 1) = m + d := by omega
      rw [hind, hk1] at hrec
      exact hrec.trans (by gcongr; exact hzero m he)

theorem power_le_exp (a : ℝ) (ha : 0 ≤ 1 - a) (k : ℕ) :
    (1 - a) ^ k ≤ Real.exp (-a * k) := by
  have h : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
  have hp := pow_le_pow_left₀ ha h k
  simpa only [← Real.exp_nat_mul, mul_comm (k : ℝ) (-a)] using hp

end Dyadic354.EventDecay
