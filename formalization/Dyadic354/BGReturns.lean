import Dyadic354.BGBinaryRatio
import Dyadic354.BGExactLayers

namespace Dyadic354.BGReturns

open FloorSequence FECounting FERecurrence BGExactLayers
open scoped Classical

noncomputable def word (γ : ℝ) (n h : ℕ) : ℤ := term γ (n + h) - (2 : ℤ) ^ h * term γ n
noncomputable def support (α β : ℝ) (n h : ℕ) : Finset ℕ :=
  (Finset.range h).filter (fun j => digitSum α β (n + j) ≠ 0)

theorem word_step (γ : ℝ) (n h : ℕ) :
    word γ n (h + 1) = 2 * word γ n h + correction γ (n + h) := by
  unfold word correction
  rw [pow_succ]
  simp only [Nat.add_assoc]
  ring

theorem word_polynomial (γ : ℝ) (n h : ℕ) :
    word γ n h = ∑ j ∈ Finset.range h, (2 : ℤ) ^ (h - 1 - j) * correction γ (n + j) := by
  induction h with
  | zero => simp [word]
  | succ h ih =>
    rw [word_step, ih, Finset.sum_range_succ]
    have he : (h + 1 - 1 - h) = 0 := by omega
    rw [he, pow_zero, one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show h + 1 - 1 - j = (h - 1 - j) + 1 by omega, pow_succ]
    ring

theorem support_card (α β : ℝ) (n h : ℕ) :
    (support α β n h).card = eventCount α β (n + h) - eventCount α β n := by
  have hcount : eventCount α β (n + h) = eventCount α β n + (support α β n h).card := by
    induction h with
    | zero => simp [support]
    | succ h ih =>
      rw [show n + (h + 1) = (n + h) + 1 by omega, eventCount_step, ih]
      simp only [support, Finset.range_add_one, Finset.filter_insert]
      by_cases hz : digitSum α β (n + h) = 0
      · simp [hz]
      · simp [hz, Finset.mem_filter, Nat.add_assoc]
  omega

theorem support_polynomials (α β : ℝ) (n h : ℕ) :
    word α n h = ∑ j ∈ support α β n h, (2 : ℤ) ^ (h - 1 - j) * correction α (n + j) ∧
    word β n h = ∑ j ∈ support α β n h, (2 : ℤ) ^ (h - 1 - j) * correction β (n + j) := by
  have hsub : support α β n h ⊆ Finset.range h := Finset.filter_subset _ _
  have hz (j : ℕ) (hj : j ∈ Finset.range h) (hn : j ∉ support α β n h) :
      correction α (n + j) = 0 ∧ correction β (n + j) = 0 := by
    have hw : digitSum α β (n + j) = 0 := by simpa [support, hj] using hn
    have ha := correction_bounds α (n + j)
    have hb := correction_bounds β (n + j)
    unfold digitSum at hw
    omega
  constructor
  · rw [word_polynomial]
    exact (Finset.sum_subset hsub (fun j hj hn => by rw [(hz j hj hn).1, mul_zero])).symm
  · rw [word_polynomial]
    exact (Finset.sum_subset hsub (fun j hj hn => by rw [(hz j hj hn).2, mul_zero])).symm

theorem exact_word_relation (α β : ℝ) (p q : ℤ) (n h : ℕ)
    (hn : delta α β p q n = 0) (hh : delta α β p q (n + h) = 0) :
    q * word α n h = p * word β n h := by
  unfold delta at hn hh
  unfold word
  linear_combination hh - (2 : ℤ) ^ h * hn

/-- Exact returns with few actual event positions have a bounded-complexity
ratio. Both columns are reconstructed from the same finite support. -/
theorem return_ratio_mem (α β : ℝ) (p q : ℤ) (hq : 0 < q) (n h k : ℕ)
    (hn : delta α β p q n = 0) (hh : delta α β p q (n + h) = 0)
    (he : (support α β n h).Nonempty)
    (hk : eventCount α β (n + h) - eventCount α β n ≤ k)
    (hr1 : (1 : ℝ) < (p : ℝ) / q) (hr2 : (p : ℝ) / q < 2) :
    (p : ℝ) / q ∈ BGSparseCompact.ratios k := by
  have ha (j : ℕ) (_hj : j ∈ support α β n h) :
      (correction α (n + j) : ℝ) = 0 ∨ (correction α (n + j) : ℝ) = 1 := by
    have hb := correction_bounds α (n + j)
    have hh : correction α (n + j) = 0 ∨ correction α (n + j) = 1 := by omega
    exact_mod_cast hh
  have hb (j : ℕ) (_hj : j ∈ support α β n h) :
      (correction β (n + j) : ℝ) = 0 ∨ (correction β (n + j) : ℝ) = 1 := by
    have hb := correction_bounds β (n + j)
    have hh : correction β (n + j) = 0 ∨ correction β (n + j) = 1 := by omega
    exact_mod_cast hh
  have hab (j : ℕ) (hj : j ∈ support α β n h) :
      (correction α (n + j) : ℝ) = 1 ∨ (correction β (n + j) : ℝ) = 1 := by
    have hw := (Finset.mem_filter.mp hj).2
    have ha := correction_bounds α (n + j)
    have hb := correction_bounds β (n + j)
    have hh : correction α (n + j) = 1 ∨ correction β (n + j) = 1 := by unfold digitSum at hw; omega
    exact_mod_cast hh
  apply BGBinaryRatio.ratio_mem (support α β n h) he h k
    (fun j hj => Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
    (by rwa [support_card]) (fun j => (correction α (n + j) : ℝ)) (fun j => (correction β (n + j) : ℝ))
    ha hb hab ((p : ℝ) / q) hr1 hr2
  have hw := exact_word_relation α β p q n h hn hh
  rw [(support_polynomials α β n h).1, (support_polynomials α β n h).2] at hw
  have hwR : (q : ℝ) * (∑ j ∈ support α β n h, (2 : ℝ) ^ (h - 1 - j) * (correction α (n + j) : ℝ)) =
      (p : ℝ) * (∑ j ∈ support α β n h, (2 : ℝ) ^ (h - 1 - j) * (correction β (n + j) : ℝ)) := by exact_mod_cast hw
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  apply (mul_right_cancel₀ hqR)
  field_simp
  nlinarith

/-- The operational return-cost divergence used in BG. Near a fixed
irrational ratio, every nontrivial exact return costs more than any fixed
number k of events. This applies uniformly to all common multipliers. -/
theorem return_cost_unbounded (α β : ℝ) (hirr : Irrational (α / β)) (k : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p q : ℤ, 0 < q →
      (1 : ℝ) < (p : ℝ) / q → (p : ℝ) / q < 2 →
      |α / β - (p : ℝ) / q| < ε →
      ∀ n h : ℕ, delta α β p q n = 0 → delta α β p q (n + h) = 0 →
        (support α β n h).Nonempty → k < eventCount α β (n + h) - eventCount α β n := by
  obtain ⟨ε, hε, hsep⟩ := BGSparseCompact.irrational_separation (α / β) hirr k
  refine ⟨ε, hε, ?_⟩
  intro p q hq hr1 hr2 hnear n h hn hh he
  by_contra hbad
  have hmem := return_ratio_mem α β p q hq n h k hn hh he (by omega) hr1 hr2
  have hfar := hsep _ hmem
  linarith

end Dyadic354.BGReturns
