import Dyadic354.FERecurrence
import Dyadic354.Representations

namespace Dyadic354.DBDigits

open FloorSequence FECounting FERecurrence

noncomputable def residual (γ : ℝ) (i : ℕ) : ℝ := (2 : ℝ) ^ i * γ - (term γ i : ℝ)
noncomputable def error (α β : ℝ) (n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (residual α (n + i) + residual β (n + i))

theorem residual_bounds (γ : ℝ) (i : ℕ) : 0 ≤ residual γ i ∧ residual γ i < 1 := by
  have hlo := Int.floor_le ((2 : ℝ) ^ i * γ)
  have hhi := Int.lt_floor_add_one ((2 : ℝ) ^ i * γ)
  change 0 ≤ (2 : ℝ) ^ i * γ - (⌊(2 : ℝ) ^ i * γ⌋ : ℝ) ∧
    (2 : ℝ) ^ i * γ - (⌊(2 : ℝ) ^ i * γ⌋ : ℝ) < 1
  constructor <;> linarith

theorem residual_step (γ : ℝ) (i : ℕ) :
    residual γ (i + 1) = 2 * residual γ i - (correction γ i : ℝ) := by
  unfold residual correction
  push_cast
  rw [pow_succ]
  ring

theorem residual_telescope (γ : ℝ) (n k : ℕ) :
    (∑ i ∈ Finset.range k, residual γ (n + i)) =
      (∑ i ∈ Finset.range k, (correction γ (n + i) : ℝ)) - residual γ n + residual γ (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rw [show n + (k + 1) = (n + k) + 1 by omega, residual_step]
    ring

theorem digit_budget (α β : ℝ) (n k : ℕ) :
    (∑ i ∈ Finset.range k, digitSum α β (n + i)) ≤
      2 * ((eventCount α β (n + k) : ℤ) - (eventCount α β n : ℤ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, show n + (k + 1) = (n + k) + 1 by omega, eventCount_step]
    have hw := digitSum_bounds α β (n + k)
    split_ifs <;> push_cast <;> omega

theorem error_nonneg (α β : ℝ) (n k : ℕ) : 0 ≤ error α β n k :=
  Finset.sum_nonneg (fun i _ => add_nonneg (residual_bounds α (n + i)).1 (residual_bounds β (n + i)).1)

/-- Equation (9.1): an error bound in the number of actual nonzero digit
pairs, obtained by telescoping; no asymptotic error premise is supplied. -/
theorem error_lt_budget (α β : ℝ) (n k : ℕ) :
    error α β n k < 2 * ((eventCount α β (n + k) : ℝ) - (eventCount α β n : ℝ)) + 2 := by
  have h := digit_budget α β n k
  have hr : (∑ i ∈ Finset.range k, (digitSum α β (n + i) : ℝ)) ≤
      2 * ((eventCount α β (n + k) : ℝ) - (eventCount α β n : ℝ)) := by exact_mod_cast h
  have ha0 := residual_bounds α n
  have hb0 := residual_bounds β n
  have ha1 := residual_bounds α (n + k)
  have hb1 := residual_bounds β (n + k)
  unfold error
  rw [Finset.sum_add_distrib, residual_telescope, residual_telescope]
  simp only [digitSum, Int.cast_add, Finset.sum_add_distrib] at hr
  linarith

theorem error_le_length (α β : ℝ) (n k : ℕ) : error α β n k ≤ 2 * (k : ℝ) := by
  calc
    _ ≤ ∑ _i ∈ Finset.range k, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have ha := residual_bounds α (n + i)
      have hb := residual_bounds β (n + i)
      linarith
    _ = _ := by simp; ring

theorem column_suffix (γ : ℝ) (n k x : ℕ) (hx : x < 2 ^ k) :
    ∃ s : Finset ℕ, s ⊆ Finset.range k ∧
      (2 : ℝ) ^ n * γ * x - (∑ i ∈ s, (term γ (n + i) : ℝ)) =
        ∑ i ∈ s, residual γ (n + i) := by
  obtain ⟨s, hs, he⟩ := CoefficientInterval.binary_sum_exists k x hx
  refine ⟨s, hs, ?_⟩
  have he' : (x : ℝ) = ∑ i ∈ s, (2 : ℝ) ^ i := by exact_mod_cast he
  rw [he', Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold residual
  rw [pow_add]
  ring

theorem subset_error_bound (α β : ℝ) (n k : ℕ) (s t : Finset ℕ)
    (hs : s ⊆ Finset.range k) (ht : t ⊆ Finset.range k) :
    0 ≤ (∑ i ∈ s, residual α (n + i)) + (∑ i ∈ t, residual β (n + i)) ∧
    (∑ i ∈ s, residual α (n + i)) + (∑ i ∈ t, residual β (n + i)) ≤ error α β n k := by
  constructor
  · exact add_nonneg (Finset.sum_nonneg (fun i _ => (residual_bounds α (n + i)).1))
      (Finset.sum_nonneg (fun i _ => (residual_bounds β (n + i)).1))
  · unfold error
    rw [Finset.sum_add_distrib]
    exact add_le_add (Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => (residual_bounds α (n + i)).1))
      (Finset.sum_le_sum_of_subset_of_nonneg ht (fun i _ _ => (residual_bounds β (n + i)).1))

theorem suffix_legality (α β : ℝ) (n k : ℕ) (s t : Finset ℕ)
    (hs : s ⊆ Finset.range k) (ht : t ⊆ Finset.range k) :
    (∑ i ∈ s, term α (n + i)) + (∑ i ∈ t, term β (n + i)) ∈
      finiteSubsetSums (interleave α β 2) (Finset.Ico (2 * n) (2 * (n + k))) := by
  let a := s.image (fun i => 2 * (n + i))
  let b := t.image (fun i => 2 * (n + i) + 1)
  have hd : Disjoint a b := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hz'
    omega
  apply (mem_finiteSubsetSums _ _ _).mpr
  refine ⟨a ∪ b, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hb := Finset.mem_range.mp (hs hi)
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hb := Finset.mem_range.mp (ht hi)
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · rw [Finset.sum_union hd]
    dsimp [a, b]
    rw [Finset.sum_image (fun i _ j _ he => by omega),
      Finset.sum_image (fun i _ j _ he => by omega)]
    simp only [interleave_even, interleave_odd]

/-- Every finite ideal coefficient pair has a legal suffix representation,
with its entire downward error bounded by the same proved budget. -/
theorem suffix_approximation (α β : ℝ) (n k x y : ℕ) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    ∃ z ∈ finiteSubsetSums (interleave α β 2) (Finset.Ico (2 * n) (2 * (n + k))),
      0 ≤ (2 : ℝ) ^ n * (α * x + β * y) - (z : ℝ) ∧
      (2 : ℝ) ^ n * (α * x + β * y) - (z : ℝ) ≤ error α β n k := by
  obtain ⟨s, hs, he⟩ := column_suffix α n k x hx
  obtain ⟨t, ht, he'⟩ := column_suffix β n k y hy
  refine ⟨(∑ i ∈ s, term α (n + i)) + (∑ i ∈ t, term β (n + i)),
    suffix_legality α β n k s t hs ht, ?_⟩
  have h := subset_error_bound α β n k s t hs ht
  push_cast
  constructor <;> nlinarith

theorem prefix_suffix_add (α β : ℝ) (n k : ℕ) (x y : ℤ)
    (hx : x ∈ values α β n)
    (hy : y ∈ finiteSubsetSums (interleave α β 2) (Finset.Ico (2 * n) (2 * (n + k)))) :
    x + y ∈ values α β (n + k) := by
  obtain ⟨s, hs, he⟩ := (mem_finiteSubsetSums _ _ _).mp hx
  obtain ⟨t, ht, he'⟩ := (mem_finiteSubsetSums _ _ _).mp hy
  have hd : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    have h1 := Finset.mem_range.mp (hs hi)
    have h2 := Finset.mem_Ico.mp (ht hi')
    omega
  apply (mem_finiteSubsetSums _ _ _).mpr
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · have h := Finset.mem_range.mp (hs hi)
      exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (Finset.mem_Ico.mp (ht hi)).2
  · rw [Finset.sum_union hd, ← he, ← he']

end Dyadic354.DBDigits
