import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace Dyadic354.BGSparseCompact

open Set Filter
open scoped Topology

/-- A normalized binary position, including zero for padding a finite list. -/
def atoms : Set ℝ := insert 0 (Set.range (fun n : ℕ => (1 / 2 : ℝ) ^ n))

/-- At most k normalized binary terms. Repetitions are allowed here; this
larger set remains compact and consists entirely of rational numbers. -/
def sums : ℕ → Set ℝ
  | 0 => {0}
  | k + 1 => (fun xy : ℝ × ℝ => xy.1 + xy.2) '' (sums k ×ˢ atoms)

theorem atoms_compact : IsCompact atoms := by
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).isCompact_insert_range

theorem atom_rational (x : ℝ) (hx : x ∈ atoms) : ∃ r : ℚ, (r : ℝ) = x := by
  rcases hx with rfl | ⟨n, rfl⟩
  · exact ⟨0, by simp⟩
  · exact ⟨(1 / 2 : ℚ) ^ n, by push_cast; rfl⟩

theorem sums_compact (k : ℕ) : IsCompact (sums k) := by
  induction k with
  | zero => exact isCompact_singleton
  | succ k ih => exact (ih.prod atoms_compact).image (continuous_fst.add continuous_snd)

theorem sum_rational (k : ℕ) (x : ℝ) (hx : x ∈ sums k) : ∃ r : ℚ, (r : ℝ) = x := by
  induction k generalizing x with
  | zero =>
    have : x = 0 := hx
    exact ⟨0, by simpa using this.symm⟩
  | succ k ih =>
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hx
    obtain ⟨r, hr⟩ := ih a ha
    obtain ⟨s, hs⟩ := atom_rational b hb
    exact ⟨r + s, by simp [hr, hs]⟩

theorem zero_mem_sums (k : ℕ) : (0 : ℝ) ∈ sums k := by
  induction k with
  | zero => rfl
  | succ k ih => exact ⟨(0, 0), ⟨ih, Set.mem_insert _ _⟩, by simp⟩

theorem sums_mono : Monotone sums := by
  apply monotone_nat_of_le_succ
  intro k x hx
  exact ⟨(x, 0), ⟨hx, Set.mem_insert _ _⟩, by simp⟩

theorem finset_sum_mem {ι : Type*} (s : Finset ι) (f : ι → ℝ) (k : ℕ)
    (hf : ∀ i ∈ s, f i ∈ atoms) (hk : s.card ≤ k) : (∑ i ∈ s, f i) ∈ sums k := by
  classical
  suffices h : (∑ i ∈ s, f i) ∈ sums s.card from sums_mono hk h
  clear hk
  induction s using Finset.induction_on with
  | empty => simp [sums]
  | @insert i s hi ih =>
    rw [Finset.card_insert_of_notMem hi, Finset.sum_insert hi]
    exact ⟨(∑ j ∈ s, f j, f i),
      ⟨ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)), hf i (Finset.mem_insert_self _ _)⟩, by simp [add_comm]⟩

/-- Normalized pairs have denominator at least 1/2. This restriction is
essential: a quotient at denominator zero would not be a continuous map. -/
def ratios (k : ℕ) : Set ℝ :=
  (fun xy : ℝ × ℝ => xy.1 / xy.2) ''
    ((sums k ×ˢ sums k) ∩ {xy : ℝ × ℝ | (1 / 2 : ℝ) ≤ xy.2})

theorem ratios_compact (k : ℕ) : IsCompact (ratios k) := by
  have hc := (sums_compact k).prod (sums_compact k)
  have hd : IsClosed {xy : ℝ × ℝ | (1 / 2 : ℝ) ≤ xy.2} :=
    isClosed_le continuous_const continuous_snd
  apply (hc.inter_right hd).image_of_continuousOn
  apply continuousOn_fst.div continuousOn_snd
  intro xy hxy
  have h := hxy.2
  change (1 / 2 : ℝ) ≤ xy.2 at h
  linarith

theorem ratio_rational (k : ℕ) (x : ℝ) (hx : x ∈ ratios k) : ∃ r : ℚ, (r : ℝ) = x := by
  obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := hx
  obtain ⟨r, hr⟩ := sum_rational k a ha
  obtain ⟨s, hs⟩ := sum_rational k b hb
  exact ⟨r / s, by simp [hr, hs]⟩

theorem irrational_not_mem_ratios (θ : ℝ) (hθ : Irrational θ) (k : ℕ) : θ ∉ ratios k := by
  intro h
  obtain ⟨r, hr⟩ := ratio_rational k θ h
  exact hθ.ne_rat r hr.symm

/-- The compactness core of return-cost divergence. An irrational target is
separated by a positive distance from every bounded-complexity ratio set. -/
theorem irrational_separation (θ : ℝ) (hθ : Irrational θ) (k : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ ratios k, ε ≤ |θ - x| := by
  have hopen := (ratios_compact k).isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen θ (irrational_not_mem_ratios θ hθ k)
  refine ⟨ε, hε, ?_⟩
  intro x hx
  by_contra hn
  have hd : dist x θ < ε := by simpa [Real.dist_eq, abs_sub_comm] using lt_of_not_ge hn
  exact hball (Metric.mem_ball.mpr hd) hx

theorem eventually_not_bounded (θ : ℝ) (hθ : Irrational θ) (k : ℕ)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 θ)) : ∀ᶠ j in atTop, r j ∉ ratios k := by
  exact hr ((ratios_compact k).isClosed.isOpen_compl.mem_nhds (irrational_not_mem_ratios θ hθ k))

end Dyadic354.BGSparseCompact
