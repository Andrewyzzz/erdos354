import Dyadic354.PairReindex

namespace Dyadic354.PrefixMesh

open Mesh PermanentMesh

/-- Allow separated hulls as well as overlapping ones. The new bridge is
paid for explicitly; Lemma 2.2 alone does not cover this case. -/
theorem translate_union_mesh (W : Finset ℤ) (lo hi c : ℤ) (k : ℕ)
    (hm : MeshOn W lo hi k) (hc : 0 ≤ c) (hbridge : c ≤ hi - lo + k) :
    MeshOn (W ∪ translate W c) lo (hi + c) k := by
  refine ⟨⟨Finset.mem_union_left _ hm.1.1, ?_, ?_⟩, ?_⟩
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨hi, hm.1.2.1, rfl⟩)
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · have := hm.1.2.2 w hw
      constructor <;> omega
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      have := hm.1.2.2 v hv
      constructor <;> omega
  · intro z hlz hzu
    by_cases hzi : z ≤ hi
    · obtain ⟨w, hw, hzw, hwk⟩ := hm.2 z hlz hzi
      exact ⟨w, Finset.mem_union_left _ hw, hzw, hwk⟩
    · by_cases hzl : lo ≤ z - c
      · obtain ⟨w, hw, hzw, hwk⟩ := hm.2 (z - c) hzl (by omega)
        exact ⟨w + c, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩),
          by omega, by omega⟩
      · exact ⟨lo + c, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨lo, hm.1.1, rfl⟩),
          by omega, by omega⟩

theorem prefix_zero (v : ℕ → ℤ) : prefixSums v 0 = {0} := by
  simp [prefixSums, finiteSubsetSums]

/-- Equality, not only inclusion: all choices either omit or use the last
original index exactly once. Equal-valued sums are still counted only once. -/
theorem prefix_step (v : ℕ → ℤ) (n : ℕ) :
    prefixSums v (n + 1) = prefixSums v n ∪ translate (prefixSums v n) (v n) := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨s, hs, he⟩ := (mem_finiteSubsetSums _ _ _).mp hz
    by_cases hn : n ∈ s
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨∑ i ∈ s.erase n, v i, ?_, ?_⟩
      · apply (mem_finiteSubsetSums _ _ _).mpr
        refine ⟨s.erase n, ?_, rfl⟩
        intro i hi
        have hi' := Finset.mem_erase.mp hi
        have hiN := Finset.mem_range.mp (hs hi'.2)
        exact Finset.mem_range.mpr (by omega)
      · rw [he]
        exact Finset.sum_erase_add _ _ hn
    · apply Finset.mem_union_left
      apply (mem_finiteSubsetSums _ _ _).mpr
      refine ⟨s, ?_, he⟩
      intro i hi
      have hiN := Finset.mem_range.mp (hs hi)
      have hne : i ≠ n := by rintro rfl; exact hn hi
      exact Finset.mem_range.mpr (by omega)
  · exact extend_step_subset v n _ (Finset.Subset.refl _)

theorem prefix_encloses (v : ℕ → ℤ) (hp : ∀ i, 0 ≤ v i) (n : ℕ) :
    Encloses (prefixSums v n) 0 (∑ i ∈ Finset.range n, v i) := by
  refine ⟨(mem_finiteSubsetSums _ _ _).mpr ⟨∅, Finset.empty_subset _, by simp⟩,
    (mem_finiteSubsetSums _ _ _).mpr ⟨Finset.range n, Finset.Subset.refl _, rfl⟩, ?_⟩
  intro z hz
  obtain ⟨s, hs, rfl⟩ := (mem_finiteSubsetSums _ _ _).mp hz
  exact ⟨Finset.sum_nonneg (fun i _ => hp i),
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => hp i)⟩

theorem prefix_span (v : ℕ → ℤ) (hp : ∀ i, 0 ≤ v i) (n : ℕ) :
    span (prefixSums v n) (prefix_nonempty v n) = ∑ i ∈ Finset.range n, v i := by
  rw [span_of_encloses _ _ _ _ (prefix_encloses v hp n), sub_zero]

/-- The deficit bound follows from the adjacent doubling bound alone. -/
theorem next_weight_bound (v : ℕ → ℤ) (hd : ∀ i, v (i + 1) ≤ 2 * v i) :
    ∀ n, v n ≤ (∑ i ∈ Finset.range n, v i) + v 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hd n
      omega

/-- Section 1.1: every finite prefix has maximum adjacent distance at most
the first weight, including prefixes whose two translated hulls are disjoint. -/
theorem prefix_gap_bound (v : ℕ → ℤ) (hp : ∀ i, 0 < v i)
    (hd : ∀ i, v (i + 1) ≤ 2 * v i) (n : ℕ) :
    gap (prefixSums v n) ≤ (v 0).toNat := by
  have hk : 0 < (v 0).toNat := by have := hp 0; omega
  have hmesh : ∀ t, MeshOn (prefixSums v t) 0 (∑ i ∈ Finset.range t, v i) (v 0).toNat := by
    intro t
    induction t with
    | zero =>
        apply meshOn_of_gap_le
        · exact prefix_encloses v (fun i => le_of_lt (hp i)) 0
        · exact hk
        · rw [prefix_zero, gap_singleton]
          omega
    | succ t ih =>
        rw [prefix_step, Finset.sum_range_succ]
        apply translate_union_mesh _ _ _ _ _ ih (le_of_lt (hp t))
        have := next_weight_bound v hd t
        omega
  exact meshOn_gap_le _ _ _ _ (hmesh n)

/-- A missing interval contained in the actual integer hull has length at
most k-1. This is an ordinary interval bound, not a claim about another modulus. -/
theorem internal_run_bound (W : Finset ℤ) (lo hi : ℤ) (k : ℕ) (hm : MeshOn W lo hi k)
    (a : ℤ) (r : ℕ) (ha : lo ≤ a) (hr : a + (r : ℤ) - 1 ≤ hi)
    (hmiss : ∀ i : ℕ, i < r → a + (i : ℤ) ∉ W) : r ≤ k - 1 := by
  by_cases hzero : r = 0
  · omega
  obtain ⟨w, hw, haw, hwk⟩ := hm.2 a ha (by omega)
  by_contra hlarge
  have hi : (w - a).toNat < r := by omega
  have he : a + ((w - a).toNat : ℤ) = w := by omega
  exact hmiss (w - a).toNat hi (by rwa [he])

end Dyadic354.PrefixMesh
