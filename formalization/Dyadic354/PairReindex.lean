import Dyadic354.FloorSequence
import Dyadic354.PermanentMesh

namespace Dyadic354.PairReindex

/-- Leave old indices fixed and interchange each later adjacent pair. -/
def swapAfter (r j : ℕ) : ℕ :=
  if j < 2 * r then j else if j % 2 = 0 then j + 1 else j - 1

theorem swapAfter_before (r j : ℕ) (hj : j < 2 * r) : swapAfter r j = j := by
  simp [swapAfter, hj]

theorem swapAfter_even (r i : ℕ) :
    swapAfter r (2 * i) = if i < r then 2 * i else 2 * i + 1 := by
  by_cases h : i < r
  · simp [swapAfter, h, show 2 * i < 2 * r by omega]
  · simp [swapAfter, h, show ¬2 * i < 2 * r by omega]

theorem swapAfter_odd (r i : ℕ) :
    swapAfter r (2 * i + 1) = if i < r then 2 * i + 1 else 2 * i := by
  by_cases h : i < r
  · simp [swapAfter, h, show 2 * i + 1 < 2 * r by omega]
  · simp [swapAfter, h, show ¬2 * i + 1 < 2 * r by omega]

theorem index_cases (j : ℕ) : j = 2 * (j / 2) ∨ j = 2 * (j / 2) + 1 := by omega

theorem swapAfter_involutive (r : ℕ) : Function.Involutive (swapAfter r) := by
  intro j
  rcases index_cases j with h | h
  · conv_lhs => rw [h]
    rw [swapAfter_even]
    split_ifs with hj
    · rw [swapAfter_even, if_pos hj, ← h]
    · rw [swapAfter_odd, if_neg hj, ← h]
  · conv_lhs => rw [h]
    rw [swapAfter_odd]
    split_ifs with hj
    · rw [swapAfter_odd, if_pos hj, ← h]
    · rw [swapAfter_even, if_neg hj, ← h]

theorem swapAfter_injective (r : ℕ) : Function.Injective (swapAfter r) :=
  (swapAfter_involutive r).injective

/-- Swapping pairs preserves every complete paired prefix, even across the cutoff. -/
theorem swapAfter_lt_iff (r j t : ℕ) : swapAfter r j < 2 * t ↔ j < 2 * t := by
  rcases index_cases j with h | h
  · conv_lhs => rw [h, swapAfter_even]
    split_ifs <;> omega
  · conv_lhs => rw [h, swapAfter_odd]
    split_ifs <;> omega

theorem prefixSums_reindex_subset (v : ℕ → ℤ) (r t : ℕ) :
    PermanentMesh.prefixSums (fun j => v (swapAfter r j)) (2 * t) ⊆
      PermanentMesh.prefixSums v (2 * t) := by
  intro z hz
  obtain ⟨s, hs, he⟩ := (mem_finiteSubsetSums _ _ _).mp hz
  refine (mem_finiteSubsetSums _ _ _).mpr ⟨s.image (swapAfter r), ?_, ?_⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr ((swapAfter_lt_iff r i t).mpr (Finset.mem_range.mp (hs hi)))
  · rw [Finset.sum_image (fun i _ j _ hij => swapAfter_injective r hij)]
    exact he

theorem prefixSums_reindex (v : ℕ → ℤ) (r t : ℕ) :
    PermanentMesh.prefixSums (fun j => v (swapAfter r j)) (2 * t) =
      PermanentMesh.prefixSums v (2 * t) := by
  apply Finset.Subset.antisymm (prefixSums_reindex_subset v r t)
  have h := prefixSums_reindex_subset (fun j => v (swapAfter r j)) r t
  have he : (fun j => v (swapAfter r (swapAfter r j))) = v := by
    funext j
    rw [swapAfter_involutive r j]
  rwa [he] at h

noncomputable def sortedTail (α β : ℝ) (r j : ℕ) : ℤ := interleave α β 2 (swapAfter r j)

theorem isSubsetSum_reindex_iff (v : ℕ → ℤ) (r : ℕ) (z : ℤ) :
    IsSubsetSum (fun j => v (swapAfter r j)) z ↔ IsSubsetSum v z := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.image (swapAfter r), ?_⟩
    rw [Finset.sum_image (fun i _ j _ hij => swapAfter_injective r hij)]
    exact hs
  · rintro ⟨s, hs⟩
    refine ⟨s.image (swapAfter r), ?_⟩
    rw [Finset.sum_image (fun i _ j _ hij => swapAfter_injective r hij)]
    have he (i : ℕ) : swapAfter r (swapAfter r i) = i := swapAfter_involutive r i
    simpa only [he] using hs

theorem indexedComplete_reindex_iff (v : ℕ → ℤ) (r : ℕ) :
    IndexedComplete (fun j => v (swapAfter r j)) ↔ IndexedComplete v := by
  simp only [IndexedComplete, isSubsetSum_reindex_iff]

theorem sortedTail_even (α β : ℝ) (r t : ℕ) :
    sortedTail α β r (2 * r + 2 * t) = FloorSequence.term β (r + t) := by
  unfold sortedTail
  rw [show 2 * r + 2 * t = 2 * (r + t) by omega, swapAfter_even,
    if_neg (by omega), FloorSequence.interleave_odd]

theorem sortedTail_odd (α β : ℝ) (r t : ℕ) :
    sortedTail α β r (2 * r + 2 * t + 1) = FloorSequence.term α (r + t) := by
  unfold sortedTail
  rw [show 2 * r + 2 * t + 1 = 2 * (r + t) + 1 by omega, swapAfter_odd,
    if_neg (by omega), FloorSequence.interleave_even]

theorem sortedTail_positive (α β : ℝ) (r : ℕ)
    (hb : 0 < FloorSequence.term β 0)
    (hba : FloorSequence.term β 0 < FloorSequence.term α 0)
    (hab : FloorSequence.term α 0 < 2 * FloorSequence.term β 0) :
    ∀ j, 0 < sortedTail α β r (2 * r + j) := by
  intro j
  have hn := FloorSequence.normalized_bounds α β hb hba hab (r + j / 2)
  rcases index_cases j with h | h
  · rw [h, sortedTail_even]
    exact hn.1
  · rw [h, ← Nat.add_assoc, sortedTail_odd]
    exact lt_trans hn.1 hn.2.1

theorem sortedTail_doubling (α β : ℝ) (r : ℕ)
    (hb : 0 < FloorSequence.term β 0)
    (hba : FloorSequence.term β 0 < FloorSequence.term α 0)
    (hab : FloorSequence.term α 0 < 2 * FloorSequence.term β 0) :
    ∀ j, sortedTail α β r (2 * r + (j + 1)) ≤ 2 * sortedTail α β r (2 * r + j) := by
  intro j
  have hn := FloorSequence.normalized_bounds α β hb hba hab (r + j / 2)
  rcases index_cases j with h | h
  · have hleft : 2 * r + (j + 1) = 2 * r + 2 * (j / 2) + 1 := by omega
    have hright : 2 * r + j = 2 * r + 2 * (j / 2) := by omega
    rw [hleft, hright, sortedTail_odd, sortedTail_even]
    exact le_of_lt hn.2.2
  · have hleft : 2 * r + (j + 1) = 2 * r + 2 * (j / 2 + 1) := by omega
    have hright : 2 * r + j = 2 * r + 2 * (j / 2) + 1 := by omega
    rw [hleft, hright, sortedTail_even, sortedTail_odd]
    have hnxt := FloorSequence.next_bounds β (r + j / 2)
    rw [Nat.add_assoc] at hnxt
    omega

end Dyadic354.PairReindex
