import Dyadic354.Normalization

namespace Dyadic354.SetBridge

open FloorSequence PairReindex

theorem normalized_sorted_strictMono (α β : ℝ)
    (hb : 0 < term β 0) (hba : term β 0 < term α 0) (hab : term α 0 < 2 * term β 0) :
    StrictMono (sortedTail α β 0) := by
  have he (i : ℕ) : sortedTail α β 0 (2 * i) = term β i := by
    simpa using sortedTail_even α β 0 i
  have ho (i : ℕ) : sortedTail α β 0 (2 * i + 1) = term α i := by
    simpa using sortedTail_odd α β 0 i
  apply strictMono_nat_of_lt_succ
  intro j
  rcases index_cases j with hj | hj
  · rw [hj, he, ho]
    exact (normalized_bounds α β hb hba hab _).2.1
  · have hs : j + 1 = 2 * (j / 2 + 1) := by omega
    conv_lhs => rw [hj, ho]
    conv_rhs => rw [hs, he]
    exact (normalized_bounds α β hb hba hab _).2.2.trans_le (next_bounds β _).1

/-- Distinct retained indices have distinct values, despite possible
coincidences in the original, unnormalized sequences. -/
theorem normalized_injective (α β : ℝ)
    (hb : 0 < term β 0) (hba : term β 0 < term α 0) (hab : term α 0 < 2 * term β 0) :
    Function.Injective (interleave α β 2) := by
  intro i j hij
  have hs : sortedTail α β 0 (swapAfter 0 i) = sortedTail α β 0 (swapAfter 0 j) := by
    simpa only [sortedTail, swapAfter_involutive 0 i, swapAfter_involutive 0 j] using hij
  exact swapAfter_injective 0 ((normalized_sorted_strictMono α β hb hba hab).injective hs)

theorem normalized_lower_bound (α β : ℝ)
    (hb : 0 < term β 0) (hba : term β 0 < term α 0) (hab : term α 0 < 2 * term β 0)
    (i : ℕ) : term β 0 ≤ interleave α β 2 i := by
  have hs := (normalized_sorted_strictMono α β hb hba hab).monotone (Nat.zero_le (swapAfter 0 i))
  have hz : sortedTail α β 0 0 = term β 0 := by simpa using sortedTail_even α β 0 0
  rw [hz] at hs
  change term β 0 ≤ interleave α β 2 (swapAfter 0 (swapAfter 0 i)) at hs
  rwa [swapAfter_involutive 0 i] at hs

theorem indexed_to_set (w : ℕ → ℤ) (hinj : Function.Injective w) (h : IndexedComplete w) :
    SetComplete (Set.range w) := by
  classical
  filter_upwards [h] with z hz
  obtain ⟨s, hs⟩ := hz
  refine ⟨s.image w, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i, rfl⟩
  · rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
    exact hs

theorem setComplete_mono (A B : Set ℤ) (hAB : A ⊆ B) (hA : SetComplete A) : SetComplete B := by
  filter_upwards [hA] with z hz
  obtain ⟨s, hs, hsum⟩ := hz
  exact ⟨s, hs.trans hAB, hsum⟩

theorem set_to_indexed (w : ℕ → ℤ) (h : SetComplete (Set.range w)) : IndexedComplete w := by
  classical
  filter_upwards [h] with z hz
  obtain ⟨s, hs, hsum⟩ := hz
  let f := Function.invFun w
  have hf (x : ℤ) (hx : x ∈ s) : w (f x) = x := by
    obtain ⟨i, rfl⟩ := hs hx
    exact Function.apply_invFun_apply
  refine ⟨s.image f, ?_⟩
  rw [Finset.sum_image (fun i hi j hj hij => by simpa only [hf i hi, hf j hj] using congrArg w hij)]
  rw [hsum]
  exact Finset.sum_congr rfl (fun x hx => (hf x hx).symm)

/-- Each shifted term is an actual term of the original pair. -/
theorem shifted_range_subset (α β : ℝ) (u v : ℕ) :
    Set.range (interleave ((2 : ℝ) ^ u * α) ((2 : ℝ) ^ v * β) 2) ⊆
      Set.range (interleave α β 2) := by
  rintro z ⟨i, rfl⟩
  rcases index_cases i with hi | hi
  · rw [hi, interleave_even]
    change term ((2 : ℝ) ^ u * α) (i / 2) ∈ Set.range (interleave α β 2)
    rw [Normalization.term_shift]
    exact ⟨2 * (i / 2 + u), interleave_even α β 2 _⟩
  · rw [hi, interleave_odd]
    change term ((2 : ℝ) ^ v * β) (i / 2) ∈ Set.range (interleave α β 2)
    rw [Normalization.term_shift]
    exact ⟨2 * (i / 2 + v) + 1, interleave_odd α β 2 _⟩

end Dyadic354.SetBridge
