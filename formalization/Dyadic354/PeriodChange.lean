import Dyadic354.FEShift

namespace Dyadic354.PeriodChange

open PeriodicWord CyclicBoundary

theorem basic_word (S : Finset ℤ) (L : ℕ) (hS : S ⊆ Finset.Ico 0 (L : ℤ))
    (x : ℤ) (hx : x ∈ Finset.Ico 0 (2 * (L : ℤ))) :
    word S L x = missing (S ∪ Mesh.translate S L) x := by
  have hxb := Finset.mem_Ico.mp hx
  by_cases hxl : x < (L : ℤ)
  · rw [word_on_period S L hS x (Finset.mem_Ico.mpr ⟨hxb.1, hxl⟩)]
    have ht : x ∉ Mesh.translate S L := by
      intro ht
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp ht
      have hyb := Finset.mem_Ico.mp (hS hy)
      omega
    simp only [missing, Finset.mem_union, ht, or_false]
  · rw [← word_sub_period S L x, word_on_period S L hS (x - L) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]
    have hs : x ∉ S := by intro hs; have hb := Finset.mem_Ico.mp (hS hs); omega
    have ht : x ∈ Mesh.translate S L ↔ x - L ∈ S := by
      constructor
      · intro h
        obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
        have he' : x - L = y := by omega
        rwa [he']
      · intro h
        exact Finset.mem_image.mpr ⟨x - L, h, by omega⟩
    simp only [missing, Finset.mem_union, hs, false_or, ht]

theorem missing_difference (S T : Finset ℤ) (hST : S ⊆ T) (x : ℤ) :
    |missing T x - missing S x| = if x ∈ T \ S then 1 else 0 := by
  by_cases hs : x ∈ S
  · have ht := hST hs
    simp [missing, hs, ht]
  · by_cases ht : x ∈ T <;> simp [missing, hs, ht]

theorem sum_indicator_le_card (D A : Finset ℤ) :
    (∑ x ∈ D, if x ∈ A then (1 : ℤ) else 0) ≤ A.card := by
  have hc : (D.filter (fun x => x ∈ A)).card ≤ A.card :=
    Finset.card_le_card (fun _ hx => (Finset.mem_filter.mp hx).2)
  have he : (∑ x ∈ D, if x ∈ A then (1 : ℤ) else 0) = ((D.filter (fun x => x ∈ A)).card : ℤ) := by
    rw [← Finset.sum_filter]
    simp
  rw [he]
  exact_mod_cast hc

/-- Generic changing-period comparison. The last L'-2L positions are paid
for explicitly; the old word is extended using L, not reinterpreted modulo L'. -/
theorem changing_period_bound (S T : Finset ℤ) (L L' : ℕ)
    (hS : S ⊆ Finset.Ico 0 (L : ℤ)) (hT : T ⊆ Finset.Ico 0 (L' : ℤ))
    (hbasic : S ∪ Mesh.translate S L ⊆ T) (hL : 2 * L ≤ L') :
    (∑ x ∈ Finset.Ico 0 (L' : ℤ), |word T L' x - word S L x|) ≤
      ((T \ (S ∪ Mesh.translate S L)).card : ℤ) + ((L' : ℤ) - 2 * L) := by
  let A := T \ (S ∪ Mesh.translate S L)
  have hp (x : ℤ) (hx : x ∈ Finset.Ico 0 (L' : ℤ)) :
      |word T L' x - word S L x| ≤
        (if x ∈ A then (1 : ℤ) else 0) + (if 2 * (L : ℤ) ≤ x then 1 else 0) := by
    by_cases hxold : x < 2 * (L : ℤ)
    · have hx0 := (Finset.mem_Ico.mp hx).1
      rw [basic_word S L hS x (Finset.mem_Ico.mpr ⟨hx0, hxold⟩), word_on_period T L' hT x hx]
      change |missing T x - missing (S ∪ Mesh.translate S L) x| ≤ _
      rw [missing_difference _ _ hbasic]
      simp only [if_neg (by omega : ¬ 2 * (L : ℤ) ≤ x), add_zero]
      exact le_refl _
    · have hf := word_bounds T L' x
      have hg := word_bounds S L x
      have hi : (0 : ℤ) ≤ if x ∈ A then 1 else 0 := by split_ifs <;> omega
      rw [if_pos (by omega : 2 * (L : ℤ) ≤ x)]
      rw [abs_le]
      constructor <;> omega
  have htail : (∑ x ∈ Finset.Ico 0 (L' : ℤ), if 2 * (L : ℤ) ≤ x then (1 : ℤ) else 0) =
      (L' : ℤ) - 2 * L := by
    have hf : (Finset.Ico (0 : ℤ) (L' : ℤ)).filter (fun x => 2 * (L : ℤ) ≤ x) =
        Finset.Ico (2 * (L : ℤ)) (L' : ℤ) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    have he : (∑ x ∈ Finset.Ico 0 (L' : ℤ), if 2 * (L : ℤ) ≤ x then (1 : ℤ) else 0) =
        (((Finset.Ico (0 : ℤ) (L' : ℤ)).filter (fun x => 2 * (L : ℤ) ≤ x)).card : ℤ) := by simp
    rw [he, hf, Int.card_Ico]
    omega
  calc
    _ ≤ ∑ x ∈ Finset.Ico 0 (L' : ℤ),
        ((if x ∈ A then (1 : ℤ) else 0) + (if 2 * (L : ℤ) ≤ x then 1 else 0)) := Finset.sum_le_sum hp
    _ = (∑ x ∈ Finset.Ico 0 (L' : ℤ), if x ∈ A then (1 : ℤ) else 0) + ((L' : ℤ) - 2 * L) := by
      rw [Finset.sum_add_distrib, htail]
    _ ≤ _ := by
      have h := sum_indicator_le_card (Finset.Ico 0 (L' : ℤ)) A
      change _ ≤ (A.card : ℤ) + _
      omega

/-- Manuscript (8.4) for the actual dyadic floor-sequence prefixes. -/
theorem actual_changing_period_bound (α β : ℝ)
    (hb0 : 0 < FloorSequence.term β 0)
    (hba0 : FloorSequence.term β 0 < FloorSequence.term α 0)
    (hab0 : FloorSequence.term α 0 < 2 * FloorSequence.term β 0) (n : ℕ) :
    (∑ x ∈ Finset.Ico 0 (PrefixBounds.period α β (n + 1)),
      |FEShift.missingWord α β (n + 1) x - FEShift.missingWord α β n x|) ≤
      FECounting.growth α β n + FECounting.digitSum α β n := by
  have hL := FEShift.length_cast α β hb0 hba0 hab0 n
  have hL' := FEShift.length_cast α β hb0 hba0 hab0 (n + 1)
  have hS := FECounting.values_subset_period α β hb0 hba0 hab0 n
  have hT := FECounting.values_subset_period α β hb0 hba0 hab0 (n + 1)
  have hb := FECounting.basic_copies_subset α β n
  have hstep := FECounting.period_step α β n
  have hw := (FECounting.digitSum_bounds α β n).1
  rw [← hL] at hS hb
  rw [← hL'] at hT
  have h := changing_period_bound _ _ _ _ hS hT hb (by omega)
  rw [hL', hL] at h
  rw [FECounting.growth_eq_newValues α β hb0 hba0 hab0 n]
  change _ ≤ ((FECounting.values α β (n + 1) \
    (FECounting.values α β n ∪ Mesh.translate (FECounting.values α β n) (PrefixBounds.period α β n))).card : ℤ) + _
  change _ ≤ _ at h
  have hd : PrefixBounds.period α β (n + 1) - 2 * PrefixBounds.period α β n = FECounting.digitSum α β n := by omega
  rw [hd] at h
  exact h

end Dyadic354.PeriodChange
