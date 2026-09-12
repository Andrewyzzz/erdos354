import Dyadic354.PeriodicWord

namespace Dyadic354.FEShift

open CyclicBoundary PeriodicWord FECounting FloorSequence PrefixBounds

/-- Each missing translated residue has an actual new integer representative
outside both basic copies. The source map is surjective, so no mask counts enter. -/
theorem exits_le_new_values (S T : Finset ℤ) (L : ℕ) [NeZero L] (a : ℤ)
    (htrans : Mesh.translate S a ⊆ T) :
    (exits (residues S L) (a : ZMod L)).card ≤
      (T \ (S ∪ Mesh.translate S L)).card := by
  apply Finset.card_le_card_of_surjOn (fun z : ℤ => ((z - a : ℤ) : ZMod L))
  intro r hr
  have hr' := (Finset.mem_filter.mp hr).2
  obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hr'.1
  refine ⟨x + a, Finset.mem_sdiff.mpr ⟨htrans (Finset.mem_image.mpr ⟨x, hx, rfl⟩), ?_⟩, ?_⟩
  · intro hbad
    apply hr'.2
    have hcast : ((x + a : ℤ) : ZMod L) = r + (a : ZMod L) := by rw [Int.cast_add, he]
    rw [← hcast]
    rcases Finset.mem_union.mp hbad with hbad | hbad
    · exact Finset.mem_image.mpr ⟨x + a, hbad, rfl⟩
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hbad
      refine Finset.mem_image.mpr ⟨y, hy, ?_⟩
      rw [← hyx]
      simp
  · simpa only [add_sub_cancel_right] using he

theorem variation_le_new_values (S T : Finset ℤ) (L : ℕ) [NeZero L] (a : ℤ)
    (htrans : Mesh.translate S a ⊆ T) :
    variation (missing (residues S L)) (a : ZMod L) ≤
      2 * ((T \ (S ∪ Mesh.translate S L)).card : ℤ) := by
  rw [variation_missing]
  have h := exits_le_new_values S T L a htrans
  omega

noncomputable def length (α β : ℝ) (n : ℕ) : ℕ := (period α β n).toNat
noncomputable def missingWord (α β : ℝ) (n : ℕ) (x : ℤ) : ℤ := word (values α β n) (length α β n) x
noncomputable def boundary (α β : ℝ) (n : ℕ) (t : ℤ) : ℤ :=
  ∑ x ∈ Finset.Ico 0 (period α β n), |missingWord α β n (x + t) - missingWord α β n x|

theorem length_cast (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : (length α β n : ℤ) = period α β n := by
  have h := normalized_bounds α β hb0 hba0 hab0 n
  dsimp [length, period]
  omega

theorem length_positive (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : 0 < length α β n := by
  have h := normalized_bounds α β hb0 hba0 hab0 n
  dsimp [length, period]
  omega

theorem boundary_eq_cyclic (α β : ℝ) (n : ℕ) [NeZero (length α β n)]
    (hL : (length α β n : ℤ) = period α β n) (t : ℤ) :
    boundary α β n t = variation (missing (residues (values α β n) (length α β n)))
      (t : ZMod (length α β n)) := by
  rw [variation_eq_sum, hL]
  rfl

/-- Manuscript (8.3), the shift by the actual a_n, with its actual growth G_n. -/
theorem boundary_a_le (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : boundary α β n (term α n) ≤ 2 * growth α β n := by
  letI : NeZero (length α β n) := ⟨ne_of_gt (length_positive α β hb0 hba0 hab0 n)⟩
  have hL := length_cast α β hb0 hba0 hab0 n
  rw [boundary_eq_cyclic α β n hL]
  have htrans : Mesh.translate (values α β n) (term α n) ⊆ values α β (n + 1) := by
    rw [values_step]
    intro z hz
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hz))
  have h := variation_le_new_values _ _ (length α β n) _ htrans
  rw [hL] at h
  rw [growth_eq_newValues α β hb0 hba0 hab0 n]
  exact h

theorem boundary_b_eq_a (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : boundary α β n (term β n) = boundary α β n (term α n) := by
  letI : NeZero (length α β n) := ⟨ne_of_gt (length_positive α β hb0 hba0 hab0 n)⟩
  have hL := length_cast α β hb0 hba0 hab0 n
  rw [boundary_eq_cyclic α β n hL, boundary_eq_cyclic α β n hL]
  have he : (term β n : ZMod (length α β n)) = -(term α n : ZMod (length α β n)) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← Int.cast_add]
    rw [add_comm (term β n) (term α n)]
    change (period α β n : ZMod (length α β n)) = 0
    rw [← hL]
    simp
  rw [he, variation_neg]

theorem boundary_double_a_le (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : boundary α β n (2 * term α n) ≤ 4 * growth α β n := by
  letI : NeZero (length α β n) := ⟨ne_of_gt (length_positive α β hb0 hba0 hab0 n)⟩
  have hL := length_cast α β hb0 hba0 hab0 n
  have h := variation_double (missing (residues (values α β n) (length α β n)))
    (term α n : ZMod (length α β n))
  have ha := boundary_a_le α β hb0 hba0 hab0 n
  rw [boundary_eq_cyclic α β n hL] at ha ⊢
  have he : ((2 * term α n : ℤ) : ZMod (length α β n)) =
      (term α n : ZMod (length α β n)) + (term α n : ZMod (length α β n)) := by push_cast; ring
  rw [he]
  omega

end Dyadic354.FEShift
