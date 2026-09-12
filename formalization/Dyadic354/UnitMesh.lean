import Dyadic354.PermanentMesh
import Dyadic354.Statements

namespace Dyadic354.UnitMesh

theorem mem_extend (W : Finset ℤ) (c : ℕ → ℤ) (w : ℤ) (hw : w ∈ W) :
    ∀ t, w ∈ Mesh.extend W c t := by
  intro t
  induction t with
  | zero => exact hw
  | succ t ih => exact Finset.mem_union_left _ ih

/-- Selecting every future index is a legal choice, so the right endpoint
can be bounded below without assuming an abstract unbounded mesh. -/
theorem add_sum_mem_extend (W : Finset ℤ) (c : ℕ → ℤ) (w : ℤ) (hw : w ∈ W) :
    ∀ t, w + (∑ i ∈ Finset.range t, c i) ∈ Mesh.extend W c t := by
  intro t
  induction t with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using hw
  | succ t ih =>
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨w + (∑ i ∈ Finset.range t, c i), ih, ?_⟩
      rw [Finset.sum_range_succ]
      ring

theorem positive_sum_ge_length (c : ℕ → ℤ) (hc : ∀ i, 0 < c i) (t : ℕ) :
    (t : ℤ) ≤ ∑ i ∈ Finset.range t, c i := by
  calc
    (t : ℤ) = ∑ _i ∈ Finset.range t, (1 : ℤ) := by simp
    _ ≤ ∑ i ∈ Finset.range t, c i := Finset.sum_le_sum (fun i _ => by have := hc i; omega)

/-- A genuine unit mesh inside a prefix produces a half-line of legal
finite-index representations. The cutoff is the original mesh's minimum. -/
theorem unit_mesh_half_line (v : ℕ → ℤ) (N : ℕ) (W : Finset ℤ) (hW : W.Nonempty)
    (hsub : W ⊆ PermanentMesh.prefixSums v N) (hg : Mesh.gap W ≤ 1)
    (hs : v N ≤ Mesh.span W hW) (hpos : ∀ t, 0 < v (N + t))
    (hdbl : ∀ t, v (N + (t + 1)) ≤ 2 * v (N + t)) :
    ∀ z : ℤ, W.min' hW ≤ z → IsSubsetSum v z := by
  intro z hz
  let c := fun i => v (N + i)
  let t := (z - W.max' hW).toNat
  let V := Mesh.extend W c t
  have hV : V.Nonempty := Mesh.extend_nonempty W hW c t
  have hprop := Mesh.propagate_iterate W hW c 1 hpos hdbl
    (by simpa only [Nat.add_zero] using hs) hg t
  have hleft := V.min'_le (W.min' hW) (mem_extend W c _ (W.min'_mem hW) t)
  have hright := V.le_max' (W.max' hW + ∑ i ∈ Finset.range t, c i)
    (add_sum_mem_extend W c _ (W.max'_mem hW) t)
  have hsum := positive_sum_ge_length c hpos t
  have ht : z ≤ W.max' hW + (t : ℤ) := by dsimp [t]; omega
  have hmesh := Mesh.meshOn_of_gap_le V (V.min' hV) (V.max' hV) 1
    (Mesh.encloses_min_max V hV) (by decide) hprop.1
  obtain ⟨w, hw, hzw, hwz⟩ := hmesh.2 z (by omega) (by omega)
  have heq : w = z := by norm_num at hwz; omega
  have hzV : z ∈ V := heq ▸ hw
  have hzP := PermanentMesh.extend_subset_prefix v N W hsub t hzV
  obtain ⟨s, _, he⟩ := (mem_finiteSubsetSums _ _ _).mp hzP
  exact ⟨s, he⟩

theorem unit_mesh_complete (v : ℕ → ℤ) (N : ℕ) (W : Finset ℤ) (hW : W.Nonempty)
    (hsub : W ⊆ PermanentMesh.prefixSums v N) (hg : Mesh.gap W ≤ 1)
    (hs : v N ≤ Mesh.span W hW) (hpos : ∀ t, 0 < v (N + t))
    (hdbl : ∀ t, v (N + (t + 1)) ≤ 2 * v (N + t)) : IndexedComplete v := by
  apply (indexedComplete_iff v).mpr
  exact ⟨W.min' hW, unit_mesh_half_line v N W hW hsub hg hs hpos hdbl⟩

end Dyadic354.UnitMesh
