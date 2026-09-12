import Dyadic354.UnitMesh
import Dyadic354.BlockLength

namespace Dyadic354.LowGap

open FloorSequence FloorDescent

/-- Low old cyclic gap plus a qualifying block yields actual indexed
completeness, not just a full residue set in one modulus. -/
theorem long_block_complete (α β : ℝ) (n ℓ : ℕ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hℓ : 0 < ℓ)
    (hzero : ∀ i, i + 1 < ℓ → ExactBlock.digits α β (n + i) = (false, false))
    (hevent : ExactBlock.IsEvent α β (n + ℓ))
    (hK : InitialMesh.threshold (pCoord α β n) (qCoord α β n) ≤ (2 : ℤ) ^ ℓ)
    (hlow : gapAt α β n (normalized_bounds α β hb0 hba0 hab0 n).1 ≤ 1) :
    IndexedComplete (interleave α β 2) := by
  let r := n + ℓ + 3
  obtain ⟨W, hW, hsub, hgap, hspan⟩ := long_block_mesh α β n ℓ hb0 hba0 hab0
    hℓ hzero hevent hK
  have hsub' : W ⊆ PermanentMesh.prefixSums (PairReindex.sortedTail α β r) (2 * r) := by
    change W ⊆ PermanentMesh.prefixSums (fun j => interleave α β 2 (PairReindex.swapAfter r j)) (2 * r)
    rw [PairReindex.prefixSums_reindex]
    exact hsub
  have hnext : PairReindex.sortedTail α β r (2 * r) ≤ Mesh.span W hW := by
    have he := PairReindex.sortedTail_even α β r 0
    simp only [Nat.mul_zero, Nat.add_zero] at he
    rw [he]
    exact hspan
  have hcomplete := UnitMesh.unit_mesh_complete (PairReindex.sortedTail α β r) (2 * r)
    W hW hsub' (by omega) hnext
    (PairReindex.sortedTail_positive α β r hb0 hba0 hab0)
    (PairReindex.sortedTail_doubling α β r hb0 hba0 hab0)
  exact (PairReindex.indexedComplete_reindex_iff (interleave α β 2) r).mp hcomplete

theorem next_event_length_complete (α β : ℝ) (n m : ℕ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hnm : n < m) (hno : ∀ t, n < t → t < m → ¬ ExactBlock.IsEvent α β t)
    (hm : ExactBlock.IsEvent α β m) (hlen : 2 * n + BlockLength.growthConstant α ≤ m - n)
    (hlow : gapAt α β n (normalized_bounds α β hb0 hba0 hab0 n).1 ≤ 1) :
    IndexedComplete (interleave α β 2) := by
  have he : n + (m - n) = m := Nat.add_sub_of_le (le_of_lt hnm)
  exact long_block_complete α β n (m - n) hb0 hba0 hab0 (by omega)
    (ExactBlock.no_events_zero_digits α β n m hno) (by rwa [he])
    (BlockLength.threshold_of_length α β n (m - n) hb0 hba0 hab0 hlen) hlow

end Dyadic354.LowGap
