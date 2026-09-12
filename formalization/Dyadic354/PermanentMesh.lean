import Dyadic354.InitialMesh

namespace Dyadic354.PermanentMesh

def prefixSums (v : ℕ → ℤ) (N : ℕ) : Finset ℤ := finiteSubsetSums v (Finset.range N)

theorem prefix_nonempty (v : ℕ → ℤ) (N : ℕ) : (prefixSums v N).Nonempty := by
  exact ⟨0, (mem_finiteSubsetSums v _ 0).mpr ⟨∅, Finset.empty_subset _, by simp⟩⟩

/-- Appending one new original index cannot collide with the old prefix. -/
theorem extend_step_subset (v : ℕ → ℤ) (N : ℕ) (W : Finset ℤ)
    (hW : W ⊆ prefixSums v N) : W ∪ Mesh.translate W (v N) ⊆ prefixSums v (N + 1) := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨s, hs, he⟩ := (mem_finiteSubsetSums _ _ _).mp (hW hz)
    exact (mem_finiteSubsetSums _ _ _).mpr
      ⟨s, hs.trans (Finset.range_mono (Nat.le_succ N)), he⟩
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨s, hs, he⟩ := (mem_finiteSubsetSums _ _ _).mp (hW hw)
    have hNs : N ∉ s := fun hi => (Finset.mem_range.mp (hs hi)).false
    refine (mem_finiteSubsetSums _ _ _).mpr ⟨insert N s, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        exact Finset.mem_range.mpr (Nat.lt_succ_self N)
      · exact Finset.range_mono (Nat.le_succ N) (hs hi)
    · rw [Finset.sum_insert hNs, ← he, add_comm]

theorem extend_subset_prefix (v : ℕ → ℤ) (N : ℕ) (W : Finset ℤ)
    (hW : W ⊆ prefixSums v N) :
    ∀ t, Mesh.extend W (fun i => v (N + i)) t ⊆ prefixSums v (N + t) := by
  intro t
  induction t with
  | zero => simpa only [Mesh.extend, Nat.add_zero] using hW
  | succ t ih =>
      exact extend_step_subset v (N + t) _ ih

theorem gap_of_subset {m : ℕ} [NeZero m] (X Y : Finset (ZMod m))
    (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : X ⊆ Y) :
    CyclicGaps.gap Y hY ≤ CyclicGaps.gap X hX := by
  apply (CyclicGaps.gap_le_iff Y hY _).mpr
  intro a
  obtain ⟨i, hi, hm⟩ := CyclicGaps.gap_spec X hX a
  exact ⟨i, hi, hXY hm⟩

/-- Permanent projection to the full later prefix, with a fresh arbitrary
modulus at each t. Its premise is a proved initial mesh plus ordinary bounds
on the explicitly indexed future weights. -/
theorem permanent_projection (v : ℕ → ℤ) (N : ℕ) (W : Finset ℤ)
    (hW : W.Nonempty) (k : ℕ) (hsub : W ⊆ prefixSums v N)
    (hg : Mesh.gap W ≤ k) (hs : v N ≤ Mesh.span W hW)
    (hpos : ∀ t, 0 < v (N + t))
    (hdbl : ∀ t, v (N + (t + 1)) ≤ 2 * v (N + t)) :
    ∀ t m : ℕ, ∀ _hm : NeZero m, (m : ℤ) ≤ v (N + t) →
      CyclicGaps.gap (Mesh.residues (prefixSums v (N + t)) m)
        (Mesh.residues_nonempty _ (prefix_nonempty v (N + t)) m) ≤ k - 1 := by
  intro t m hm hmv
  have hprop := Mesh.propagate_iterate W hW (fun i => v (N + i)) k hpos hdbl
    (by simpa only [Nat.add_zero] using hs) hg t
  let V := Mesh.extend W (fun i => v (N + i)) t
  have hV : V.Nonempty := Mesh.extend_nonempty W hW _ t
  have hproj := Mesh.projection_gap V hV k m (le_trans hmv hprop.2.1) hprop.1
  have hinc : Mesh.residues V m ⊆ Mesh.residues (prefixSums v (N + t)) m := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨z, extend_subset_prefix v N W hsub t hz, rfl⟩
  exact le_trans (gap_of_subset _ _ (Mesh.residues_nonempty V hV m)
    (Mesh.residues_nonempty _ (prefix_nonempty v (N + t)) m) hinc) hproj

/-- Algebraic local descent, including the actual certificate-to-prefix link.
The future enumeration must satisfy the explicit doubling bound. This is
not automatic for the frozen a,b,a,b interleave: the manuscript orders the
future pairs b,a. The floor-sequence and arrival-event adapter is proved in
FloorDescent.lean. Existence of qualifying blocks and completeness remain
separate obligations; this generic theorem asserts neither. -/
theorem certificate_permanent_descent (n ℓ d : ℕ) [NeZero d] (v : ℕ → ℤ)
    (first second third : Certificate.Digits) (p q : ℤ)
    (hfirst : first ≠ (false, false)) (hq : 0 < q) (hqp : q < p) (hpq : p < 2 * q)
    (hcop : IsCoprime p q) (hpos : ∀ i : Fin (2 * n), 0 ≤ v i.val)
    (hS : (∑ i : Fin (2 * n), v i.val) < (d : ℤ) * (p + q))
    (hK : InitialMesh.threshold p q ≤ (2 : ℤ) ^ ℓ)
    (ha : ∀ i : Fin ℓ, v (2 * n + 2 * i.val) = (d : ℤ) * p * 2 ^ i.val)
    (hb : ∀ i : Fin ℓ, v (2 * n + 2 * i.val + 1) = (d : ℤ) * q * 2 ^ i.val)
    (hsix : ∀ i : Fin 6, v (2 * n + 2 * ℓ + i.val) =
      Certificate.weights first second third d (2 ^ ℓ) p q i)
    (hnext : v (2 * (n + ℓ + 3)) ≤ 8 * (d : ℤ) * (2 : ℤ) ^ ℓ * q + 15)
    (hfuture : ∀ t, 0 < v (2 * (n + ℓ + 3) + t))
    (hdbl : ∀ t, v (2 * (n + ℓ + 3) + (t + 1)) ≤
      2 * v (2 * (n + ℓ + 3) + t)) :
    let old : Fin (2 * n) → ℤ := fun i => v i.val
    ∀ t m : ℕ, ∀ _hm : NeZero m, (m : ℤ) ≤ v (2 * (n + ℓ + 3) + t) →
      CyclicGaps.gap (Mesh.residues (prefixSums v (2 * (n + ℓ + 3) + t)) m)
        (Mesh.residues_nonempty _ (prefix_nonempty v _) m) ≤
      CyclicGaps.gap (NodeRepresentations.oldResidues n d old)
        (NodeRepresentations.oldResidues_nonempty n d old) - 1 := by
  obtain ⟨W, hW, hsub, hgap, hspan⟩ := InitialMesh.prefix_initial_mesh n ℓ d v
    first second third p q hfirst hq hqp hpq hcop hpos hS hK ha hb hsix
  dsimp only
  intro t m hm hmv
  have h := permanent_projection v (2 * (n + ℓ + 3)) W hW _ hsub hgap
    (le_trans hnext (le_of_lt hspan)) hfuture hdbl t m hm hmv
  have heq : max 1 (CyclicGaps.gap (NodeRepresentations.oldResidues n d (fun i => v i.val))
      (NodeRepresentations.oldResidues_nonempty n d (fun i => v i.val))) - 1 =
      CyclicGaps.gap (NodeRepresentations.oldResidues n d (fun i => v i.val))
        (NodeRepresentations.oldResidues_nonempty n d (fun i => v i.val)) - 1 := by omega
  rwa [heq] at h

end Dyadic354.PermanentMesh
