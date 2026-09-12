import Dyadic354.Representations
import Dyadic354.CyclicGaps

namespace Dyadic354.NodeRepresentations

def margin (d p q S : ℤ) : ℤ := S + d * (q * (p - 1) + p + q) + 22

/-- Uniform bounds for the old coefficient left after choosing one offset
and one old-prefix representative. The constant 22 is checked, not hidden. -/
theorem residual_bounds (d K p q S L U l c f u z : ℤ)
    (hd : 0 < d) (hK : 0 ≤ K) (hpq : 0 ≤ p + q)
    (hf : 0 ≤ f ∧ f ≤ S) (hc : 0 ≤ c ∧ c ≤ 22)
    (hL : l ≤ L) (hU : U ≤ l + p + q)
    (hzlo : d * K * L + margin d p q S ≤ z)
    (hzhi : z ≤ d * K * U - margin d p q S)
    (heq : z = f + (d * u + (d * K * l + c))) :
    q * (p - 1) ≤ u ∧ u ≤ (p + q) * (K - 1) - q * (p - 1) := by
  have hdK : 0 ≤ d * K := mul_nonneg (le_of_lt hd) hK
  have hl := mul_le_mul_of_nonneg_left hL hdK
  have hu := mul_le_mul_of_nonneg_left hU hdK
  have hdpq := mul_nonneg (le_of_lt hd) hpq
  dsimp [margin] at hzlo hzhi
  constructor <;> nlinarith [hf.1, hf.2, hc.1, hc.2]

/-- Nonnegative original weights give the actual range of every old sum. -/
theorem old_sum_bounds (n : ℕ) (old : Fin (2 * n) → ℤ)
    (hpos : ∀ i, 0 ≤ old i) (f : ℤ) (hf : IsSubsetSum old f) :
    0 ≤ f ∧ f ≤ ∑ i, old i := by
  obtain ⟨s, rfl⟩ := hf
  exact ⟨Finset.sum_nonneg (fun i _ => hpos i),
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => hpos i)⟩

/-- One particular mask represents any admissible old residue in its
trimmed interval, using three explicitly disjoint groups of indices. -/
theorem mask_representation (n ℓ : ℕ) (old : Fin (2 * n) → ℤ)
    (first second third : Certificate.Digits) (d p q S L U z : ℤ) (mask tm : ℕ)
    (hd : 0 < d) (hq : 0 < q) (hqp : q < p) (hK : p ≤ (2 : ℤ) ^ ℓ)
    (hcop : IsCoprime p q)
    (hbounds : ∀ f, IsSubsetSum old f → 0 ≤ f ∧ f ≤ S)
    (hc : 0 ≤ Certificate.constant first second third mask tm ∧
      Certificate.constant first second third mask tm ≤ 22)
    (hL : (Certificate.coefficient mask tm).eval p q ≤ L)
    (hU : U ≤ (Certificate.coefficient mask tm).eval p q + p + q)
    (hzlo : d * (2 : ℤ) ^ ℓ * L + margin d p q S ≤ z)
    (hzhi : z ≤ d * (2 : ℤ) ^ ℓ * U - margin d p q S)
    (hres : ∃ f, IsSubsetSum old f ∧
      d ∣ z - Certificate.constant first second third mask tm - f) :
    IsSubsetSum (Representations.packedWeights n ℓ old first second third d p q) z := by
  obtain ⟨f, hf, v, hv⟩ := hres
  let u := v - (2 : ℤ) ^ ℓ * (Certificate.coefficient mask tm).eval p q
  have heq : z = f + (d * u + (d * (2 : ℤ) ^ ℓ *
      (Certificate.coefficient mask tm).eval p q +
      Certificate.constant first second third mask tm)) := by
    dsimp [u]
    nlinarith [hv]
  have hu := residual_bounds d (2 ^ ℓ) p q S L U
    ((Certificate.coefficient mask tm).eval p q)
    (Certificate.constant first second third mask tm) f u z hd (by positivity)
    (by omega) (hbounds f hf) hc hL hU hzlo hzhi heq
  rw [heq]
  exact Representations.prefix_block_offset n ℓ old first second third d p q f u mask tm
    hf hq hqp hK hcop hu.1 hu.2

/-- Full arithmetic meaning of a verified node: both old residue classes
are attained throughout its actual, margin-trimmed integer interval. -/
theorem node_representation (n ℓ : ℕ) (old : Fin (2 * n) → ℤ)
    (first second third : Certificate.Digits) (node : Certificate.Node)
    (d p q S z : ℤ) (hd : 0 < d) (hq : 0 < q) (hqp : q < p)
    (hK : p ≤ (2 : ℤ) ^ ℓ) (hcop : IsCoprime p q)
    (hbounds : ∀ f, IsSubsetSum old f → 0 ≤ f ∧ f ≤ S)
    (hn : Certificate.NodeMeaning first second node p q)
    (hzlo : d * (2 : ℤ) ^ ℓ * node.lo.eval p q + margin d p q S ≤ z)
    (hzhi : z ≤ d * (2 : ℤ) ^ ℓ * node.hi.eval p q - margin d p q S)
    (hres : ∃ f, IsSubsetSum old f ∧
      (d ∣ z - Certificate.constant first second third node.mask0 node.thirdMask - f ∨
       d ∣ z - (Certificate.constant first second third node.mask0 node.thirdMask + 1) - f)) :
    IsSubsetSum (Representations.packedWeights n ℓ old first second third d p q) z := by
  obtain ⟨_, _, _, hlo, hhi, _, hc⟩ := hn
  obtain ⟨c, hc0, hc22, hcfirst, hcsecond, _⟩ := hc third
  obtain ⟨f, hf, hr | hr⟩ := hres
  · apply mask_representation n ℓ old first second third d p q S
      (node.lo.eval p q) (node.hi.eval p q) z node.mask0 node.thirdMask
      hd hq hqp hK hcop hbounds
    · rw [hcfirst]; omega
    · rw [hlo]; exact le_max_left _ _
    · rw [hhi]; linarith [min_le_left ((Certificate.coefficient node.mask0 node.thirdMask).eval p q)
        ((Certificate.coefficient node.mask1 node.thirdMask).eval p q)]
    · exact hzlo
    · exact hzhi
    · exact ⟨f, hf, hr⟩
  · apply mask_representation n ℓ old first second third d p q S
      (node.lo.eval p q) (node.hi.eval p q) z node.mask1 node.thirdMask
      hd hq hqp hK hcop hbounds
    · rw [hcsecond]; omega
    · rw [hlo]; exact le_max_right _ _
    · rw [hhi]; linarith [min_le_right ((Certificate.coefficient node.mask0 node.thirdMask).eval p q)
        ((Certificate.coefficient node.mask1 node.thirdMask).eval p q)]
    · exact hzlo
    · exact hzhi
    · refine ⟨f, hf, ?_⟩
      simpa only [hcfirst, hcsecond] using hr

def oldResidues (n d : ℕ) (old : Fin (2 * n) → ℤ) : Finset (ZMod d) :=
  (finiteSubsetSums old Finset.univ).image (fun f : ℤ => (f : ZMod d))

theorem oldResidues_nonempty (n d : ℕ) (old : Fin (2 * n) → ℤ) :
    (oldResidues n d old).Nonempty := by
  refine ⟨0, Finset.mem_image.mpr ⟨0, ?_, by simp⟩⟩
  exact (mem_finiteSubsetSums old Finset.univ 0).mpr ⟨∅, Finset.empty_subset _, by simp⟩

theorem lift_oldResidues_iff (n d : ℕ) (old : Fin (2 * n) → ℤ) (z : ℤ) :
    z ∈ CyclicGaps.lift (oldResidues n d old) ↔
      ∃ f, IsSubsetSum old f ∧ (d : ℤ) ∣ z - f := by
  change (z : ZMod d) ∈ (finiteSubsetSums old Finset.univ).image _ ↔ _
  constructor
  · intro hz
    obtain ⟨f, hf, he⟩ := Finset.mem_image.mp hz
    obtain ⟨s, _, hs⟩ := (mem_finiteSubsetSums old Finset.univ f).mp hf
    exact ⟨f, ⟨s, hs⟩, (ZMod.intCast_eq_intCast_iff_dvd_sub f z d).mp he⟩
  · rintro ⟨f, ⟨s, hs⟩, he⟩
    exact Finset.mem_image.mpr ⟨f,
      (mem_finiteSubsetSums old Finset.univ f).mpr ⟨s, Finset.subset_univ _, hs⟩,
      (ZMod.intCast_eq_intCast_iff_dvd_sub f z d).mpr he⟩

/-- Every k-window wholly inside a verified node's trimmed interval contains
an actual legal subset sum. The window size follows from exact gap erosion. -/
theorem node_window (n ℓ d : ℕ) [NeZero d] (old : Fin (2 * n) → ℤ)
    (first second third : Certificate.Digits) (node : Certificate.Node)
    (p q S a : ℤ) (k : ℕ) (hq : 0 < q) (hqp : q < p)
    (hK : p ≤ (2 : ℤ) ^ ℓ) (hcop : IsCoprime p q)
    (hbounds : ∀ f, IsSubsetSum old f → 0 ≤ f ∧ f ≤ S)
    (hn : Certificate.NodeMeaning first second node p q)
    (hk : 0 < k)
    (hg : CyclicGaps.gap (oldResidues n d old) (oldResidues_nonempty n d old) ≤ k)
    (halo : (d : ℤ) * (2 : ℤ) ^ ℓ * node.lo.eval p q + margin d p q S ≤ a)
    (hahi : a + (k : ℤ) - 1 ≤ (d : ℤ) * (2 : ℤ) ^ ℓ * node.hi.eval p q - margin d p q S) :
    ∃ z, IsSubsetSum (Representations.packedWeights n ℓ old first second third d p q) z ∧
      a ≤ z ∧ z < a + (k : ℤ) := by
  let X := oldResidues n d old
  let c := Certificate.constant first second third node.mask0 node.thirdMask
  have hb := CyclicGaps.gap_spec (CyclicGaps.erode X)
    (CyclicGaps.erode_nonempty X (oldResidues_nonempty n d old))
  rw [CyclicGaps.erosion_exact X (oldResidues_nonempty n d old)] at hb
  obtain ⟨i, hi, him⟩ := (CyclicGaps.gapBound_mono hb (Nat.sub_le_sub_right hg 1)) (a - c)
  have hi' : (i : ℤ) < k := by omega
  refine ⟨a + i, ?_, by omega, by omega⟩
  apply node_representation n ℓ old first second third node d p q S (a + i)
    (by exact_mod_cast NeZero.pos d) hq hqp hK hcop hbounds hn (by omega) (by omega)
  rw [CyclicGaps.lift_erode] at him
  rcases him with him | him
  · obtain ⟨f, hf, hr⟩ := (lift_oldResidues_iff n d old (a - c + i)).mp him
    refine ⟨f, hf, Or.inl ?_⟩
    convert hr using 1
    dsimp [c]
    ring
  · obtain ⟨f, hf, hr⟩ := (lift_oldResidues_iff n d old (a - c + i - 1)).mp him
    refine ⟨f, hf, Or.inr ?_⟩
    convert hr using 1
    dsimp [c]
    ring

end Dyadic354.NodeRepresentations
