import Dyadic354.DBCover

namespace Dyadic354.DB

open FloorSequence FECounting FERecurrence FER

theorem interval_complete (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) (a b : ℤ) (hab : a ≤ b) (hsub : Finset.Icc a b ⊆ values α β n)
    (hwidth : term β n ≤ b - a) : IndexedComplete (interleave α β 2) := by
  let W := Finset.Icc a b
  have hW : W.Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  have he : Mesh.Encloses W a b := by
    refine ⟨Finset.mem_Icc.mpr ⟨le_rfl, hab⟩, Finset.mem_Icc.mpr ⟨hab, le_rfl⟩, ?_⟩
    intro z hz
    exact Finset.mem_Icc.mp hz
  have hm : Mesh.MeshOn W a b 1 := by
    refine ⟨he, ?_⟩
    intro z hz hz'
    exact ⟨z, Finset.mem_Icc.mpr ⟨hz, hz'⟩, le_rfl, by norm_num⟩
  have hsub' : W ⊆ PermanentMesh.prefixSums (PairReindex.sortedTail α β n) (2 * n) := by
    change W ⊆ PermanentMesh.prefixSums (fun j => interleave α β 2 (PairReindex.swapAfter n j)) (2 * n)
    rw [PairReindex.prefixSums_reindex]
    exact hsub
  have hfirst : PairReindex.sortedTail α β n (2 * n) = term β n := by
    simpa using PairReindex.sortedTail_even α β n 0
  have hs : PairReindex.sortedTail α β n (2 * n) ≤ Mesh.span W hW := by
    rw [hfirst, Mesh.span_of_encloses W hW a b he]
    exact hwidth
  have h := UnitMesh.unit_mesh_complete (PairReindex.sortedTail α β n) (2 * n) W hW hsub'
    (Mesh.meshOn_gap_le W a b 1 hm) hs
    (PairReindex.sortedTail_positive α β n hb0 hba0 hab0)
    (PairReindex.sortedTail_doubling α β n hb0 hba0 hab0)
  exact (PairReindex.indexedComplete_reindex_iff (interleave α β 2) n).mp h

theorem incomplete_seed_lt_error (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hi : ¬ IndexedComplete (interleave α β 2))
    (n k : ℕ) (p q : ℤ) (hq : 2 ≤ q) (hK : 8 * q ≤ (2 : ℤ) ^ k)
    (hc : IsCoprime p q) (happrox : |α / β - (p : ℝ) / q| < 1 / (q : ℝ) ^ 2) :
    (seedWidth α β n : ℝ) < 3 * ((2 : ℝ) ^ n * β) / q + DBDigits.error α β n k := by
  by_contra hh
  have hh' := le_of_not_gt hh
  obtain ⟨a, b, _, hseed, hwidth⟩ := seed_interval_exists α β n
  have hw : 3 * ((2 : ℝ) ^ n * β) / q + DBDigits.error α β n k ≤ (b - a : ℤ) := by
    rw [hwidth]
    exact_mod_cast hh'
  obtain ⟨c, d, hcd, hsub, hspan⟩ := DBCover.propagated_interval α β hba0 hab0 n k p q hq hK hc happrox a b hseed hw
  exact hi (interval_complete α β hb0 hba0 hab0 (n + k) c d hcd hsub hspan.le)

theorem incomplete_seed_budget (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hi : ¬ IndexedComplete (interleave α β 2))
    (n k : ℕ) (p q : ℤ) (hq : 2 ≤ q) (hK : 8 * q ≤ (2 : ℤ) ^ k)
    (hc : IsCoprime p q) (happrox : |α / β - (p : ℝ) / q| < 1 / (q : ℝ) ^ 2)
    (hscale : (2 : ℝ) ^ n * β ≤ q) :
    seedWidth α β n ≤ 2 * (eventCount α β (n + k) - eventCount α β n) + 4 := by
  have hs := incomplete_seed_lt_error α β hb0 hba0 hab0 hi n k p q hq hK hc happrox
  have he := DBDigits.error_lt_budget α β n k
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hdelta : 3 * ((2 : ℝ) ^ n * β) / q ≤ 3 := by
    apply (div_le_iff₀ hqR).mpr
    linarith
  have hr : (seedWidth α β n : ℝ) < 2 * ((eventCount α β (n + k) : ℝ) - (eventCount α β n : ℝ)) + 5 := by
    linarith
  have hz : (seedWidth α β n : ℤ) < 2 * ((eventCount α β (n + k) : ℤ) - (eventCount α β n : ℤ)) + 5 := by exact_mod_cast hr
  have hmono := eventCount_mono α β (show n ≤ n + k by omega)
  omega

/-- The manuscript DB increment, at every depth and every sufficiently
large finite coefficient square meeting the rational-approximation scale. -/
theorem digit_propagation (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hi : ¬ IndexedComplete (interleave α β 2))
    (n k : ℕ) (hn : 1 ≤ n) (p q : ℤ) (hq : 2 ≤ q) (hK : 8 * q ≤ (2 : ℤ) ^ k)
    (hc : IsCoprime p q) (happrox : |α / β - (p : ℝ) / q| < 1 / (q : ℝ) ^ 2)
    (hscale : (2 : ℝ) ^ n * β ≤ q) :
    (eventCount α β n : ℝ) + seedConstant α β / 2 * Real.exp (FE.decayRate β * eventCount α β n) - 3 ≤
      (eventCount α β (n + k) : ℝ) := by
  have h := incomplete_seed_budget α β hb0 hba0 hab0 hi n k p q hq hK hc happrox hscale
  have hmono := eventCount_mono α β (show n ≤ n + k by omega)
  have hr : (seedWidth α β n : ℝ) ≤
      2 * ((eventCount α β (n + k) : ℝ) - (eventCount α β n : ℝ)) + 4 := by
    exact_mod_cast (show (seedWidth α β n : ℤ) ≤ 2 * ((eventCount α β (n + k) : ℤ) - (eventCount α β n : ℤ)) + 4 by omega)
  have hf := seed_exponential_bound α β hb0 hba0 hab0 n hn
  linarith

end Dyadic354.DB
