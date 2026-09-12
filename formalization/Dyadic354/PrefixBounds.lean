import Dyadic354.PrefixMesh
import Dyadic354.FloorDescent

namespace Dyadic354.PrefixBounds

open FloorSequence PermanentMesh

noncomputable def total (α β : ℝ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n), interleave α β 2 i

noncomputable def period (α β : ℝ) (n : ℕ) : ℤ := term α n + term β n

theorem total_eq (α β : ℝ) (n : ℕ) :
    total α β n = ∑ i ∈ Finset.range n, (term α i + term β i) :=
  paired_prefix_sum α β 2 n

theorem total_step (α β : ℝ) (n : ℕ) :
    total α β (n + 1) = total α β n + period α β n := by
  simp only [total_eq, Finset.sum_range_succ, period]

theorem actual_prefix_encloses (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : Mesh.Encloses (prefixSums (interleave α β 2) (2 * n)) 0 (total α β n) :=
  PrefixMesh.prefix_encloses _
    (fun i => le_of_lt (FloorDescent.interleave_positive α β hb0 hba0 hab0 i)) (2 * n)

theorem actual_prefix_span (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) :
    Mesh.span (prefixSums (interleave α β 2) (2 * n)) (prefix_nonempty _ _) = total α β n :=
  PrefixMesh.prefix_span _
    (fun i => le_of_lt (FloorDescent.interleave_positive α β hb0 hba0 hab0 i)) (2 * n)

theorem actual_prefix_gap (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : Mesh.gap (prefixSums (interleave α β 2) (2 * n)) ≤ (term β 0).toNat := by
  have hp : ∀ i, 0 < PairReindex.sortedTail α β 0 i := by
    simpa only [Nat.mul_zero, Nat.zero_add] using PairReindex.sortedTail_positive α β 0 hb0 hba0 hab0
  have hd : ∀ i, PairReindex.sortedTail α β 0 (i + 1) ≤ 2 * PairReindex.sortedTail α β 0 i := by
    simpa only [Nat.mul_zero, Nat.zero_add] using PairReindex.sortedTail_doubling α β 0 hb0 hba0 hab0
  have hg := PrefixMesh.prefix_gap_bound _ hp hd (2 * n)
  have hfirst : PairReindex.sortedTail α β 0 0 = term β 0 := by
    simpa only [Nat.mul_zero, Nat.zero_add] using PairReindex.sortedTail_even α β 0 0
  rw [hfirst] at hg
  change Mesh.gap (prefixSums (fun j => interleave α β 2 (PairReindex.swapAfter 0 j)) (2 * n)) ≤
    (term β 0).toNat at hg
  rwa [PairReindex.prefixSums_reindex] at hg

/-- The span needed for modular projection starts at layer two. An elementary
induction replaces the manuscript's explicit exponential lower bound. -/
theorem total_ge_first (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) (hn : 2 ≤ n) : term α n ≤ total α β n := by
  have haux : ∀ k, term α (k + 2) ≤ total α β (k + 2) := by
    intro k
    induction k with
    | zero =>
        have ha0 := next_bounds α 0
        have hb1 := next_bounds β 0
        have ha1 := next_bounds α 1
        norm_num only [Nat.reduceAdd] at ha0 hb1 ha1
        simp only [total_eq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        omega
    | succ k ih =>
        have ha := next_bounds α (k + 2)
        have hp := (normalized_bounds α β hb0 hba0 hab0 (k + 2)).1
        rw [show k + 1 + 2 = (k + 2) + 1 by omega, total_step]
        dsimp only [period]
        omega
  simpa only [Nat.sub_add_cancel hn] using haux (n - 2)

/-- Manuscript (1.1), for the actual gcd modulus and actual finite prefix,
with no uniform-gap assumption supplied by the caller. -/
theorem uniform_cyclic_gap (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) (hn : 2 ≤ n) :
    FloorDescent.gapAt α β n (normalized_bounds α β hb0 hba0 hab0 n).1 ≤ (term β 0).toNat - 1 := by
  have hnorm := normalized_bounds α β hb0 hba0 hab0 n
  letI : NeZero (FloorDescent.modulus α β n) :=
    ⟨ne_of_gt (FloorDescent.modulus_positive α β n hnorm.1)⟩
  have hspan : (FloorDescent.modulus α β n : ℤ) ≤
      Mesh.span (prefixSums (interleave α β 2) (2 * n)) (prefix_nonempty _ _) := by
    rw [actual_prefix_span α β hb0 hba0 hab0 n]
    exact le_trans (Int.gcd_le_right _ hnorm.1)
      (le_trans (le_of_lt hnorm.2.1) (total_ge_first α β hb0 hba0 hab0 n hn))
  exact Mesh.projection_gap _ (prefix_nonempty _ _) _ _ hspan
    (actual_prefix_gap α β hb0 hba0 hab0 n)

/-- The internal missing-run estimate used in Section 8, valid for every
prefix, separately from the cyclic gcd estimate which starts at layer two. -/
theorem internal_missing_run_bound (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) (a : ℤ) (r : ℕ) (ha : 0 ≤ a) (hr : a + (r : ℤ) - 1 ≤ total α β n)
    (hmiss : ∀ i : ℕ, i < r → a + (i : ℤ) ∉ prefixSums (interleave α β 2) (2 * n)) :
    r ≤ (term β 0).toNat - 1 := by
  have hk : 0 < (term β 0).toNat := by omega
  have hm := Mesh.meshOn_of_gap_le _ _ _ _ (actual_prefix_encloses α β hb0 hba0 hab0 n)
    hk (actual_prefix_gap α β hb0 hba0 hab0 n)
  exact PrefixMesh.internal_run_bound _ _ _ _ hm a r ha hr hmiss

end Dyadic354.PrefixBounds
