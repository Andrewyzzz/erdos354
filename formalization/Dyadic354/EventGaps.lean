import Dyadic354.LowGap

namespace Dyadic354.EventGaps

open FloorSequence FloorDescent

/-- Well-founded descent, allowing an arbitrary delay before each update
becomes permanent. No monotonicity between qualifying starts is assumed. -/
theorem eventually_not_of_eventual_descent (g : ℕ → ℕ) (Q : ℕ → Prop)
    (hd : ∀ n, Q n → ∃ B, ∀ t, B ≤ t → Q t → g t < g n) :
    ∃ N, ∀ n, N ≤ n → ¬ Q n := by
  classical
  by_contra hn
  push_neg at hn
  have impossible : ∀ k, ∀ n, g n = k → Q n → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro n he hQ
        obtain ⟨B, hB⟩ := hd n hQ
        obtain ⟨t, ht, htQ⟩ := hn B
        have hlt : g t < k := by rw [← he]; exact hB t ht htQ
        exact ih (g t) hlt t rfl htQ
  obtain ⟨n, _, hQ⟩ := hn 0
  exact impossible (g n) n rfl hQ

/-- A start layer need not itself be an event. Using this slightly more
general predicate includes, in particular, all manuscript qualifying gaps. -/
def QualifyingGap (α β : ℝ) (n m : ℕ) : Prop :=
  n < m ∧ (∀ t, n < t → t < m → ¬ ExactBlock.IsEvent α β t) ∧
    ExactBlock.IsEvent α β m ∧ 2 * n + BlockLength.growthConstant α ≤ m - n

theorem incomplete_eventually_no_qualifying (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hinc : ¬ IndexedComplete (interleave α β 2)) :
    ∃ N, ∀ n, N ≤ n → ¬ ∃ m, QualifyingGap α β n m := by
  apply eventually_not_of_eventual_descent
    (fun n => gapAt α β n (normalized_bounds α β hb0 hba0 hab0 n).1)
    (fun n => ∃ m, QualifyingGap α β n m)
  intro n hQ
  obtain ⟨m, hnm, hno, hm, hlen⟩ := hQ
  have hlarge : 1 < gapAt α β n (normalized_bounds α β hb0 hba0 hab0 n).1 := by
    by_contra hlow
    exact hinc (LowGap.next_event_length_complete α β n m hb0 hba0 hab0 hnm hno hm hlen (by omega))
  refine ⟨m + 3, ?_⟩
  intro t ht _hQt
  have hd := BlockLength.next_event_length_descent α β n m hb0 hba0 hab0 hnm hno hm hlen t ht
  omega

/-- Section 6 without an assumed uniform prefix-gap bound: natural-number
well-foundedness suffices to rule out unbounded qualifying starts. -/
theorem unbounded_qualifying_complete (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hQ : ∀ N, ∃ n m, N ≤ n ∧ QualifyingGap α β n m) :
    IndexedComplete (interleave α β 2) := by
  by_contra hinc
  obtain ⟨N, hN⟩ := incomplete_eventually_no_qualifying α β hb0 hba0 hab0 hinc
  obtain ⟨n, m, hn, hnm⟩ := hQ N
  exact hN n hn ⟨m, hnm⟩

theorem incomplete_event_step_bound (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hinc : ¬ IndexedComplete (interleave α β 2)) :
    ∃ N, ∀ n, N ≤ n → ∀ m, n < m →
      (∀ t, n < t → t < m → ¬ ExactBlock.IsEvent α β t) →
      ExactBlock.IsEvent α β m → m < 3 * n + BlockLength.growthConstant α := by
  obtain ⟨N, hN⟩ := incomplete_eventually_no_qualifying α β hb0 hba0 hab0 hinc
  refine ⟨N, ?_⟩
  intro n hn m hnm hno hm
  by_contra hge
  exact hN n hn ⟨m, hnm, hno, hm, by omega⟩

/-- The eventual factor-four bound needed by the later FE/DB/BG argument,
proved for actual successive arrival events, not arbitrary event placeholders. -/
theorem incomplete_event_factor_four (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hinc : ¬ IndexedComplete (interleave α β 2)) :
    ∃ N, ∀ n, N ≤ n → ∀ m, n < m →
      (∀ t, n < t → t < m → ¬ ExactBlock.IsEvent α β t) →
      ExactBlock.IsEvent α β m → m ≤ 4 * n := by
  obtain ⟨N, hN⟩ := incomplete_event_step_bound α β hb0 hba0 hab0 hinc
  refine ⟨max N (BlockLength.growthConstant α), ?_⟩
  intro n hn m hnm hno hm
  have h := hN n (by omega) m hnm hno hm
  omega

end Dyadic354.EventGaps
