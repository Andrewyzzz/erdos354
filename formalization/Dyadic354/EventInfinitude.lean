import Dyadic354.EventGaps
import Mathlib.Algebra.Order.Archimedean.Basic

namespace Dyadic354.EventInfinitude

open FloorSequence ExactBlock

/-- An eventually zero binary floor-error sequence forces a dyadic rational
parameter. The proof uses the floor inequalities and unbounded powers of two. -/
theorem zero_tail_dyadic (α : ℝ) (N : ℕ)
    (hz : ∀ i, bit α (N + i) = false) :
    α = (term α N : ℝ) / (2 : ℝ) ^ N := by
  have hg (i : ℕ) : term α (N + i) = (2 : ℤ) ^ i * term α N :=
    exact_block α N (i + 1) (fun j _ => hz j) i (by omega)
  have hlo : (term α N : ℝ) ≤ (2 : ℝ) ^ N * α :=
    Int.floor_le ((2 : ℝ) ^ N * α)
  have heq : (2 : ℝ) ^ N * α = (term α N : ℝ) := by
    by_contra hne
    have hδ : 0 < (2 : ℝ) ^ N * α - (term α N : ℝ) := by
      exact sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hne))
    obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt
      (1 / ((2 : ℝ) ^ N * α - (term α N : ℝ))) (by norm_num : (1 : ℝ) < 2)
    have hi' := (div_lt_iff₀ hδ).mp hi
    have hu := Int.lt_floor_add_one ((2 : ℝ) ^ (N + i) * α)
    change (2 : ℝ) ^ (N + i) * α < (term α (N + i) : ℝ) + 1 at hu
    rw [hg, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, pow_add] at hu
    nlinarith
  apply (eq_div_iff (pow_ne_zero N (by norm_num : (2 : ℝ) ≠ 0))).mpr
  simpa only [mul_comm] using heq

theorem no_events_tail_digits (α β : ℝ) (N : ℕ)
    (hno : ∀ t, N < t → ¬ IsEvent α β t) :
    ∀ i, digits α β (N + i) = (false, false) := by
  intro i
  by_contra h
  apply hno (N + i + 1) (by omega)
  exact ⟨by omega, by simpa only [Nat.add_sub_cancel] using h⟩

/-- This implication does not require normalized floor endpoints or positivity. -/
theorem events_unbounded (α β : ℝ) (hirr : Irrational (α / β)) :
    ∀ N, ∃ t, N < t ∧ IsEvent α β t := by
  intro N
  by_contra h
  push_neg at h
  have hz := no_events_tail_digits α β N h
  have ha := zero_tail_dyadic α N (fun i => congrArg Prod.fst (hz i))
  have hb := zero_tail_dyadic β N (fun i => congrArg Prod.snd (hz i))
  apply hirr.ne_rational (term α N) (term β N)
  conv_lhs => rw [ha, hb]
  exact div_div_div_cancel_right₀ (pow_ne_zero N (by norm_num : (2 : ℝ) ≠ 0)) _ _

/-- The least actual arrival event strictly after a given layer. -/
noncomputable def nextEvent (α β : ℝ) (hirr : Irrational (α / β)) (n : ℕ) : ℕ := by
  classical
  exact Nat.find (events_unbounded α β hirr n)

theorem nextEvent_spec (α β : ℝ) (hirr : Irrational (α / β)) (n : ℕ) :
    n < nextEvent α β hirr n ∧ IsEvent α β (nextEvent α β hirr n) := by
  classical
  exact Nat.find_spec (events_unbounded α β hirr n)

theorem no_event_before_next (α β : ℝ) (hirr : Irrational (α / β)) (n t : ℕ)
    (hnt : n < t) (ht : t < nextEvent α β hirr n) : ¬ IsEvent α β t := by
  classical
  intro he
  have hle : nextEvent α β hirr n ≤ t := Nat.find_min' (events_unbounded α β hirr n) ⟨hnt, he⟩
  omega

/-- The bound now applies to a defined successor which exists from irrationality,
not to a caller-supplied or hypothetical event. -/
theorem incomplete_nextEvent_factor_four (α β : ℝ) (hirr : Irrational (α / β))
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hinc : ¬ IndexedComplete (interleave α β 2)) :
    ∃ N, ∀ n, N ≤ n → nextEvent α β hirr n ≤ 4 * n := by
  obtain ⟨N, hN⟩ := EventGaps.incomplete_event_factor_four α β hb0 hba0 hab0 hinc
  refine ⟨N, ?_⟩
  intro n hn
  exact hN n hn _ (nextEvent_spec α β hirr n).1
    (fun t hnt ht => no_event_before_next α β hirr n t hnt ht)
    (nextEvent_spec α β hirr n).2

end Dyadic354.EventInfinitude
