import Dyadic354.BGCapacity
import Dyadic354.BGWindows
import Dyadic354.BGGeometric
import Dyadic354.BGReturns

namespace Dyadic354.BG

open Filter FloorSequence FECounting FERecurrence FER BGExactLayers BGReturns BGWindowBounds

theorem support_nonempty_of_event (α β : ℝ) (a b t : ℕ)
    (hat : a < t) (htb : t ≤ b) (he : ExactBlock.IsEvent α β t) :
    (support α β a (b - a)).Nonempty := by
  classical
  refine ⟨t - 1 - a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
  apply (digitSum_event_iff α β (a + (t - 1 - a))).mpr
  convert he using 1
  omega

/-- BG: a uniform multiplicative bound on event gaps contradicts the
long sparse windows furnished by FE-R and DB, hence gives completeness.
All windows and return costs are proved, not supplied as assumptions. -/
theorem bounded_event_windows_complete (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hirr : Irrational (α / β)) (R : ℕ) (hR : 1 ≤ R)
    (hwindows : ∃ N : ℕ, ∀ n, N ≤ n → ∃ t, n < t ∧ t ≤ R * n ∧ ExactBlock.IsEvent α β t) :
    IndexedComplete (interleave α β 2) := by
  classical
  by_contra hi
  obtain ⟨N, hN⟩ := hwindows
  obtain ⟨L, hL, hlog⟩ := BGCapacity.logarithmic_bound (FE.decayRate β) (seedConstant α β)
    (2 * (DBScale.scaleConstant β : ℝ) + 7) (FE.rate_positive β hb0)
    (seed_constant_positive α β hb0 hba0) (by positivity)
  obtain ⟨k, hk, hcap⟩ := BGCapacity.eventual_capacity L hL (2 * R + 1) N (by omega)
  obtain ⟨Ncap, hNcap⟩ := eventually_atTop.mp hcap
  obtain ⟨ε, hε, hreturn⟩ := return_cost_unbounded α β hirr k
  obtain ⟨T, r, hT, hheight, hr1, hr2, hnear, hdelta, hexp⟩ :=
    BGWindows.arbitrarily_large_windows α β hb0 hba0 hab0 hi hirr ε hε
      (max Ncap (max 1 ⌈Real.exp 1⌉₊))
  have hTcap : Ncap ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTexp : ⌈Real.exp 1⌉₊ ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hexpT : Real.exp 1 ≤ (T : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hTexp)
  have hlogT : 1 ≤ Real.log (T : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hexpT
    rwa [Real.log_exp] at hh
  have hKT : (eventCount α β T : ℝ) ≤ L * Real.log (T : ℝ) :=
    hlog T (eventCount α β T) (by exact_mod_cast hT1) hlogT (by linarith)
  let H := height r
  let E := H * (eventCount α β T + 1)
  let x := max (N + 1) (E + 1)
  have hx : 0 < x := by dsimp [x]; omega
  have hEx : E ≤ x := by dsimp [x]; omega
  have hcount : ((Finset.range (T + 1)).filter (fun i => delta α β r.num r.den i ≠ 0)).card ≤ E := by
    have hh := nonexact_count α β r.num r.den T H hdelta
    dsimp [E]
    nlinarith
  have hcapacity : 2 * (2 * R + 1) ^ (eventCount α β T / k + 1) * x ≤ T :=
    hNcap T hTcap H (eventCount α β T) hheight hKT
  have hratio : (r.num : ℝ) / ((r.den : ℤ) : ℝ) = (r : ℝ) := by
    simp only [Int.cast_natCast, Rat.cast_def]
  have hcost (a b : ℕ) (hxa : x ≤ a) (hbT : b ≤ T)
      (hda : delta α β r.num r.den a = 0) (hdb : delta α β r.num r.den b = 0)
      (hab : R * a < b) : eventCount α β a + k ≤ eventCount α β b := by
    have hNa : N ≤ a := by dsimp [x] at hxa; omega
    have hab' : a ≤ b := by nlinarith
    obtain ⟨t, hat, ht, he⟩ := hN a hNa
    have hs := support_nonempty_of_event α β a b t hat (by omega) he
    have hh := hreturn r.num r.den (by exact_mod_cast r.pos)
      (by rwa [hratio]) (by rwa [hratio]) (by rwa [hratio]) a (b - a) hda
      (by rwa [Nat.add_sub_of_le hab']) hs
    rw [Nat.add_sub_of_le hab'] at hh
    omega
  have htotal := BGGeometric.cost_bound (delta α β r.num r.den) (eventCount α β)
    (eventCount_mono α β) T E x R (eventCount α β T / k + 1) k hR hx hEx hcount hcapacity hcost
  have hrem := Nat.mod_lt (eventCount α β T) hk
  have hdiv := Nat.mod_add_div (eventCount α β T) k
  nlinarith

/-- The normalized actual sequence is complete. Incompleteness itself
would give the factor-four event bound, so BG needs no extra FE/DB/BG
or event-gap hypothesis in this conclusion. -/
theorem normalized_complete (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hirr : Irrational (α / β)) : IndexedComplete (interleave α β 2) := by
  by_contra hi
  obtain ⟨N, hN⟩ := EventInfinitude.incomplete_nextEvent_factor_four α β hirr hb0 hba0 hab0 hi
  apply hi
  apply bounded_event_windows_complete α β hb0 hba0 hab0 hirr 4 (by norm_num)
  refine ⟨N, ?_⟩
  intro n hn
  exact ⟨EventInfinitude.nextEvent α β hirr n, (EventInfinitude.nextEvent_spec α β hirr n).1,
    hN n hn, (EventInfinitude.nextEvent_spec α β hirr n).2⟩

end Dyadic354.BG
