import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Dyadic354.BGGeometric

open scoped Classical

theorem exact_in_interval (D : ℕ → ℤ) (T E a b : ℕ) (hab : a ≤ b) (hbT : b ≤ T)
    (hE : ((Finset.range (T + 1)).filter (fun i => D i ≠ 0)).card ≤ E)
    (hlength : E ≤ b - a) : ∃ z, a ≤ z ∧ z ≤ b ∧ D z = 0 := by
  by_contra hh
  push_neg at hh
  have hsub : Finset.Icc a b ⊆ (Finset.range (T + 1)).filter (fun i => D i ≠ 0) := by
    intro i hi
    obtain ⟨hai, hib⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hh i hai hib⟩
  have hc := (Finset.card_le_card hsub).trans hE
  rw [Nat.card_Icc] at hc
  omega

/-- Count disjoint exact returns in geometrically separated windows.
The two quantitative premises are later discharged by actual layer and
return-cost theorems. -/
theorem cost_bound (D : ℕ → ℤ) (K : ℕ → ℕ) (hmono : Monotone K)
    (T E x R r k : ℕ) (hR : 1 ≤ R) (hx : 0 < x) (hEx : E ≤ x)
    (hE : ((Finset.range (T + 1)).filter (fun i => D i ≠ 0)).card ≤ E)
    (hT : 2 * (2 * R + 1) ^ r * x ≤ T)
    (hcost : ∀ a b, x ≤ a → b ≤ T → D a = 0 → D b = 0 → R * a < b → K a + k ≤ K b) :
    r * k ≤ K T := by
  let B := 2 * R + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hpoint (i : ℕ) : ∃ z : ℕ, i ≤ r → B ^ i * x ≤ z ∧ z ≤ 2 * B ^ i * x ∧ D z = 0 := by
    by_cases hi : i ≤ r
    · have hpow : B ^ i ≤ B ^ r := Nat.pow_le_pow_right hB hi
      have htop : 2 * B ^ i * x ≤ T := by change 2 * B ^ r * x ≤ T at hT; nlinarith
      have hpow1 : 1 ≤ B ^ i := one_le_pow₀ hB
      have heq : 2 * B ^ i * x = B ^ i * x + B ^ i * x := by ring
      have he : E ≤ 2 * B ^ i * x - B ^ i * x := by rw [heq, Nat.add_sub_cancel_left]; nlinarith
      obtain ⟨z, hz⟩ := exact_in_interval D T E (B ^ i * x) (2 * B ^ i * x) (by nlinarith) htop hE he
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun hh => (hi hh).elim⟩
  choose z hz using hpoint
  have hbounds (i : ℕ) (hi : i ≤ r) : x ≤ z i ∧ z i ≤ T ∧ D (z i) = 0 := by
    have hh := hz i hi
    have hp := one_le_pow₀ (n := i) hB
    have hpow := Nat.pow_le_pow_right hB hi
    change 2 * B ^ r * x ≤ T at hT
    exact ⟨by nlinarith, by nlinarith, hh.2.2⟩
  have hstep (i : ℕ) (hi : i + 1 ≤ r) : K (z i) + k ≤ K (z (i + 1)) := by
    have hlo := hz i (by omega)
    have hhi := hz (i + 1) hi
    have hb0 := hbounds i (by omega)
    have hb1 := hbounds (i + 1) hi
    apply hcost _ _ hb0.1 hb1.2.1 hb0.2.2 hb1.2.2
    have hp : 0 < B ^ i * x := by positivity
    rw [pow_succ] at hhi
    have hnext : (2 * R + 1) * (B ^ i * x) ≤ z (i + 1) := by
      convert hhi.1 using 1
      dsimp only [B]
      ring
    have hprev := Nat.mul_le_mul_left R hlo.2.1
    nlinarith
  have hiter : ∀ i, i ≤ r → K (z 0) + i * k ≤ K (z i) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hh := hstep i hi
      have hh' := ih (by omega)
      nlinarith
  have h := hiter r le_rfl
  have hm := hmono (hbounds r le_rfl).2.1
  omega

end Dyadic354.BGGeometric
