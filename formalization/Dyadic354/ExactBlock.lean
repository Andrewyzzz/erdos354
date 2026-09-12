import Dyadic354.FloorSequence

namespace Dyadic354.ExactBlock

open FloorSequence

noncomputable def digits (α β : ℝ) (i : ℕ) : Certificate.Digits := (bit α i, bit β i)

/-- Events are indexed by the arrival layer, not the departing digit index. -/
def IsEvent (α β : ℝ) (t : ℕ) : Prop := 0 < t ∧ digits α β (t - 1) ≠ (false, false)

theorem no_events_zero_digits (α β : ℝ) (n m : ℕ)
    (hno : ∀ t, n < t → t < m → ¬ IsEvent α β t) :
    ∀ i, i + 1 < m - n → digits α β (n + i) = (false, false) := by
  intro i hi
  by_contra h
  apply hno (n + i + 1) (by omega) (by omega)
  exact ⟨by omega, by simpa only [Nat.add_sub_cancel] using h⟩

theorem exact_block (α : ℝ) (n ℓ : ℕ)
    (hzero : ∀ i, i + 1 < ℓ → bit α (n + i) = false) :
    ∀ i, i < ℓ → term α (n + i) = (2 : ℤ) ^ i * term α n := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Nat.add_succ, recurrence, hzero i hi, Certificate.digit,
        ih (by omega), pow_succ]
      simp
      ring

/-- The nonzero arrival at n+ℓ follows ℓ exact weights but only ℓ-1
zero departures. This spells out the manuscript's off-by-one convention. -/
theorem after_exact_block (α : ℝ) (n ℓ : ℕ) (hℓ : 0 < ℓ)
    (hzero : ∀ i, i + 1 < ℓ → bit α (n + i) = false) :
    term α (n + ℓ) = (2 : ℤ) ^ ℓ * term α n +
      Certificate.digit (bit α (n + ℓ - 1)) := by
  have hr := recurrence α (n + (ℓ - 1))
  have hi : n + (ℓ - 1) + 1 = n + ℓ := by omega
  have hj : n + (ℓ - 1) = n + ℓ - 1 := by omega
  rw [hi, exact_block α n ℓ hzero (ℓ - 1) (by omega), hj] at hr
  have hp : (2 : ℤ) ^ ℓ = 2 * (2 : ℤ) ^ (ℓ - 1) := by
    conv_lhs => rw [show ℓ = (ℓ - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  rw [hp]
  nlinarith [hr]

theorem interleave_block (α β : ℝ) (n ℓ : ℕ) (d p q : ℤ)
    (ha : term α n = d * p) (hb : term β n = d * q)
    (hza : ∀ i, i + 1 < ℓ → bit α (n + i) = false)
    (hzb : ∀ i, i + 1 < ℓ → bit β (n + i) = false) :
    (∀ i : Fin ℓ, interleave α β 2 (2 * n + 2 * i.val) = d * p * 2 ^ i.val) ∧
    (∀ i : Fin ℓ, interleave α β 2 (2 * n + 2 * i.val + 1) = d * q * 2 ^ i.val) := by
  constructor
  · intro i
    rw [show 2 * n + 2 * i.val = 2 * (n + i.val) by omega, interleave_even]
    change term α (n + i.val) = _
    rw [exact_block α n ℓ hza i.val i.isLt, ha]
    ring
  · intro i
    rw [show 2 * n + 2 * i.val + 1 = 2 * (n + i.val) + 1 by omega, interleave_odd]
    change term β (n + i.val) = _
    rw [exact_block β n ℓ hzb i.val i.isLt, hb]
    ring

/-- Three actual pairs agree with the six certificate weights once their
first arrival is given; the next two digits are the actual floor digits. -/
theorem three_pairs (α β : ℝ) (r : ℕ) (d K p q : ℤ) (first : Certificate.Digits)
    (ha : term α r = d * K * p + Certificate.digit first.1)
    (hb : term β r = d * K * q + Certificate.digit first.2) :
    ∀ i : Fin 6, interleave α β 2 (2 * r + i.val) =
      Certificate.weights first (digits α β r) (digits α β (r + 1)) d K p q i := by
  have ha1 := recurrence α r
  have hb1 := recurrence β r
  have ha2 := recurrence α (r + 1)
  have hb2 := recurrence β (r + 1)
  intro i
  rw [Certificate.weights_explicit]
  fin_cases i
  · simpa only [Nat.add_zero, interleave_even] using ha
  · simpa only [interleave_odd] using hb
  ·
    rw [show 2 * r + 2 = 2 * (r + 1) by omega, interleave_even]
    change term α (r + 1) = _
    dsimp [digits]
    linarith
  ·
    rw [show 2 * r + 3 = 2 * (r + 1) + 1 by omega, interleave_odd]
    change term β (r + 1) = _
    dsimp [digits]
    linarith
  ·
    rw [show 2 * r + 4 = 2 * ((r + 1) + 1) by omega, interleave_even]
    change term α ((r + 1) + 1) = _
    dsimp [digits]
    linarith
  ·
    rw [show 2 * r + 5 = 2 * ((r + 1) + 1) + 1 by omega, interleave_odd]
    change term β ((r + 1) + 1) = _
    dsimp [digits]
    linarith

theorem six_after_exact_block (α β : ℝ) (n ℓ : ℕ) (d p q : ℤ) (hℓ : 0 < ℓ)
    (ha : term α n = d * p) (hb : term β n = d * q)
    (hza : ∀ i, i + 1 < ℓ → bit α (n + i) = false)
    (hzb : ∀ i, i + 1 < ℓ → bit β (n + i) = false) :
    ∀ i : Fin 6, interleave α β 2 (2 * n + 2 * ℓ + i.val) =
      Certificate.weights (digits α β (n + ℓ - 1)) (digits α β (n + ℓ))
        (digits α β (n + ℓ + 1)) d (2 ^ ℓ) p q i := by
  have hbasea := after_exact_block α n ℓ hℓ hza
  have hbaseb := after_exact_block β n ℓ hℓ hzb
  rw [ha] at hbasea
  rw [hb] at hbaseb
  have h := three_pairs α β (n + ℓ) d (2 ^ ℓ) p q (digits α β (n + ℓ - 1))
    (by dsimp [digits]; nlinarith [hbasea]) (by dsimp [digits]; nlinarith [hbaseb])
  intro i
  simpa only [Nat.mul_add, Nat.add_assoc] using h i

theorem next_small_weight_bound (α : ℝ) (n ℓ : ℕ) (d q : ℤ) (hℓ : 0 < ℓ)
    (hα : term α n = d * q) (hz : ∀ i, i + 1 < ℓ → bit α (n + i) = false) :
    term α (n + ℓ + 3) ≤ 8 * d * (2 : ℤ) ^ ℓ * q + 15 := by
  have hbase := after_exact_block α n ℓ hℓ hz
  rw [hα] at hbase
  have hd := correction_bounds α (n + ℓ - 1)
  rw [← digit_bit] at hd
  have h1 := next_bounds α (n + ℓ)
  have h2 := next_bounds α (n + ℓ + 1)
  have h3 := next_bounds α (n + ℓ + 2)
  nlinarith

end Dyadic354.ExactBlock
