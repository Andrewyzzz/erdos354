import Dyadic354.DBDigits

namespace Dyadic354.BGExactLayers

open FloorSequence FECounting FERecurrence
open scoped Classical

noncomputable def delta (α β : ℝ) (p q : ℤ) (i : ℕ) : ℤ := q * term α i - p * term β i

theorem delta_error_bound (α β : ℝ) (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (T i : ℕ) (hi : i ≤ T) (he : (2 : ℝ) ^ T * |(q : ℝ) * α - (p : ℝ) * β| < 1) :
    |delta α β p q i| < p + q + 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ T := pow_le_pow_right₀ (by norm_num) hi
  have he' : (2 : ℝ) ^ i * |(q : ℝ) * α - (p : ℝ) * β| < 1 :=
    (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)).trans_lt he
  have ha := DBDigits.residual_bounds α i
  have hb := DBDigits.residual_bounds β i
  have hid : (delta α β p q i : ℝ) = (2 : ℝ) ^ i * ((q : ℝ) * α - (p : ℝ) * β) -
      (q : ℝ) * DBDigits.residual α i + (p : ℝ) * DBDigits.residual β i := by
    unfold delta DBDigits.residual
    push_cast
    ring
  have heabs : |(2 : ℝ) ^ i * ((q : ℝ) * α - (p : ℝ) * β)| < 1 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ i)]
    exact he'
  have hbds := abs_lt.mp heabs
  have hout : |(delta α β p q i : ℝ)| < (p : ℝ) + q + 1 := by
    rw [hid, abs_lt]
    constructor <;> nlinarith
  exact_mod_cast hout

theorem quiet_scaling (α β : ℝ) (p q : ℤ) (i h : ℕ)
    (hz : ∀ j, j < h → digitSum α β (i + j) = 0) :
    delta α β p q (i + h) = (2 : ℤ) ^ h * delta α β p q i := by
  have hzero (j : ℕ) (hj : j + 1 < h + 1) :
      bit α (i + j) = false ∧ bit β (i + j) = false := by
    have hw := hz j (by omega)
    have ha := correction_bounds α (i + j)
    have hb := correction_bounds β (i + j)
    have hza : correction α (i + j) = 0 := by dsimp [digitSum] at hw; omega
    have hzb : correction β (i + j) = 0 := by dsimp [digitSum] at hw; omega
    simp [bit, hza, hzb]
  have ha := ExactBlock.exact_block α i (h + 1) (fun j hj => (hzero j hj).1) h (by omega)
  have hb := ExactBlock.exact_block β i (h + 1) (fun j hj => (hzero j hj).2) h (by omega)
  unfold delta
  rw [ha, hb]
  ring

theorem exact_of_quiet (α β : ℝ) (p q : ℤ) (i h : ℕ)
    (hz : ∀ j, j < h → digitSum α β (i + j) = 0)
    (hb : |delta α β p q (i + h)| < (2 : ℤ) ^ h) : delta α β p q i = 0 := by
  rw [quiet_scaling α β p q i h hz, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ h)] at hb
  have hd : |delta α β p q i| < 1 := by nlinarith [show (0 : ℤ) < 2 ^ h by positivity]
  have hh := abs_lt.mp hd
  omega

theorem nonexact_sees_event (α β : ℝ) (p q : ℤ) (T h i : ℕ)
    (hi : i + h ≤ T) (hb : ∀ j, j ≤ T → |delta α β p q j| < (2 : ℤ) ^ h)
    (hne : delta α β p q i ≠ 0) :
    ∃ j, i ≤ j ∧ j < i + h ∧ digitSum α β j ≠ 0 := by
  by_contra hh
  push_neg at hh
  apply hne
  exact exact_of_quiet α β p q i h (fun j hj => hh (i + j) (by omega) (by omega)) (hb (i + h) hi)

theorem window_count_bound (D : ℕ → ℤ) (events : Finset ℕ) (T h : ℕ)
    (hwindow : ∀ i, i + h ≤ T → D i ≠ 0 → ∃ j ∈ events, i ≤ j ∧ j < i + h) :
    ((Finset.range (T + 1)).filter (fun i => D i ≠ 0)).card ≤ h * events.card + h := by
  let S := (Finset.range (T + 1 - h)).filter (fun i => D i ≠ 0)
  have hchoose (i : S) : ∃ j ∈ events, i.val ≤ j ∧ j < i.val + h := by
    have hi := Finset.mem_filter.mp i.property
    exact hwindow i (by have hh := Finset.mem_range.mp hi.1; omega) hi.2
  choose j hj hlo hhi using hchoose
  let f (i : S) : ℕ × ℕ := (j i, j i - i.val)
  have hm (i : S) : f i ∈ events.product (Finset.range h) := by
    refine Finset.mem_product.mpr ⟨hj i, Finset.mem_range.mpr ?_⟩
    have hi := hhi i
    have hi' := hlo i
    dsimp [f]
    omega
  have hinj : Function.Injective f := by
    intro i k he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp [f] at h1 h2
    have hi := hlo i
    have hk := hlo k
    apply Subtype.ext
    omega
  have hc := Finset.card_le_card_of_injOn (s := Finset.univ) f (by intro i _; exact hm i)
    (by intro i _ k _ he; exact hinj he)
  simp only [Finset.card_univ, Fintype.card_coe, Finset.product_eq_sprod, Finset.card_product, Finset.card_range] at hc
  have hsub : (Finset.range (T + 1)).filter (fun i => D i ≠ 0) ⊆
      S ∪ Finset.Ico (T + 1 - h) (T + 1) := by
    intro i hi
    obtain ⟨hi, hd⟩ := Finset.mem_filter.mp hi
    by_cases hh : i < T + 1 - h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hd⟩)
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, Finset.mem_range.mp hi⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Nat.card_Ico] at hcard
  have ht : T + 1 - (T + 1 - h) ≤ h := by omega
  nlinarith

/-- Equation (11.2), including all last-h boundary layers. -/
theorem nonexact_count (α β : ℝ) (p q : ℤ) (T h : ℕ)
    (hb : ∀ j, j ≤ T → |delta α β p q j| < (2 : ℤ) ^ h) :
    ((Finset.range (T + 1)).filter (fun i => delta α β p q i ≠ 0)).card ≤
      h * eventCount α β T + h := by
  let events := (Finset.range T).filter (fun j => ExactBlock.IsEvent α β (j + 1))
  have hc : events.card = eventCount α β T := (eventCount_card α β T).symm
  rw [← hc]
  apply window_count_bound
  intro i hi hn
  obtain ⟨j, hij, hj, he⟩ := nonexact_sees_event α β p q T h i hi hb hn
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (digitSum_event_iff α β j).mp he⟩, hij, hj⟩

end Dyadic354.BGExactLayers
