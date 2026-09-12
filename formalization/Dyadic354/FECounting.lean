import Dyadic354.PrefixBounds
import Mathlib.Data.Int.Interval

namespace Dyadic354.FECounting

open FloorSequence PrefixBounds

/-- These are distinct integer values, not numbers of index subsets. -/
noncomputable abbrev values (α β : ℝ) (n : ℕ) : Finset ℤ :=
  PermanentMesh.prefixSums (interleave α β 2) (2 * n)

noncomputable def digitSum (α β : ℝ) (n : ℕ) : ℤ := correction α n + correction β n
noncomputable def padding (α β : ℝ) (n : ℕ) : ℤ := period α β n - total α β n
noncomputable def deficit (α β : ℝ) (n : ℕ) : ℤ := period α β n - (values α β n).card
noncomputable def growth (α β : ℝ) (n : ℕ) : ℤ :=
  (values α β (n + 1)).card - 2 * (values α β n).card

noncomputable def holes (α β : ℝ) (n : ℕ) : Finset ℤ :=
  Finset.Ico 0 (period α β n) \ values α β n

noncomputable def newValues (α β : ℝ) (n : ℕ) : Finset ℤ :=
  values α β (n + 1) \ (values α β n ∪ Mesh.translate (values α β n) (period α β n))

theorem translate_translate (W : Finset ℤ) (a b : ℤ) :
    Mesh.translate (Mesh.translate W a) b = Mesh.translate W (a + b) := by
  simp only [Mesh.translate, Finset.image_image]
  congr 1
  funext w
  simp only [Function.comp_apply, add_assoc]

/-- The four translates are a union of finite sets, so overlaps are deduplicated. -/
theorem values_step (α β : ℝ) (n : ℕ) :
    values α β (n + 1) =
      values α β n ∪ Mesh.translate (values α β n) (term α n) ∪
      Mesh.translate (values α β n) (term β n) ∪
      Mesh.translate (values α β n) (period α β n) := by
  change PermanentMesh.prefixSums (interleave α β 2) (2 * (n + 1)) = _
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, PrefixMesh.prefix_step,
    PrefixMesh.prefix_step, interleave_even, interleave_odd]
  change (values α β n ∪ Mesh.translate (values α β n) (term α n)) ∪
    Mesh.translate (values α β n ∪ Mesh.translate (values α β n) (term α n)) (term β n) = _
  have hu (W V : Finset ℤ) (c : ℤ) :
      Mesh.translate (W ∪ V) c = Mesh.translate W c ∪ Mesh.translate V c := Finset.image_union _ _
  rw [hu, translate_translate]
  simp only [Finset.union_assoc, period]

theorem period_step (α β : ℝ) (n : ℕ) :
    period α β (n + 1) = 2 * period α β n + digitSum α β n := by
  dsimp [period, digitSum, correction]
  ring

theorem digitSum_bounds (α β : ℝ) (n : ℕ) : 0 ≤ digitSum α β n ∧ digitSum α β n ≤ 2 := by
  have ha := correction_bounds α n
  have hb := correction_bounds β n
  dsimp [digitSum]
  omega

theorem digitSum_event_iff (α β : ℝ) (n : ℕ) :
    digitSum α β n ≠ 0 ↔ ExactBlock.IsEvent α β (n + 1) := by
  unfold digitSum
  rw [← digit_bit, ← digit_bit]
  simp only [ExactBlock.IsEvent, Nat.add_sub_cancel, ExactBlock.digits]
  cases bit α n <;> cases bit β n <;> simp [Certificate.digit]

theorem total_lt_period (α β : ℝ) (ha0 : 0 < term α 0) (hb0 : 0 < term β 0) (n : ℕ) :
    total α β n < period α β n := paired_prefix_lt α β ha0 hb0 n

theorem basic_copies_subset (α β : ℝ) (n : ℕ) :
    values α β n ∪ Mesh.translate (values α β n) (period α β n) ⊆ values α β (n + 1) := by
  rw [values_step]
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
  · exact Finset.mem_union_right _ hz

theorem basic_copies_disjoint (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : Disjoint (values α β n) (Mesh.translate (values α β n) (period α β n)) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hz'
  have hbound := (actual_prefix_encloses α β hb0 hba0 hab0 n).2.2
  have hzb := hbound z hz
  have hwb := hbound w hw
  have hlt := total_lt_period α β (lt_trans hb0 hba0) hb0 n
  omega

theorem card_translate (W : Finset ℤ) (c : ℤ) : (Mesh.translate W c).card = W.card :=
  Finset.card_image_of_injective W (fun _ _ h => add_right_cancel h)

/-- G is proved nonnegative from two disjoint basic copies inside the next
actual prefix; it is not defined by truncated subtraction. -/
theorem growth_nonneg (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : 0 ≤ growth α β n := by
  have hc := Finset.card_le_card (basic_copies_subset α β n)
  rw [Finset.card_union_of_disjoint (basic_copies_disjoint α β hb0 hba0 hab0 n), card_translate] at hc
  dsimp [growth]
  omega

theorem values_subset_period (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : values α β n ⊆ Finset.Ico (0 : ℤ) (period α β n) := by
  have hbound := (actual_prefix_encloses α β hb0 hba0 hab0 n).2.2
  have hlt := total_lt_period α β (lt_trans hb0 hba0) hb0 n
  intro z hz
  exact Finset.mem_Ico.mpr ⟨(hbound z hz).1, lt_of_le_of_lt (hbound z hz).2 hlt⟩

theorem deficit_nonneg (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : 0 ≤ deficit α β n := by
  have hc := Finset.card_le_card (values_subset_period α β hb0 hba0 hab0 n)
  rw [Int.card_Ico, sub_zero] at hc
  have hp := normalized_bounds α β hb0 hba0 hab0 n
  dsimp [period] at hc
  dsimp [deficit, period]
  omega

theorem padding_step (α β : ℝ) (n : ℕ) :
    padding α β (n + 1) = padding α β n + digitSum α β n := by
  unfold padding
  rw [period_step, total_step]
  ring

theorem padding_identity (α β : ℝ) (n : ℕ) :
    padding α β n = term α 0 + term β 0 + ∑ i ∈ Finset.range n, digitSum α β i := by
  induction n with
  | zero => simp [padding, period, total_eq]
  | succ n ih => rw [padding_step, Finset.sum_range_succ, ih]; ring

theorem padding_bound (α β : ℝ)
    (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : 0 < padding α β n ∧ padding α β n < 3 * term β 0 + 2 * n := by
  have hlo : 0 ≤ ∑ i ∈ Finset.range n, digitSum α β i :=
    Finset.sum_nonneg (fun i _ => (digitSum_bounds α β i).1)
  have hhi : (∑ i ∈ Finset.range n, digitSum α β i) ≤ 2 * (n : ℤ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, (2 : ℤ) := Finset.sum_le_sum (fun i _ => (digitSum_bounds α β i).2)
      _ = _ := by simp; ring
  rw [padding_identity]
  constructor <;> omega

/-- Manuscript (8.1): the exact deficit recurrence for distinct sum values. -/
theorem deficit_step (α β : ℝ) (n : ℕ) :
    deficit α β (n + 1) = 2 * deficit α β n + digitSum α β n - growth α β n := by
  unfold deficit growth
  rw [period_step]
  ring

theorem deficit_zero (α β : ℝ) : deficit α β 0 = term α 0 + term β 0 - 1 := by
  simp [deficit, values, PrefixMesh.prefix_zero, period]

/-- Q counts the actual missing integer positions in one period. -/
theorem deficit_eq_holes (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : deficit α β n = ((holes α β n).card : ℤ) := by
  have hc := Finset.card_sdiff_add_card_eq_card (values_subset_period α β hb0 hba0 hab0 n)
  rw [Int.card_Ico, sub_zero] at hc
  have hp := normalized_bounds α β hb0 hba0 hab0 n
  change (holes α β n).card + (values α β n).card = (period α β n).toNat at hc
  dsimp [deficit, period] at *
  omega

/-- G counts exactly the new sum values outside both disjoint basic copies. -/
theorem growth_eq_newValues (α β : ℝ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (n : ℕ) : growth α β n = ((newValues α β n).card : ℤ) := by
  have hc := Finset.card_sdiff_add_card_eq_card (basic_copies_subset α β n)
  change (newValues α β n).card +
    (values α β n ∪ Mesh.translate (values α β n) (period α β n)).card = (values α β (n + 1)).card at hc
  rw [Finset.card_union_of_disjoint (basic_copies_disjoint α β hb0 hba0 hab0 n), card_translate] at hc
  dsimp [growth]
  omega

end Dyadic354.FECounting
