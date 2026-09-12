import Dyadic354.IntervalSums
import Dyadic354.PeriodChange

namespace Dyadic354.EventBoundary

open CyclicBoundary

def lift {L : ℕ} (f : ZMod L → ℤ) (x : ℤ) : ℤ := f (x : ZMod L)

theorem segment_variation_le (L : ℕ) [NeZero L] (f : ZMod L → ℤ) (a b t : ℤ)
    (hlen : b - a ≤ L) :
    (∑ x ∈ Finset.Ico a b, |lift f (x + t) - lift f x|) ≤ variation f (t : ZMod L) := by
  have h := IntervalSums.interval_le_period L (fun y => |f (y + (t : ZMod L)) - f y|)
    (fun _ => abs_nonneg _) a b hlen
  simpa only [lift, Int.cast_add] using h

/-- Compare a shift on a segment whose two copies both lie in the new
period. The total changing-period error is charged at most twice. -/
theorem compare_segment (L' : ℕ) [NeZero L'] (f : ℤ → ℤ) (g : ZMod L' → ℤ)
    (a b t C : ℤ) (ha : 0 ≤ a) (hb : b ≤ L') (hat : 0 ≤ a + t) (hbt : b + t ≤ L')
    (hd : (∑ x ∈ Finset.Ico 0 (L' : ℤ), |f x - lift g x|) ≤ C) :
    (∑ x ∈ Finset.Ico a b, |f (x + t) - f x|) ≤ variation g (t : ZMod L') + 2 * C := by
  have h := IntervalSums.replace_variation f (lift g) (Finset.Ico a b) t
  have hg := segment_variation_le L' g a b t (by omega)
  have he0 := IntervalSums.mono (fun x => |f x - lift g x|) (fun _ => abs_nonneg _) a b 0 L' ha hb
  have het := IntervalSums.mono (fun x => |f x - lift g x|) (fun _ => abs_nonneg _)
    (a + t) (b + t) 0 L' hat hbt
  have hshift := Finset.sum_Ico_add' (fun x => |f x - lift g x|) a b t
  dsimp only at he0 het hshift
  omega

theorem add_shift_cancel (L : ℕ) [NeZero L] (f : ZMod L → ℤ) (a b s t : ℤ)
    (hlen : b - a ≤ L) :
    (∑ x ∈ Finset.Ico a b, |lift f (x + s + t) - lift f (x + s)|) ≤
      (∑ x ∈ Finset.Ico a b, |lift f (x + (s + t)) - lift f x|) + variation f (s : ZMod L) := by
  have hp : (∑ x ∈ Finset.Ico a b, |lift f (x + s + t) - lift f (x + s)|) ≤
      (∑ x ∈ Finset.Ico a b, |lift f (x + (s + t)) - lift f x|) +
      (∑ x ∈ Finset.Ico a b, |lift f (x + s) - lift f x|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    rw [add_assoc]
    have h := abs_sub_le (lift f (x + (s + t))) (lift f x) (lift f (x + s))
    rwa [abs_sub_comm (lift f x) (lift f (x + s))] at h
  have h := segment_variation_le L f a b s hlen
  omega

/-- The u=1 case of the nonzero-event unit boundary estimate. -/
theorem first_digit_one (L L' : ℕ) [NeZero L] [NeZero L']
    (f : ZMod L → ℤ) (g : ZMod L' → ℤ) (a b v G G' : ℤ)
    (hba : b < a) (hab : a < 2 * b)
    (hL : (L : ℤ) = a + b) (hL' : (L' : ℤ) = 2 * (a + b) + 1 + v) (hv : 0 ≤ v)
    (haold : variation f (a : ZMod L) ≤ 2 * G)
    (hbold : variation f (b : ZMod L) ≤ 2 * G)
    (hanew : variation g ((2 * a + 1 : ℤ) : ZMod L') ≤ 2 * G')
    (hd : (∑ x ∈ Finset.Ico 0 (L' : ℤ), |lift f x - lift g x|) ≤ G + 1 + v) :
    variation f 1 ≤ 16 * G + 4 * G' + 4 * (1 + v) := by
  let τ := fun x : ZMod L => |f (x + 1) - f x|
  have hcomp := compare_segment L' (lift f) g 0 (2 * b) (2 * a + 1) (G + 1 + v)
    (by omega) (by omega) (by omega) (by omega) hd
  have hdouble := variation_double f (a : ZMod L)
  have hcast : ((2 * a : ℤ) : ZMod L) = (a : ZMod L) + (a : ZMod L) := by push_cast; ring
  have hdouble' : variation f ((2 * a : ℤ) : ZMod L) ≤ 4 * G := by rw [hcast]; omega
  have hcancel := add_shift_cancel L f 0 (2 * b) (2 * a) 1 (by omega)
  have hlocal : (∑ x ∈ Finset.Ico 0 (2 * b), τ ((x + 2 * a : ℤ) : ZMod L)) ≤ 2 * G' + 6 * G + 2 * (1 + v) := by
    have he (x : ℤ) : τ ((x + 2 * a : ℤ) : ZMod L) = |lift f (x + 2 * a + 1) - lift f (x + 2 * a)| := by
      simp only [τ, lift, Int.cast_add, Int.cast_one]
    simp only [he]
    omega
  have hemod : ((2 * a : ℤ) : ZMod L) = (((L : ℤ) - 2 * b : ℤ) : ZMod L) := by
    have he : 2 * a = ((L : ℤ) - 2 * b) + L := by omega
    rw [he]
    simp
  have harc : (∑ x ∈ Finset.Ico ((L : ℤ) - 2 * b) L, τ (x : ZMod L)) ≤ 2 * G' + 6 * G + 2 * (1 + v) := by
    have he := Finset.sum_Ico_add' (fun x : ℤ => τ (x : ZMod L)) 0 (2 * b) ((L : ℤ) - 2 * b)
    have hright : 2 * b + ((L : ℤ) - 2 * b) = L := by omega
    simp only [zero_add, hright] at he
    have hm (x : ℤ) : τ ((x + 2 * a : ℤ) : ZMod L) = τ ((x + ((L : ℤ) - 2 * b) : ℤ) : ZMod L) := by
      simp only [Int.cast_add, hemod]
    simp only [hm] at hlocal
    rw [he] at hlocal
    exact hlocal
  have hcover := IntervalSums.two_arcs_cover L τ (fun _ => abs_nonneg _) b (by omega) (by omega)
  have hvarτ := variation_boundary_le f 1 (b : ZMod L)
  have harcvar := segment_variation_le L τ ((L : ℤ) - 2 * b) L b (by omega)
  have hshift : (∑ x ∈ Finset.Ico ((L : ℤ) - 2 * b) L, τ ((x + b : ℤ) : ZMod L)) ≤
      (∑ x ∈ Finset.Ico ((L : ℤ) - 2 * b) L, τ (x : ZMod L)) + variation τ (b : ZMod L) := by
    have hh : (∑ x ∈ Finset.Ico ((L : ℤ) - 2 * b) L, τ ((x + b : ℤ) : ZMod L)) ≤
        (∑ x ∈ Finset.Ico ((L : ℤ) - 2 * b) L, τ (x : ZMod L)) +
        (∑ x ∈ Finset.Ico ((L : ℤ) - 2 * b) L, |lift τ (x + b) - lift τ x|) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro x _
      have h := le_abs_self (lift τ (x + b) - lift τ x)
      dsimp only [lift] at h ⊢
      omega
    omega
  change variation f 1 ≤ _ at hcover
  change variation τ (b : ZMod L) ≤ 2 * variation f (b : ZMod L) at hvarτ
  omega

/-- The u=0,v=1 case uses a wrapping segment in the new period. -/
theorem second_digit_one (L L' : ℕ) [NeZero L] [NeZero L']
    (f : ZMod L → ℤ) (g : ZMod L' → ℤ) (a b G G' : ℤ)
    (hb : 0 < b) (hba : b < a)
    (hL : (L : ℤ) = a + b) (hL' : (L' : ℤ) = 2 * (a + b) + 1)
    (haold : variation f (a : ZMod L) ≤ 2 * G)
    (hanew : variation g ((2 * a : ℤ) : ZMod L') ≤ 2 * G')
    (hd : (∑ x ∈ Finset.Ico 0 (L' : ℤ), |lift f x - lift g x|) ≤ G + 1) :
    variation f 1 ≤ 6 * G + 2 * G' + 2 := by
  have hcomp := compare_segment L' (lift f) g (2 * b + 1) (2 * b + 1 + L)
    (2 * a - (L' : ℤ)) (G + 1) (by omega) (by omega) (by omega) (by omega) hd
  have hnew : ((2 * a - (L' : ℤ) : ℤ) : ZMod L') = ((2 * a : ℤ) : ZMod L') := by simp
  rw [hnew] at hcomp
  have hold : ((2 * a - (L' : ℤ) : ℤ) : ZMod L) = ((2 * a - 1 : ℤ) : ZMod L) := by
    have he : 2 * a - (L' : ℤ) = (2 * a - 1) - 2 * (L : ℤ) := by omega
    rw [he]
    simp
  have heq : (∑ x ∈ Finset.Ico (2 * b + 1) (2 * b + 1 + L),
      |lift f (x + (2 * a - (L' : ℤ))) - lift f x|) =
      variation f ((2 * a - 1 : ℤ) : ZMod L) := by
    have he := IntervalSums.sum_period_start L
      (fun y => |f (y + ((2 * a - 1 : ℤ) : ZMod L)) - f y|) (2 * b + 1)
    simpa only [lift, Int.cast_add, hold] using he
  rw [heq] at hcomp
  have hdouble := variation_double f (a : ZMod L)
  have ht : ((2 * a : ℤ) : ZMod L) = (a : ZMod L) + (a : ZMod L) := by push_cast; ring
  rw [← ht] at hdouble
  have hadd := variation_add_le f ((2 * a : ℤ) : ZMod L) (-((2 * a - 1 : ℤ) : ZMod L))
  have hsum : ((2 * a : ℤ) : ZMod L) + -((2 * a - 1 : ℤ) : ZMod L) = 1 := by push_cast; ring
  rw [hsum, variation_neg] at hadd
  omega

/-- Manuscript (8.5): all three nonzero pairs of actual floor digits. -/
theorem actual_nonzero_boundary (α β : ℝ)
    (hb0 : 0 < FloorSequence.term β 0)
    (hba0 : FloorSequence.term β 0 < FloorSequence.term α 0)
    (hab0 : FloorSequence.term α 0 < 2 * FloorSequence.term β 0) (n : ℕ)
    (hevent : ExactBlock.IsEvent α β (n + 1)) :
    FEShift.boundary α β n 1 ≤ 16 * FECounting.growth α β n +
      4 * FECounting.growth α β (n + 1) + 4 * FECounting.digitSum α β n := by
  letI : NeZero (FEShift.length α β n) := ⟨ne_of_gt (FEShift.length_positive α β hb0 hba0 hab0 n)⟩
  letI : NeZero (FEShift.length α β (n + 1)) :=
    ⟨ne_of_gt (FEShift.length_positive α β hb0 hba0 hab0 (n + 1))⟩
  let f := missing (PeriodicWord.residues (FECounting.values α β n) (FEShift.length α β n))
  let g := missing (PeriodicWord.residues (FECounting.values α β (n + 1)) (FEShift.length α β (n + 1)))
  have hL := FEShift.length_cast α β hb0 hba0 hab0 n
  have hL' := FEShift.length_cast α β hb0 hba0 hab0 (n + 1)
  have hnorm := FloorSequence.normalized_bounds α β hb0 hba0 hab0 n
  have ha := FEShift.boundary_a_le α β hb0 hba0 hab0 n
  have hb := FEShift.boundary_b_eq_a α β hb0 hba0 hab0 n
  have ha' := FEShift.boundary_a_le α β hb0 hba0 hab0 (n + 1)
  have hd := PeriodChange.actual_changing_period_bound α β hb0 hba0 hab0 n
  have hu := FloorSequence.correction_bounds α n
  have hv := FloorSequence.correction_bounds β n
  have hw := (FECounting.digitSum_event_iff α β n).mpr hevent
  have hstep := FECounting.period_step α β n
  have har : FloorSequence.term α (n + 1) = 2 * FloorSequence.term α n + FloorSequence.correction α n := by
    unfold FloorSequence.correction
    ring
  rw [FEShift.boundary_eq_cyclic α β n hL] at ha hb ⊢
  simp only [Int.cast_one]
  change variation f 1 ≤ _
  rw [FEShift.boundary_eq_cyclic α β n hL] at hb
  rw [FEShift.boundary_eq_cyclic α β (n + 1) hL', har] at ha'
  have hbd : variation f (FloorSequence.term β n : ZMod (FEShift.length α β n)) ≤ 2 * FECounting.growth α β n := by
    rw [hb]
    exact ha
  have hdiff : (∑ x ∈ Finset.Ico 0 (FEShift.length α β (n + 1) : ℤ), |lift f x - lift g x|) ≤
      FECounting.growth α β n + FECounting.digitSum α β n := by
    rw [hL']
    have he (x : ℤ) : |lift f x - lift g x| =
        |FEShift.missingWord α β (n + 1) x - FEShift.missingWord α β n x| := abs_sub_comm _ _
    simp only [he]
    exact hd
  dsimp only [FECounting.digitSum] at hw hstep hdiff ⊢
  by_cases hu1 : FloorSequence.correction α n = 1
  · rw [hu1] at ha' hdiff ⊢
    have hl : (FEShift.length α β (n + 1) : ℤ) =
        2 * (FloorSequence.term α n + FloorSequence.term β n) + 1 + FloorSequence.correction β n := by
      dsimp only [PrefixBounds.period] at hL hL' hstep
      omega
    exact first_digit_one _ _ f g _ _ _ _ _ hnorm.2.1 hnorm.2.2 hL hl hv.1 ha hbd ha'
      (by simpa only [add_assoc] using hdiff)
  · have hu0 : FloorSequence.correction α n = 0 := by omega
    have hv1 : FloorSequence.correction β n = 1 := by omega
    rw [hu0, hv1] at hdiff ⊢
    rw [hu0, add_zero] at ha'
    have hl : (FEShift.length α β (n + 1) : ℤ) = 2 * (FloorSequence.term α n + FloorSequence.term β n) + 1 := by
      dsimp only [PrefixBounds.period] at hL hL' hstep
      omega
    have h := second_digit_one _ _ f g _ _ _ _ hnorm.1 hnorm.2.1 hL hl ha ha' hdiff
    have hG := FECounting.growth_nonneg α β hb0 hba0 hab0 n
    have hG' := FECounting.growth_nonneg α β hb0 hba0 hab0 (n + 1)
    omega

end Dyadic354.EventBoundary
