import Dyadic354.FECounting
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Dyadic354.CyclicBoundary

variable {G : Type*} [AddCommGroup G] [Fintype G]

def missing [DecidableEq G] (S : Finset G) (x : G) : ℤ := if x ∈ S then 0 else 1

def variation (f : G → ℤ) (t : G) : ℤ := ∑ x, |f (x + t) - f x|

def exits [DecidableEq G] (S : Finset G) (t : G) : Finset G :=
  Finset.univ.filter (fun x => x ∈ S ∧ x + t ∉ S)

theorem sum_shift (f : G → ℤ) (t : G) : (∑ x, f (x + t)) = ∑ x, f x := by
  apply Fintype.sum_bijective (fun x => x + t)
    ⟨fun _ _ h => add_right_cancel h, fun y => ⟨y - t, by simp⟩⟩
  intro x
  rfl

theorem variation_nonneg (f : G → ℤ) (t : G) : 0 ≤ variation f t :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem variation_zero (f : G → ℤ) : variation f 0 = 0 := by simp [variation]

theorem variation_neg (f : G → ℤ) (t : G) : variation f (-t) = variation f t := by
  have h := sum_shift (fun x => |f (x + -t) - f x|) t
  unfold variation
  rw [← h]
  apply Finset.sum_congr rfl
  intro x _
  simp only [add_neg_cancel_right, abs_sub_comm]

theorem variation_add_le (f : G → ℤ) (s t : G) :
    variation f (s + t) ≤ variation f s + variation f t := by
  calc
    _ ≤ ∑ x, (|f ((x + t) + s) - f (x + t)| + |f (x + t) - f x|) := by
      apply Finset.sum_le_sum
      intro x _
      have he : x + (s + t) = (x + t) + s := by abel
      rw [he]
      exact abs_sub_le _ _ _
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_shift (fun x => |f (x + s) - f x|) t]
      rfl

omit [AddCommGroup G] [Fintype G] in
theorem missing_bounds [DecidableEq G] (S : Finset G) (x : G) : 0 ≤ missing S x ∧ missing S x ≤ 1 := by
  unfold missing
  split_ifs <;> omega

/-- Variation counts twice the represented-to-missing transitions. -/
theorem variation_missing [DecidableEq G] (S : Finset G) (t : G) :
    variation (missing S) t = 2 * (exits S t).card := by
  have hp (x : G) : |missing S (x + t) - missing S x| =
      2 * (if x ∈ S ∧ x + t ∉ S then (1 : ℤ) else 0) -
        (missing S (x + t) - missing S x) := by
    by_cases hx : x ∈ S <;> by_cases ht : x + t ∈ S <;> simp [missing, hx, ht]
  unfold variation
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_shift]
  simp only [sub_self, sub_zero]
  congr 1
  simp [exits]

theorem variation_double (f : G → ℤ) (t : G) : variation f (t + t) ≤ 2 * variation f t := by
  have h := variation_add_le f t t
  omega

theorem variation_shift (f : G → ℤ) (s t : G) :
    variation (fun x => f (x + s)) t = variation f t := by
  have h := sum_shift (fun x => |f (x + t) - f x|) s
  calc
    _ = ∑ x, |f ((x + s) + t) - f (x + s)| := by
      apply Finset.sum_congr rfl
      intro x _
      congr 2
      abel
    _ = _ := h

/-- Translating the unit-boundary word costs at most twice the corresponding
translation of the original word. -/
theorem variation_boundary_le (f : G → ℤ) (s t : G) :
    variation (fun x => |f (x + s) - f x|) t ≤ 2 * variation f t := by
  calc
    _ ≤ ∑ x, (|f ((x + s) + t) - f (x + s)| + |f (x + t) - f x|) := by
      apply Finset.sum_le_sum
      intro x _
      have h := abs_abs_sub_abs_le_abs_sub (f ((x + t) + s) - f (x + t)) (f (x + s) - f x)
      have he : (x + t) + s = (x + s) + t := by abel
      rw [he] at h
      change abs (abs (f ((x + t) + s) - f (x + t)) - abs (f (x + s) - f x)) ≤ _
      rw [he]
      apply le_trans h
      have he' : f ((x + s) + t) - f (x + t) - (f (x + s) - f x) =
          (f ((x + s) + t) - f (x + s)) - (f (x + t) - f x) := by ring
      rw [he']
      exact abs_sub _ _
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_shift (fun x => |f (x + t) - f x|) s]
      unfold variation
      ring

end Dyadic354.CyclicBoundary
