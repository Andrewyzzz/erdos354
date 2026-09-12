import Dyadic354.PeriodicWord
import Mathlib.Algebra.BigOperators.Intervals

namespace Dyadic354.IntervalSums

theorem split (f : ℤ → ℤ) (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ x ∈ Finset.Ico a b, f x) + (∑ x ∈ Finset.Ico b c, f x) = ∑ x ∈ Finset.Ico a c, f x := by
  rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a b c), Finset.Ico_union_Ico_eq_Ico hab hbc]

theorem mono (f : ℤ → ℤ) (hf : ∀ x, 0 ≤ f x) (a b c d : ℤ) (hca : c ≤ a) (hbd : b ≤ d) :
    (∑ x ∈ Finset.Ico a b, f x) ≤ ∑ x ∈ Finset.Ico c d, f x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    have h := Finset.mem_Ico.mp hx
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro x _ _
    exact hf x

theorem sum_period_start (L : ℕ) [NeZero L] (f : ZMod L → ℤ) (a : ℤ) :
    (∑ x ∈ Finset.Ico a (a + L), f (x : ZMod L)) = ∑ x, f x := by
  rw [add_comm a (L : ℤ)]
  have h := Finset.sum_Ico_add' (fun x : ℤ => f (x : ZMod L)) 0 L a
  simp only [zero_add] at h
  rw [← h]
  simp only [Int.cast_add]
  change (∑ x ∈ Finset.Ico 0 (L : ℤ), (fun y : ZMod L => f (y + (a : ZMod L))) (x : ZMod L)) = _
  rw [PeriodicWord.sum_period L (fun y : ZMod L => f (y + (a : ZMod L)))]
  exact CyclicBoundary.sum_shift f (a : ZMod L)

theorem interval_le_period (L : ℕ) [NeZero L] (f : ZMod L → ℤ) (hf : ∀ x, 0 ≤ f x)
    (a b : ℤ) (hlen : b - a ≤ L) :
    (∑ x ∈ Finset.Ico a b, f (x : ZMod L)) ≤ ∑ x, f x := by
  have h := mono (fun x : ℤ => f (x : ZMod L)) (fun _ => hf _) a b a (a + L) (le_refl _) (by omega)
  rwa [sum_period_start] at h

/-- Two old-period arcs cover the circle, with multiplicity allowed. -/
theorem two_arcs_cover (L : ℕ) [NeZero L] (f : ZMod L → ℤ) (hf : ∀ x, 0 ≤ f x)
    (b : ℤ) (h2 : 2 * b ≤ L) (h3 : (L : ℤ) ≤ 3 * b) :
    (∑ x, f x) ≤ (∑ x ∈ Finset.Ico ((L : ℤ) - 2 * b) L, f (x : ZMod L)) +
      (∑ x ∈ Finset.Ico ((L : ℤ) - 2 * b) L, f ((x + b : ℤ) : ZMod L)) := by
  have hs := split (fun x : ℤ => f (x : ZMod L)) 0 ((L : ℤ) - 2 * b) L (by omega) (by omega)
  rw [PeriodicWord.sum_period] at hs
  have hleft := mono (fun x : ℤ => f (x : ZMod L)) (fun _ => hf _)
    0 ((L : ℤ) - 2 * b) 0 b (le_refl _) (by omega)
  have hwrap : (∑ x ∈ Finset.Ico 0 b, f (x : ZMod L)) =
      ∑ x ∈ Finset.Ico (L : ℤ) ((L : ℤ) + b), f (x : ZMod L) := by
    have h := Finset.sum_Ico_add' (fun x : ℤ => f (x : ZMod L)) 0 b L
    simpa only [zero_add, Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero, add_comm b (L : ℤ)] using h
  have hright := mono (fun x : ℤ => f (x : ZMod L)) (fun _ => hf _)
    L ((L : ℤ) + b) ((L : ℤ) - b) ((L : ℤ) + b) (by omega) (le_refl _)
  have hshift := Finset.sum_Ico_add' (fun x : ℤ => f (x : ZMod L)) ((L : ℤ) - 2 * b) L b
  have he : (L : ℤ) - 2 * b + b = (L : ℤ) - b := by omega
  rw [he] at hshift
  rw [hwrap] at hleft
  dsimp only at hs hleft hright hshift
  rw [hshift]
  omega

theorem replace_variation (f g : ℤ → ℤ) (D : Finset ℤ) (t : ℤ) :
    (∑ x ∈ D, |f (x + t) - f x|) ≤ (∑ x ∈ D, |g (x + t) - g x|) +
      (∑ x ∈ D, |f (x + t) - g (x + t)|) + (∑ x ∈ D, |f x - g x|) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have h1 := abs_sub_le (f (x + t)) (g (x + t)) (f x)
  have h2 := abs_sub_le (g (x + t)) (g x) (f x)
  rw [abs_sub_comm (g x) (f x)] at h2
  omega

end Dyadic354.IntervalSums
