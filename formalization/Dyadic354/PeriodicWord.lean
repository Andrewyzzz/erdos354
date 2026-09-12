import Dyadic354.CyclicBoundary
import Mathlib.Algebra.Ring.Periodic

namespace Dyadic354.PeriodicWord

def residues (S : Finset ℤ) (L : ℕ) : Finset (ZMod L) := Mesh.residues S L

def word (S : Finset ℤ) (L : ℕ) (x : ℤ) : ℤ := CyclicBoundary.missing (residues S L) (x : ZMod L)

theorem cast_injective (L : ℕ) (x y : ℤ) (hx : x ∈ Finset.Ico 0 (L : ℤ))
    (hy : y ∈ Finset.Ico 0 (L : ℤ)) (he : (x : ZMod L) = (y : ZMod L)) : x = y := by
  have hx' := Finset.mem_Ico.mp hx
  have hy' := Finset.mem_Ico.mp hy
  rw [ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt hx'.1 hx'.2,
    Int.emod_eq_of_lt hy'.1 hy'.2] at he
  exact he

theorem cast_mem_iff (S : Finset ℤ) (L : ℕ) (hS : S ⊆ Finset.Ico 0 (L : ℤ))
    (x : ℤ) (hx : x ∈ Finset.Ico 0 (L : ℤ)) : (x : ZMod L) ∈ residues S L ↔ x ∈ S := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
    have heq := cast_injective L y x (hS hy) hx he
    rwa [← heq]
  · intro h
    exact Finset.mem_image.mpr ⟨x, h, rfl⟩

theorem word_on_period (S : Finset ℤ) (L : ℕ) (hS : S ⊆ Finset.Ico 0 (L : ℤ))
    (x : ℤ) (hx : x ∈ Finset.Ico 0 (L : ℤ)) : word S L x = if x ∈ S then 0 else 1 := by
  simp only [word, CyclicBoundary.missing, cast_mem_iff S L hS x hx]

theorem word_add_period (S : Finset ℤ) (L : ℕ) (x : ℤ) : word S L (x + L) = word S L x := by
  simp [word, Int.cast_add]

theorem word_sub_period (S : Finset ℤ) (L : ℕ) (x : ℤ) : word S L (x - L) = word S L x := by
  simp [word, Int.cast_sub]

theorem word_bounds (S : Finset ℤ) (L : ℕ) (x : ℤ) : 0 ≤ word S L x ∧ word S L x ≤ 1 :=
  CyclicBoundary.missing_bounds _ _

theorem sum_period (L : ℕ) [NeZero L] (f : ZMod L → ℤ) :
    (∑ x ∈ Finset.Ico 0 (L : ℤ), f (x : ZMod L)) = ∑ x, f x := by
  apply Finset.sum_bij (fun (x : ℤ) _ => (x : ZMod L))
  · intro _ _
    exact Finset.mem_univ _
  · intro x hx y hy he
    exact cast_injective L x y hx hy he
  · intro x _
    refine ⟨(x.val : ℤ), Finset.mem_Ico.mpr ⟨by omega, ?_⟩, ?_⟩
    · exact_mod_cast ZMod.val_lt x
    · simp
  · intro _ _
    rfl

theorem variation_eq_sum (S : Finset ℤ) (L : ℕ) [NeZero L] (t : ℤ) :
    CyclicBoundary.variation (CyclicBoundary.missing (residues S L)) (t : ZMod L) =
      ∑ x ∈ Finset.Ico 0 (L : ℤ), |word S L (x + t) - word S L x| := by
  unfold CyclicBoundary.variation
  rw [← sum_period]
  apply Finset.sum_congr rfl
  intro x _
  simp only [word, Int.cast_add]

/-- The pointwise representation is compatible with periodization, but no
identification between different cyclic groups is made. -/
theorem word_periodic (S : Finset ℤ) (L : ℕ) : Function.Periodic (word S L) (L : ℤ) :=
  word_add_period S L

end Dyadic354.PeriodicWord
