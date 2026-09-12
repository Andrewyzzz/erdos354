import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

namespace Dyadic354.RationalWindows

open Set
open scoped Classical

def Good (θ : ℝ) (r : ℚ) : Prop := |θ - (r : ℝ)| < 1 / (r.den : ℝ) ^ 2

theorem cast_mul_den (r : ℚ) : (r : ℝ) * r.den = (r.num : ℝ) := by
  rw [Rat.cast_def]
  exact div_mul_cancel₀ _ (by exact_mod_cast r.den_nz)

theorem good_distance_lt_one (θ : ℝ) (r : ℚ) (hr : Good θ r) : |θ - (r : ℝ)| < 1 := by
  have hd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hh : 1 / (r.den : ℝ) ^ 2 ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (r.den : ℝ) ^ 2)).mpr
    nlinarith
  exact hr.trans_le hh

theorem bounded_good_finite (θ : ℝ) (D : ℕ) : {r : ℚ | Good θ r ∧ r.den ≤ D}.Finite := by
  let f : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk_inj] at hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hab.1, hab.2]
  have hsub : f '' {r : ℚ | Good θ r ∧ r.den ≤ D} ⊆
      ⋃ (d : ℕ) (_ : d ∈ Set.Ioc 0 D),
        Set.Icc ⌈(θ - 1) * d⌉ ⌊(θ + 1) * d⌋ ×ˢ {d} := by
    rintro _ ⟨r, ⟨hr, hd⟩, rfl⟩
    have h := abs_lt.mp (good_distance_lt_one θ r hr)
    have hdpos : (0 : ℝ) < r.den := by exact_mod_cast r.pos
    have he := cast_mul_den r
    have hlo : (θ - 1) * r.den ≤ (r.num : ℝ) := by nlinarith
    have hhi : (r.num : ℝ) ≤ (θ + 1) * r.den := by nlinarith
    simp only [Set.mem_iUnion]
    exact ⟨r.den, ⟨r.pos, hd⟩, ⟨⟨Int.ceil_le.mpr hlo, Int.le_floor.mpr hhi⟩, rfl⟩⟩
  refine (Set.Finite.subset ?_ hsub).of_finite_image hinj.injOn
  exact Set.Finite.biUnion (Set.finite_Ioc _ _) (fun d _ =>
    (Set.finite_Icc _ _).prod (Set.finite_singleton d))

theorem good_den_unbounded (θ : ℝ) (hθ : Irrational θ) (D : ℕ) :
    ∃ r : ℚ, Good θ r ∧ D < r.den := by
  have hi := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hθ
  by_contra hh
  push_neg at hh
  apply hi
  exact (bounded_good_finite θ D).subset (fun r hr => ⟨hr, by have h := hh r hr; omega⟩)

theorem crossing_exists (θ : ℝ) (hθ : Irrational θ) (b : ℕ) :
    ∃ d : ℕ, b ≤ d ∧ ∃ r : ℚ, r.den = d ∧ Good θ r := by
  obtain ⟨r, hr, hb⟩ := good_den_unbounded θ hθ b
  exact ⟨r.den, by omega, r, rfl, hr⟩

/-- Least denominator of a good rational approximation above a threshold.
Using all good rationals generalizes the continued-fraction interface. -/
noncomputable def crossingDen (θ : ℝ) (hθ : Irrational θ) (b : ℕ) : ℕ :=
  Nat.find (crossing_exists θ hθ b)

theorem crossing_spec (θ : ℝ) (hθ : Irrational θ) (b : ℕ) :
    b ≤ crossingDen θ hθ b ∧ ∃ r : ℚ, r.den = crossingDen θ hθ b ∧ Good θ r :=
  Nat.find_spec (crossing_exists θ hθ b)

noncomputable def crossingRat (θ : ℝ) (hθ : Irrational θ) (b : ℕ) : ℚ :=
  Classical.choose (crossing_spec θ hθ b).2

theorem crossingRat_spec (θ : ℝ) (hθ : Irrational θ) (b : ℕ) :
    (crossingRat θ hθ b).den = crossingDen θ hθ b ∧ Good θ (crossingRat θ hθ b) :=
  Classical.choose_spec (crossing_spec θ hθ b).2

theorem crossing_minimal (θ : ℝ) (hθ : Irrational θ) (b : ℕ) (r : ℚ)
    (hr : Good θ r) (hb : b ≤ r.den) : crossingDen θ hθ b ≤ r.den :=
  Nat.find_min' (crossing_exists θ hθ b) ⟨hb, r, rfl, hr⟩

/-- Dirichlet approximation just before a least good denominator produces
a much smaller denominator with accuracy controlled by the next crossing.
This supplies the long-window approximation without a CF placeholder. -/
theorem before_crossing (θ : ℝ) (hθ : Irrational θ) (b : ℕ) (hb : 2 ≤ b) :
    ∃ r : ℚ, r.den < b ∧ Good θ r ∧
      |θ - (r : ℝ)| ≤ 1 / ((crossingDen θ hθ b : ℝ) * r.den) := by
  let D := crossingDen θ hθ b
  have hD : 2 ≤ D := hb.trans (crossing_spec θ hθ b).1
  obtain ⟨r, hr, hd⟩ := Real.exists_rat_abs_sub_le_and_den_le θ (show 0 < D - 1 by omega)
  have hDE : (D - 1 : ℕ) + 1 = D := by omega
  have hDC : ((D - 1 : ℕ) : ℝ) + 1 = D := by exact_mod_cast hDE
  rw [hDC] at hr
  have hrpos : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hDr : (r.den : ℝ) < D := by exact_mod_cast (show r.den < D by omega)
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hgood : Good θ r := by
    apply hr.trans_lt
    apply (div_lt_div_iff₀ (mul_pos hDR hrpos) (pow_pos hrpos 2)).mpr
    nlinarith
  have hsmall : r.den < b := by
    by_contra hh
    have hc := crossing_minimal θ hθ b r hgood (by omega)
    change D ≤ r.den at hc
    omega
  exact ⟨r, hsmall, hgood, hr⟩

end Dyadic354.RationalWindows
