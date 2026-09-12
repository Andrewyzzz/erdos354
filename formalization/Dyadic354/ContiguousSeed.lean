import Dyadic354.FECounting
import Mathlib.Data.Finset.Lattice.Fold

namespace Dyadic354.ContiguousSeed

open scoped Classical

/-- Width, not cardinality, of the longest integer interval in S. -/
noncomputable def width (S : Finset ℤ) : ℕ :=
  S.sup fun x => S.sup fun y => if Finset.Icc x y ⊆ S then (y - x).toNat else 0

theorem interval_width_le (S : Finset ℤ) (x y : ℤ) (hxy : x ≤ y)
    (h : Finset.Icc x y ⊆ S) : (y - x).toNat ≤ width S := by
  have hx := h (Finset.mem_Icc.mpr ⟨le_rfl, hxy⟩)
  have hy := h (Finset.mem_Icc.mpr ⟨hxy, le_rfl⟩)
  unfold width
  apply Finset.le_sup_of_le hx
  apply Finset.le_sup_of_le hy
  simp [h]

theorem width_attained (S : Finset ℤ) (hne : S.Nonempty) :
    ∃ x y : ℤ, x ≤ y ∧ Finset.Icc x y ⊆ S ∧ y - x = (width S : ℤ) := by
  by_cases h0 : width S = 0
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, x, le_rfl, by simpa using hx, by simp [h0]⟩
  obtain ⟨x, hx, he⟩ := Finset.exists_mem_eq_sup S hne
    (fun x => S.sup fun y => if Finset.Icc x y ⊆ S then (y - x).toNat else 0)
  obtain ⟨y, hy, he'⟩ := Finset.exists_mem_eq_sup S hne
    (fun y => if Finset.Icc x y ⊆ S then (y - x).toNat else 0)
  change width S = _ at he
  rw [he'] at he
  split_ifs at he with hh
  · exact ⟨x, y, by omega, hh, by omega⟩
  · exact (h0 he).elim

theorem next_hole (S : Finset ℤ) (u x : ℤ) (hS : S ⊆ Finset.Icc 0 u) (hx : x ∈ S) :
    ∃ y ∈ insert (u + 1) (Finset.Icc 0 u \ S),
      0 < y - x ∧ y - x ≤ (width S : ℤ) + 1 := by
  let D := insert (u + 1) (Finset.Icc 0 u \ S)
  let T := D.filter (fun y => x ≤ y)
  have hxb := Finset.mem_Icc.mp (hS hx)
  have hne : T.Nonempty := ⟨u + 1, by simp [T, D]; omega⟩
  let y := T.min' hne
  have hym := T.min'_mem hne
  obtain ⟨hyD, hxy⟩ := Finset.mem_filter.mp hym
  have hynot : y ∉ S := by
    intro hyS
    rcases Finset.mem_insert.mp hyD with hy | hy
    · have h := Finset.mem_Icc.mp (hS hyS); omega
    · exact (Finset.mem_sdiff.mp hy).2 hyS
  have hyu : y ≤ u + 1 := T.min'_le (u + 1) (by simp [T, D]; omega)
  have hlt : x < y := lt_of_le_of_ne hxy (by intro hh; exact hynot (hh ▸ hx))
  have hi : Finset.Icc x (y - 1) ⊆ S := by
    intro z hz
    have hz' := Finset.mem_Icc.mp hz
    by_contra hn
    have hzT : z ∈ T := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨?_, hn⟩), hz'.1⟩
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hh := T.min'_le z hzT
    omega
  have hw := interval_width_le S x (y - 1) (by omega) hi
  exact ⟨y, hyD, by omega, by omega⟩

theorem represented_card_bound (S : Finset ℤ) (u : ℤ) (hS : S ⊆ Finset.Icc 0 u) :
    S.card ≤ ((Finset.Icc 0 u \ S).card + 1) * (width S + 1) := by
  let D := insert (u + 1) (Finset.Icc 0 u \ S)
  have hn (x : S) := next_hole S u x hS x.property
  choose y hy hp hw using hn
  let f (x : S) : ℤ × ℕ := (y x, (y x - x - 1).toNat)
  have hf (x : S) : f x ∈ D.product (Finset.range (width S + 1)) := by
    apply Finset.mem_product.mpr
    exact ⟨hy x, Finset.mem_range.mpr (by have h := hw x; have h' := hp x; dsimp [f]; omega)⟩
  have hi : Function.Injective f := by
    intro x z he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp [f] at h1 h2
    have hx := hp x
    have hz := hp z
    apply Subtype.ext
    omega
  have hc := Finset.card_le_card_of_injOn (s := Finset.univ) f (by intro x _; exact hf x)
    (by intro x _ z _ he; exact hi he)
  simp only [Finset.card_univ, Fintype.card_coe] at hc
  rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_range] at hc
  have hD : D.card ≤ (Finset.Icc 0 u \ S).card + 1 := Finset.card_insert_le _ _
  exact hc.trans (Nat.mul_le_mul_right _ hD)

/-- The integer form of the manuscript's run-count estimate. -/
theorem width_count_bound (S : Finset ℤ) (u : ℤ) (hu : 0 ≤ u) (hS : S ⊆ Finset.Icc 0 u) :
    u + 2 ≤ (((Finset.Icc 0 u \ S).card : ℤ) + 1) * ((width S : ℤ) + 2) := by
  have hc := represented_card_bound S u hS
  have he := Finset.card_sdiff_add_card_eq_card hS
  rw [Int.card_Icc] at he
  have hc' : (S.card : ℤ) ≤ (((Finset.Icc 0 u \ S).card : ℤ) + 1) * ((width S : ℤ) + 1) := by
    exact_mod_cast hc
  have he' : ((Finset.Icc 0 u \ S).card : ℤ) + S.card = u + 1 := by omega
  nlinarith

end Dyadic354.ContiguousSeed
