import Dyadic354.PeriodChange

namespace Dyadic354.FEMissingRuns

open CyclicBoundary PeriodicWord

theorem successor_after_hole (S : Finset ℤ) (u : ℤ) (k : ℕ)
    (hm : Mesh.MeshOn S 0 u k) (x : ℤ) (hx0 : 0 ≤ x) (hxu : x ≤ u) (hx : x ∉ S) :
    ∃ y ∈ S, x < y ∧ y < x + k ∧ y - 1 ∉ S := by
  let A := S.filter (fun y => x ≤ y)
  have hA : A.Nonempty := ⟨u, Finset.mem_filter.mpr ⟨hm.1.2.1, hxu⟩⟩
  let y := A.min' hA
  have hy := Finset.mem_filter.mp (A.min'_mem hA)
  have hxy : x < y := by
    by_contra h
    have he : x = y := by omega
    exact hx (he ▸ hy.1)
  obtain ⟨w, hw, hxw, hwk⟩ := hm.2 x hx0 hxu
  have hyw := A.min'_le w (Finset.mem_filter.mpr ⟨hw, hxw⟩)
  refine ⟨y, hy.1, hxy, by omega, ?_⟩
  intro hy1
  have hh := A.min'_le (y - 1) (Finset.mem_filter.mpr ⟨hy1, by omega⟩)
  omega

/-- Charge each internal missing position to the next represented endpoint
and its distance. This injects into reversed boundary exits times k positions. -/
theorem internal_holes_card (S : Finset ℤ) (L k : ℕ) [NeZero L] (u : ℤ)
    (hS : S ⊆ Finset.Ico 0 (L : ℤ)) (hm : Mesh.MeshOn S 0 u k) :
    (Finset.Icc 0 u \ S).card ≤ (exits (residues S L) (-1)).card * k := by
  classical
  let H := Finset.Icc 0 u \ S
  have hh (x : {z // z ∈ H}) : ∃ y ∈ S, x.val < y ∧ y < x.val + k ∧ y - 1 ∉ S := by
    have hx := Finset.mem_sdiff.mp x.property
    have hb := Finset.mem_Icc.mp hx.1
    exact successor_after_hole S u k hm x.val hb.1 hb.2 hx.2
  let next := fun x : {z // z ∈ H} => Classical.choose (hh x)
  have hn (x : {z // z ∈ H}) : next x ∈ S ∧ x.val < next x ∧ next x < x.val + k ∧ next x - 1 ∉ S :=
    Classical.choose_spec (hh x)
  let D := (exits (residues S L) (-1)).product (Finset.range k)
  have hmem (x : {z // z ∈ H}) : ((next x : ZMod L), (next x - x.val).toNat) ∈ D := by
    have hp := hn x
    have hx0 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp x.property).1).1
    have hyb := Finset.mem_Ico.mp (hS hp.1)
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_range.mpr (by omega)⟩
    refine ⟨Finset.mem_image.mpr ⟨next x, hp.1, rfl⟩, ?_⟩
    intro hbad
    have hc : ((next x : ZMod L) + -1) = ((next x - 1 : ℤ) : ZMod L) := by push_cast; ring
    rw [hc] at hbad
    exact hp.2.2.2 ((cast_mem_iff S L hS _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)).mp hbad)
  let f : {z // z ∈ H} → {p // p ∈ D} := fun x => ⟨((next x : ZMod L), (next x - x.val).toNat), hmem x⟩
  have hinj : Function.Injective f := by
    intro x y he
    have he' := congrArg Subtype.val he
    have h1 : (next x : ZMod L) = (next y : ZMod L) := congrArg Prod.fst he'
    have h2 : (next x - x.val).toNat = (next y - y.val).toNat := congrArg Prod.snd he'
    have hx := hn x
    have hy := hn y
    have hnxy := cast_injective L (next x) (next y) (hS hx.1) (hS hy.1) h1
    apply Subtype.ext
    omega
  have hc := Finset.card_le_card_of_injective hinj
  change H.card ≤ D.card at hc
  dsimp only [D] at hc
  rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_range] at hc
  exact hc

theorem holes_split_bound (S : Finset ℤ) (L : ℕ) (u : ℤ) (huL : u < L) :
    ((Finset.Ico 0 (L : ℤ) \ S).card : ℤ) ≤ (Finset.Icc 0 u \ S).card + ((L : ℤ) - u) := by
  have hsub : Finset.Ico 0 (L : ℤ) \ S ⊆ (Finset.Icc 0 u \ S) ∪ Finset.Ico (u + 1) (L : ℤ) := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    have hxb := Finset.mem_Ico.mp hx'.1
    by_cases hxu : x ≤ u
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hxb.1, hxu⟩, hx'.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, hxb.2⟩)
  have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [Int.card_Ico] at hc
  omega

/-- The doubled integer version of (8.2), avoiding any rounding convention
for N/2. The period's terminal padding is paid separately. -/
theorem holes_boundary_bound (S : Finset ℤ) (L k : ℕ) [NeZero L] (u : ℤ)
    (hS : S ⊆ Finset.Ico 0 (L : ℤ)) (hm : Mesh.MeshOn S 0 u k) :
    2 * ((Finset.Ico 0 (L : ℤ) \ S).card : ℤ) ≤
      (k : ℤ) * variation (missing (residues S L)) 1 + 2 * ((L : ℤ) - u) := by
  have hu := Finset.mem_Ico.mp (hS hm.1.2.1)
  have hc := holes_split_bound S L u hu.2
  have hi : ((Finset.Icc 0 u \ S).card : ℤ) ≤
      ((exits (residues S L) (-1)).card : ℤ) * (k : ℤ) := by
    exact_mod_cast internal_holes_card S L k u hS hm
  have hj := variation_missing (residues S L) (-1)
  rw [variation_neg] at hj
  nlinarith

set_option maxHeartbeats 1000000 in
theorem actual_holes_boundary_bound (α β : ℝ)
    (hb0 : 0 < FloorSequence.term β 0)
    (hba0 : FloorSequence.term β 0 < FloorSequence.term α 0)
    (hab0 : FloorSequence.term α 0 < 2 * FloorSequence.term β 0) (n : ℕ) :
    2 * FECounting.deficit α β n ≤
      FloorSequence.term β 0 * FEShift.boundary α β n 1 + 2 * FECounting.padding α β n := by
  letI : NeZero (FEShift.length α β n) := ⟨ne_of_gt (FEShift.length_positive α β hb0 hba0 hab0 n)⟩
  have hL := FEShift.length_cast α β hb0 hba0 hab0 n
  have hs := FECounting.values_subset_period α β hb0 hba0 hab0 n
  rw [← hL] at hs
  have hk : 0 < (FloorSequence.term β 0).toNat := by omega
  have hm := Mesh.meshOn_of_gap_le _ _ _ _ (PrefixBounds.actual_prefix_encloses α β hb0 hba0 hab0 n)
    hk (PrefixBounds.actual_prefix_gap α β hb0 hba0 hab0 n)
  have h := holes_boundary_bound (FECounting.values α β n) (FEShift.length α β n)
    (FloorSequence.term β 0).toNat (PrefixBounds.total α β n) hs hm
  rw [hL, Int.toNat_of_nonneg (le_of_lt hb0)] at h
  rw [FECounting.deficit_eq_holes α β hb0 hba0 hab0 n,
    FEShift.boundary_eq_cyclic α β n hL]
  simpa only [Int.cast_one, FECounting.holes, FECounting.padding] using h

end Dyadic354.FEMissingRuns
