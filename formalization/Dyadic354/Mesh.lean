import Dyadic354.CyclicGaps
import Mathlib.Data.Finset.Max

namespace Dyadic354
namespace Mesh

/-- Actual consecutive distinct elements, with no intervening element of W. -/
def Consecutive (W : Finset ℤ) (a b : ℤ) : Prop :=
  a ∈ W ∧ b ∈ W ∧ a < b ∧ ∀ w ∈ W, a < w → b ≤ w

instance (W : Finset ℤ) (a b : ℤ) : Decidable (Consecutive W a b) := by
  unfold Consecutive
  infer_instance

/-- Maximum adjacent distance. Empty and singleton sets have gap zero. -/
def gap (W : Finset ℤ) : ℕ :=
  (W.product W).sup (fun ab => if Consecutive W ab.1 ab.2 then (ab.2-ab.1).toNat else 0)

def span (W : Finset ℤ) (hW : W.Nonempty) : ℤ := W.max' hW - W.min' hW

def Encloses (W : Finset ℤ) (lo hi : ℤ) : Prop :=
  lo ∈ W ∧ hi ∈ W ∧ ∀ w ∈ W, lo ≤ w ∧ w ≤ hi

/-- A rightward k-window from any point of the hull meets the actual finite set. -/
def MeshOn (W : Finset ℤ) (lo hi : ℤ) (k : ℕ) : Prop :=
  Encloses W lo hi ∧
    ∀ z : ℤ, lo ≤ z → z ≤ hi → ∃ w ∈ W, z ≤ w ∧ w < z+(k : ℤ)

theorem gap_le_iff (W : Finset ℤ) (k : ℕ) :
    gap W ≤ k ↔ ∀ a b, Consecutive W a b → b-a ≤ (k : ℤ) := by
  unfold gap
  rw [Finset.sup_le_iff]
  constructor
  · intro h a b hab
    have he := h (a,b) (Finset.mem_product.mpr ⟨hab.1, hab.2.1⟩)
    simp only [if_pos hab] at he
    omega
  · intro h ab _hab
    by_cases hc : Consecutive W ab.1 ab.2
    · simp only [if_pos hc]
      have := h ab.1 ab.2 hc
      omega
    · simp [hc]

theorem gap_empty : gap ∅ = 0 := by simp [gap]

theorem gap_singleton (a : ℤ) : gap {a} = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (gap_le_iff _ 0).2
  intro x y h
  have hx : x = a := by simpa using h.1
  have hy : y = a := by simpa using h.2.1
  have := h.2.2.1
  omega

theorem encloses_min_max (W : Finset ℤ) (hW : W.Nonempty) :
    Encloses W (W.min' hW) (W.max' hW) := by
  refine ⟨W.min'_mem hW, W.max'_mem hW, ?_⟩
  intro w hw
  exact ⟨W.min'_le w hw, W.le_max' w hw⟩

theorem span_of_encloses (W : Finset ℤ) (hW : W.Nonempty) (lo hi : ℤ)
    (he : Encloses W lo hi) : span W hW = hi-lo := by
  have hl : W.min' hW = lo :=
    le_antisymm (W.min'_le lo he.1) (he.2.2 _ (W.min'_mem hW)).1
  have hu : W.max' hW = hi :=
    le_antisymm (he.2.2 _ (W.max'_mem hW)).2 (W.le_max' hi he.2.1)
  simp [span, hl, hu]

theorem span_singleton (a : ℤ) : span {a} (Finset.singleton_nonempty a) = 0 := by
  simp [span]

theorem meshOn_gap_le (W : Finset ℤ) (lo hi : ℤ) (k : ℕ)
    (hm : MeshOn W lo hi k) : gap W ≤ k := by
  apply (gap_le_iff W k).2
  intro a b hab
  have ha := (hm.1.2.2 a hab.1).1
  have hb := (hm.1.2.2 b hab.2.1).2
  obtain ⟨w, hw, haw, hwk⟩ := hm.2 (a+1) (by omega) (by have := hab.2.2.1; omega)
  have hbw := hab.2.2.2 w hw (by omega)
  omega

/-- The window formulation follows from the actual adjacent-gap maximum. -/
theorem meshOn_of_gap_le (W : Finset ℤ) (lo hi : ℤ) (k : ℕ)
    (he : Encloses W lo hi) (hk : 0 < k) (hg : gap W ≤ k) : MeshOn W lo hi k := by
  refine ⟨he, ?_⟩
  intro z hlz hzu
  let B := W.filter (fun w => z ≤ w)
  have hB : B.Nonempty := ⟨hi, Finset.mem_filter.mpr ⟨he.2.1, hzu⟩⟩
  let b := B.min' hB
  have hb : b ∈ B := B.min'_mem hB
  have hbW : b ∈ W := (Finset.mem_filter.mp hb).1
  have hzb : z ≤ b := (Finset.mem_filter.mp hb).2
  have bmin : ∀ w ∈ W, z ≤ w → b ≤ w := by
    intro w hw hzw
    exact B.min'_le w (Finset.mem_filter.mpr ⟨hw, hzw⟩)
  refine ⟨b, hbW, hzb, ?_⟩
  by_cases heq : b = z
  · omega
  · have hloz : lo < z := by
      by_contra hn
      have hb0 := bmin lo he.1 (by omega)
      omega
    let A := W.filter (fun w => w < z)
    have hA : A.Nonempty := ⟨lo, Finset.mem_filter.mpr ⟨he.1, hloz⟩⟩
    let a := A.max' hA
    have ha : a ∈ A := A.max'_mem hA
    have haW : a ∈ W := (Finset.mem_filter.mp ha).1
    have haz : a < z := (Finset.mem_filter.mp ha).2
    have hab : Consecutive W a b := by
      refine ⟨haW, hbW, by omega, ?_⟩
      intro w hw haw
      by_cases hwz : w < z
      · have hwa := A.le_max' w (Finset.mem_filter.mpr ⟨hw, hwz⟩)
        omega
      · exact bmin w hw (by omega)
    have hgap := (gap_le_iff W k).1 hg a b hab
    omega

theorem meshOn_iff_gap_le (W : Finset ℤ) (lo hi : ℤ) (k : ℕ)
    (he : Encloses W lo hi) (hk : 0 < k) : MeshOn W lo hi k ↔ gap W ≤ k :=
  ⟨meshOn_gap_le W lo hi k, meshOn_of_gap_le W lo hi k he hk⟩

theorem gap_positive_of_encloses (W : Finset ℤ) (lo hi : ℤ)
    (he : Encloses W lo hi) (hlt : lo < hi) : 0 < gap W := by
  let B := W.filter (fun w => lo < w)
  have hB : B.Nonempty := ⟨hi, Finset.mem_filter.mpr ⟨he.2.1, hlt⟩⟩
  let b := B.min' hB
  have hb := Finset.mem_filter.mp (B.min'_mem hB)
  have hc : Consecutive W lo b := by
    refine ⟨he.1, hb.1, hb.2, ?_⟩
    intro w hw hlw
    exact B.min'_le w (Finset.mem_filter.mpr ⟨hw, hlw⟩)
  have := (gap_le_iff W (gap W)).1 (le_refl _) lo b hc
  omega

def translate (W : Finset ℤ) (c : ℤ) : Finset ℤ := W.image (fun w => w+c)

/-- Overlapping or touching hulls preserve the same mesh-window bound. -/
theorem meshOn_translate_union (W : Finset ℤ) (lo hi c : ℤ) (k : ℕ)
    (hm : MeshOn W lo hi k) (hc : 0 ≤ c) (hspan : c ≤ hi-lo) :
    MeshOn (W ∪ translate W c) lo (hi+c) k := by
  have bounds : Encloses (W ∪ translate W c) lo (hi+c) := by
    refine ⟨Finset.mem_union_left _ hm.1.1, ?_, ?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨hi, hm.1.2.1, rfl⟩)
    · intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · have := hm.1.2.2 w hw
        constructor <;> omega
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        have := hm.1.2.2 v hv
        constructor <;> omega
  refine ⟨bounds, ?_⟩
  intro z hlz hzu
  by_cases hz : z ≤ hi
  · obtain ⟨w, hw, hzw, hwk⟩ := hm.2 z hlz hz
    exact ⟨w, Finset.mem_union_left _ hw, hzw, hwk⟩
  · obtain ⟨w, hw, hzw, hwk⟩ := hm.2 (z-c) (by omega) (by omega)
    exact ⟨w+c, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩),
      by omega, by omega⟩

theorem translate_union_nonempty (W : Finset ℤ) (hW : W.Nonempty) (c : ℤ) :
    (W ∪ translate W c).Nonempty := hW.mono Finset.subset_union_left

/-- Manuscript Lemma 2.2: actual maximum gap and exact span of the union. -/
theorem translate_union_gap_span (W : Finset ℤ) (hW : W.Nonempty) (c : ℤ) (k : ℕ)
    (hc : 0 < c) (hs : c ≤ span W hW) (hg : gap W ≤ k) :
    gap (W ∪ translate W c) ≤ k ∧
    span (W ∪ translate W c) (translate_union_nonempty W hW c) = span W hW+c := by
  have he := encloses_min_max W hW
  have hlt : W.min' hW < W.max' hW := by unfold span at hs; omega
  have hk : 0 < k := lt_of_lt_of_le (gap_positive_of_encloses W _ _ he hlt) hg
  have hm := meshOn_of_gap_le W _ _ k he hk hg
  have hu := meshOn_translate_union W _ _ c k hm (le_of_lt hc) hs
  refine ⟨meshOn_gap_le _ _ _ _ hu, ?_⟩
  rw [span_of_encloses _ _ _ _ hu.1]
  unfold span
  omega

def residues (W : Finset ℤ) (m : ℕ) : Finset (ZMod m) := W.image (fun w : ℤ => (w : ZMod m))

theorem residues_nonempty (W : Finset ℤ) (hW : W.Nonempty) (m : ℕ) :
    (residues W m).Nonempty := hW.image _

/-- A window from any residue is represented by a window in the integer hull.
This includes the wraparound boundary and does not identify different moduli. -/
theorem projection_window_bound (W : Finset ℤ) (lo hi : ℤ) (k m : ℕ) [NeZero m]
    (hm : MeshOn W lo hi k) (hs : (m : ℤ) ≤ hi-lo) :
    CyclicGaps.GapBound (CyclicGaps.lift (residues W m)) (k-1) := by
  intro a
  let r : ZMod m := ((a-lo : ℤ) : ZMod m)
  let z : ℤ := lo + (r.val : ℤ)
  have hr := ZMod.val_lt r
  have hzl : lo ≤ z := by dsimp [z]; omega
  have hzh : z ≤ hi := by dsimp [z]; omega
  have hcast : (z : ZMod m) = (a : ZMod m) := by
    dsimp [z]
    simp [r, Int.cast_add, Int.cast_sub]
  obtain ⟨w, hw, hzw, hwk⟩ := hm.2 z hzl hzh
  let i := (w-z).toNat
  have he : (i : ℤ) = w-z := Int.toNat_of_nonneg (by omega)
  refine ⟨i, by omega, ?_⟩
  change ((a + (i : ℤ) : ℤ) : ZMod m) ∈ residues W m
  apply Finset.mem_image.mpr
  refine ⟨w, hw, ?_⟩
  have hwEq : w = z + (i : ℤ) := by omega
  calc
    (w : ZMod m) = (z : ZMod m) + ((i : ℤ) : ZMod m) := by
      rw [hwEq]
      exact Int.cast_add z (i : ℤ)
    _ = (a : ZMod m) + ((i : ℤ) : ZMod m) :=
      congrArg (fun x : ZMod m => x + ((i : ℤ) : ZMod m)) hcast
    _ = ((a + (i : ℤ) : ℤ) : ZMod m) := (Int.cast_add a (i : ℤ)).symm

/-- Manuscript Lemma 2.3 for every smaller positive modulus, including m=1. -/
theorem projection_gap (W : Finset ℤ) (hW : W.Nonempty) (k m : ℕ) [NeZero m]
    (hs : (m : ℤ) ≤ span W hW) (hg : gap W ≤ k) :
    CyclicGaps.gap (residues W m) (residues_nonempty W hW m) ≤ k-1 := by
  have he := encloses_min_max W hW
  have hmpos : 0 < m := NeZero.pos m
  have hlt : W.min' hW < W.max' hW := by unfold span at hs; omega
  have hk := lt_of_lt_of_le (gap_positive_of_encloses W _ _ he hlt) hg
  have hm := meshOn_of_gap_le W _ _ k he hk hg
  apply (CyclicGaps.gap_le_iff _ _ _).2
  exact projection_window_bound W _ _ k m hm hs

/-- Successive legal choices of whether to add each future weight. -/
def extend (W : Finset ℤ) (c : ℕ → ℤ) : ℕ → Finset ℤ
  | 0 => W
  | n+1 => extend W c n ∪ translate (extend W c n) (c n)

theorem extend_nonempty (W : Finset ℤ) (hW : W.Nonempty) (c : ℕ → ℤ) :
    ∀ n, (extend W c n).Nonempty
  | 0 => hW
  | n+1 => translate_union_nonempty _ (extend_nonempty W hW c n) (c n)

/-- The consequence following Lemma 2.2: the gap bound propagates for every future step. -/
theorem propagate_iterate (W : Finset ℤ) (hW : W.Nonempty) (c : ℕ → ℤ) (k : ℕ)
    (hc : ∀ n, 0 < c n) (hd : ∀ n, c (n+1) ≤ 2*c n)
    (hs : c 0 ≤ span W hW) (hg : gap W ≤ k) :
    ∀ n, gap (extend W c n) ≤ k ∧
      c n ≤ span (extend W c n) (extend_nonempty W hW c n) ∧
      span (extend W c n) (extend_nonempty W hW c n) = span W hW + ∑ i ∈ Finset.range n, c i := by
  intro n
  induction n with
  | zero => simpa [extend] using And.intro hg hs
  | succ n ih =>
    obtain ⟨hu, hspan⟩ := translate_union_gap_span (extend W c n)
      (extend_nonempty W hW c n) (c n) k (hc n) ih.2.1 ih.1
    change gap (extend W c n ∪ translate (extend W c n) (c n)) ≤ k ∧ _
    refine ⟨hu, ?_, ?_⟩
    · change c (n+1) ≤ span (extend W c n ∪ translate (extend W c n) (c n)) _
      rw [hspan]
      have := hd n
      have := ih.2.1
      omega
    · change span (extend W c n ∪ translate (extend W c n) (c n)) _ = _
      rw [hspan, ih.2.2, Finset.sum_range_succ]
      omega

end Mesh
end Dyadic354
