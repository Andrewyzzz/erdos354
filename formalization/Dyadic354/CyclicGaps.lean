import Dyadic354.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Find

namespace Dyadic354
namespace CyclicGaps

/-- Every block of h+1 consecutive integers meets S. -/
def GapBound (S : Set ℤ) (h : ℕ) : Prop :=
  ∀ a : ℤ, ∃ i : ℕ, i ≤ h ∧ a + (i : ℤ) ∈ S

/-- An actual consecutive missing run; length zero is always possible. -/
def MissingRun (S : Set ℤ) (r : ℕ) : Prop :=
  ∃ a : ℤ, ∀ i : ℕ, i < r → a + (i : ℤ) ∉ S

theorem gapBound_mono {S : Set ℤ} {h k : ℕ} (hS : GapBound S h) (hk : h ≤ k) :
    GapBound S k := by
  intro a
  obtain ⟨i, hi, hm⟩ := hS a
  exact ⟨i, le_trans hi hk, hm⟩

theorem not_missingRun_iff (S : Set ℤ) (h : ℕ) :
    ¬ MissingRun S (h+1) ↔ GapBound S h := by
  classical
  simp [MissingRun, GapBound]

def erodeSet (S : Set ℤ) : Set ℤ := S ∪ {z | z - 1 ∈ S}

/-- One-step erosion removes exactly one missing position from every nonempty run. -/
theorem gapBound_erode_iff (S : Set ℤ) (h : ℕ) :
    GapBound (erodeSet S) h ↔ GapBound S (h+1) := by
  constructor
  · intro he a
    obtain ⟨i, hi, hm⟩ := he (a+1)
    rcases hm with hm | hm
    · refine ⟨i+1, by omega, ?_⟩
      convert hm using 1
      push_cast
      ring
    · refine ⟨i, by omega, ?_⟩
      change a+1+(i : ℤ)-1 ∈ S at hm
      convert hm using 1
      ring
  · intro hs a
    obtain ⟨i, hi, hm⟩ := hs (a-1)
    by_cases hz : i = 0
    · refine ⟨0, by omega, Or.inr ?_⟩
      simpa [hz] using hm
    · refine ⟨i-1, by omega, Or.inl ?_⟩
      have heq : a + ((i-1 : ℕ) : ℤ) = a-1+(i : ℤ) := by omega
      simpa only [heq] using hm

def lift {d : ℕ} (X : Finset (ZMod d)) : Set ℤ := {z | (z : ZMod d) ∈ X}

theorem modulus_bound {d : ℕ} [NeZero d] (X : Finset (ZMod d)) (hX : X.Nonempty) :
    GapBound (lift X) (d-1) := by
  intro a
  obtain ⟨x, hx⟩ := hX
  let r : ZMod d := x - (a : ZMod d)
  refine ⟨r.val, by have := ZMod.val_lt r; omega, ?_⟩
  change ((a + (r.val : ℤ) : ℤ) : ZMod d) ∈ X
  simpa [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val, r] using hx

/-- The least bound is the longest cyclic missing run, as proved below. -/
noncomputable def gap {d : ℕ} [NeZero d] (X : Finset (ZMod d)) (hX : X.Nonempty) : ℕ :=
  @Nat.find (fun h => GapBound (lift X) h) (Classical.decPred _)
    ⟨d-1, modulus_bound X hX⟩

theorem gap_spec {d : ℕ} [NeZero d] (X : Finset (ZMod d)) (hX : X.Nonempty) :
    GapBound (lift X) (gap X hX) := by
  classical
  exact Nat.find_spec ⟨d-1, modulus_bound X hX⟩

theorem gap_le_iff {d : ℕ} [NeZero d] (X : Finset (ZMod d)) (hX : X.Nonempty) (h : ℕ) :
    gap X hX ≤ h ↔ GapBound (lift X) h := by
  classical
  constructor
  · exact gapBound_mono (gap_spec X hX)
  · exact Nat.find_min' ⟨d-1, modulus_bound X hX⟩

theorem gap_lt_modulus {d : ℕ} [NeZero d] (X : Finset (ZMod d)) (hX : X.Nonempty) :
    gap X hX < d := by
  have h := (gap_le_iff X hX (d-1)).2 (modulus_bound X hX)
  have hd : 0 < d := NeZero.pos d
  omega

/-- This establishes the connection with actual consecutive missing runs, not just a new definition. -/
theorem missingRun_iff_le_gap {d : ℕ} [NeZero d]
    (X : Finset (ZMod d)) (hX : X.Nonempty) (r : ℕ) :
    MissingRun (lift X) r ↔ r ≤ gap X hX := by
  classical
  cases r with
  | zero => simp [MissingRun]
  | succ r =>
    have hb := gap_le_iff X hX r
    have hn := not_missingRun_iff (lift X) r
    constructor
    · intro hm
      have : ¬ gap X hX ≤ r := fun h => (hn.mpr (hb.mp h)) hm
      omega
    · intro hr
      by_contra hm
      have := hb.mpr (hn.mp hm)
      omega

def erode {d : ℕ} (X : Finset (ZMod d)) : Finset (ZMod d) :=
  X ∪ X.image (fun x => x+1)

theorem erode_nonempty {d : ℕ} (X : Finset (ZMod d)) (hX : X.Nonempty) :
    (erode X).Nonempty := by
  obtain ⟨x, hx⟩ := hX
  exact ⟨x, Finset.mem_union_left _ hx⟩

theorem lift_erode {d : ℕ} (X : Finset (ZMod d)) :
    lift (erode X) = erodeSet (lift X) := by
  ext z
  change (z : ZMod d) ∈ X ∪ X.image (fun x => x+1) ↔
    (z : ZMod d) ∈ X ∨ ((z-1 : ℤ) : ZMod d) ∈ X
  simp only [Finset.mem_union, Finset.mem_image, Int.cast_sub, Int.cast_one]
  constructor
  · rintro (hz | ⟨x, hx, he⟩)
    · exact Or.inl hz
    · right
      have : (z : ZMod d)-1 = x := by rw [← he]; ring
      rwa [this]
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr ⟨(z : ZMod d)-1, hz, by ring⟩

/-- Manuscript Lemma 2.1, with natural subtraction implementing max(0,h-1). -/
theorem erosion_exact {d : ℕ} [NeZero d] (X : Finset (ZMod d)) (hX : X.Nonempty) :
    gap (erode X) (erode_nonempty X hX) = gap X hX - 1 := by
  have hb : ∀ h, GapBound (lift (erode X)) h ↔ GapBound (lift X) (h+1) := by
    intro h
    rw [lift_erode]
    exact gapBound_erode_iff (lift X) h
  apply Nat.le_antisymm
  · apply (gap_le_iff _ _ _).2
    apply (hb _).2
    exact gapBound_mono (gap_spec X hX) (by omega)
  · have he := (hb _).1 (gap_spec (erode X) (erode_nonempty X hX))
    have := (gap_le_iff X hX _).2 he
    omega

theorem gap_eq_zero_iff_full {d : ℕ} [NeZero d]
    (X : Finset (ZMod d)) (hX : X.Nonempty) : gap X hX = 0 ↔ X = Finset.univ := by
  constructor
  · intro hg
    apply Finset.eq_univ_of_forall
    intro x
    have hb := gap_spec X hX
    rw [hg] at hb
    obtain ⟨i, hi, hm⟩ := hb (x.val : ℤ)
    have hz : i = 0 := by omega
    simpa [lift, hz, ZMod.natCast_zmod_val] using hm
  · intro hf
    apply Nat.eq_zero_of_le_zero
    apply (gap_le_iff X hX 0).2
    intro a
    exact ⟨0, le_refl _, by simp [lift, hf]⟩

theorem gap_modulus_one (X : Finset (ZMod 1)) (hX : X.Nonempty) : gap X hX = 0 := by
  have := gap_lt_modulus X hX
  omega

end CyclicGaps
end Dyadic354
