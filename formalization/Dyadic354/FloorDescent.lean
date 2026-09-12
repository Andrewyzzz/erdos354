import Dyadic354.PairReindex
import Dyadic354.ExactBlock
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Fintype.BigOperators

namespace Dyadic354.FloorDescent

open FloorSequence

/-- The actual prefix indexed by natural numbers equals the finite-type
version used by the certificate, including repeated values at distinct indices. -/
theorem fin_prefix_iff (v : ℕ → ℤ) (N : ℕ) (z : ℤ) :
    IsSubsetSum (fun i : Fin N => v i.val) z ↔ z ∈ PermanentMesh.prefixSums v N := by
  constructor
  · exact Representations.subsetSum_embed _ v Fin.val Fin.val_injective (fun _ => rfl)
      (Finset.range N) (fun i => Finset.mem_range.mpr i.isLt) z
  · intro hz
    obtain ⟨s, hs, he⟩ := (mem_finiteSubsetSums _ _ _).mp hz
    let e : {i // i ∈ s} → Fin N := fun i => ⟨i.val, Finset.mem_range.mp (hs i.property)⟩
    have hi : Function.Injective e := by
      intro i j hij
      exact Subtype.ext (congrArg Fin.val hij)
    refine ⟨s.attach.image e, ?_⟩
    rw [Finset.sum_image (fun i _ j _ hij => hi hij)]
    change z = ∑ i ∈ s.attach, v i.val
    rwa [Finset.sum_attach]

theorem oldResidues_prefix (v : ℕ → ℤ) (n d : ℕ) :
    NodeRepresentations.oldResidues n d (fun i => v i.val) =
      Mesh.residues (PermanentMesh.prefixSums v (2 * n)) d := by
  have h : finiteSubsetSums (fun i : Fin (2 * n) => v i.val) Finset.univ =
      PermanentMesh.prefixSums v (2 * n) := by
    ext z
    rw [mem_finiteSubsetSums, ← fin_prefix_iff]
    constructor
    · rintro ⟨s, _, he⟩
      exact ⟨s, he⟩
    · rintro ⟨s, he⟩
      exact ⟨s, Finset.subset_univ _, he⟩
  unfold NodeRepresentations.oldResidues Mesh.residues
  rw [h]

noncomputable def modulus (α β : ℝ) (n : ℕ) : ℕ := Int.gcd (term α n) (term β n)
noncomputable def pCoord (α β : ℝ) (n : ℕ) : ℤ := term α n / (modulus α β n : ℤ)
noncomputable def qCoord (α β : ℝ) (n : ℕ) : ℤ := term β n / (modulus α β n : ℤ)

theorem modulus_positive (α β : ℝ) (n : ℕ) (hb : 0 < term β n) : 0 < modulus α β n :=
  Int.gcd_pos_of_ne_zero_right _ (ne_of_gt hb)

theorem gcd_coordinates (α β : ℝ) (n : ℕ)
    (hb : 0 < term β n) (hba : term β n < term α n) (hab : term α n < 2 * term β n) :
    0 < qCoord α β n ∧ qCoord α β n < pCoord α β n ∧
    pCoord α β n < 2 * qCoord α β n ∧ IsCoprime (pCoord α β n) (qCoord α β n) ∧
    term α n = (modulus α β n : ℤ) * pCoord α β n ∧
    term β n = (modulus α β n : ℤ) * qCoord α β n := by
  have hD := modulus_positive α β n hb
  have hd : (0 : ℤ) < modulus α β n := by exact_mod_cast hD
  have ha : term α n = (modulus α β n : ℤ) * pCoord α β n := by
    dsimp [modulus, pCoord]
    rw [mul_comm, Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)]
  have hb' : term β n = (modulus α β n : ℤ) * qCoord α β n := by
    dsimp [modulus, qCoord]
    rw [mul_comm, Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_, ha, hb'⟩
  exact Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_ediv_gcd_ediv_gcd hD)

/-- Actual cyclic gap of the original paired prefix at its current gcd.
The positivity proof only excludes the undefined zero-modulus case. -/
noncomputable def gapAt (α β : ℝ) (n : ℕ) (hb : 0 < term β n) : ℕ :=
  letI : NeZero (modulus α β n) := ⟨ne_of_gt (modulus_positive α β n hb)⟩
  CyclicGaps.gap (Mesh.residues (PermanentMesh.prefixSums (interleave α β 2) (2 * n))
    (modulus α β n)) (Mesh.residues_nonempty _ (PermanentMesh.prefix_nonempty _ _) _)

theorem interleave_positive (α β : ℝ)
    (hb : 0 < term β 0) (hba : term β 0 < term α 0) (hab : term α 0 < 2 * term β 0) :
    ∀ j, 0 < interleave α β 2 j := by
  intro j
  have hn := normalized_bounds α β hb hba hab (j / 2)
  rcases PairReindex.index_cases j with h | h
  · rw [h, interleave_even]
    exact lt_trans hn.1 hn.2.1
  · rw [h, interleave_odd]
    exact hn.1

/-- The local permanent descent theorem for actual dyadic floor sequences.
All old-sum, gcd, six-mask and sorted-future hypotheses are now derived.
The existence of a sufficiently long block is NOT assumed to have been proved. -/
theorem long_block_descent (α β : ℝ) (n ℓ : ℕ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hℓ : 0 < ℓ)
    (hzero : ∀ i, i + 1 < ℓ → ExactBlock.digits α β (n + i) = (false, false))
    (hevent : ExactBlock.IsEvent α β (n + ℓ))
    (hK : InitialMesh.threshold (pCoord α β n) (qCoord α β n) ≤ (2 : ℤ) ^ ℓ) :
    ∀ t, n + ℓ + 3 ≤ t →
      gapAt α β t (normalized_bounds α β hb0 hba0 hab0 t).1 ≤
        gapAt α β n (normalized_bounds α β hb0 hba0 hab0 n).1 - 1 := by
  let d := modulus α β n
  let p := pCoord α β n
  let q := qCoord α β n
  let r := n + ℓ + 3
  have hn := normalized_bounds α β hb0 hba0 hab0 n
  letI : NeZero d := ⟨ne_of_gt (modulus_positive α β n hn.1)⟩
  obtain ⟨hq, hqp, hpq, hcop, ha, hb⟩ := gcd_coordinates α β n hn.1 hn.2.1 hn.2.2
  have hza : ∀ i, i + 1 < ℓ → bit α (n + i) = false := by
    intro i hi
    exact congrArg Prod.fst (hzero i hi)
  have hzb : ∀ i, i + 1 < ℓ → bit β (n + i) = false := by
    intro i hi
    exact congrArg Prod.snd (hzero i hi)
  have hsum : (∑ i : Fin (2 * n), interleave α β 2 i.val) < (d : ℤ) * (p + q) := by
    rw [Fin.sum_univ_eq_sum_range]
    have hs := paired_prefix_lt α β (lt_trans hb0 hba0) hb0 n
    rw [ha, hb] at hs
    dsimp [d, p, q]
    nlinarith [hs]
  have hblock := ExactBlock.interleave_block α β n ℓ d p q ha hb hza hzb
  have hsix := ExactBlock.six_after_exact_block α β n ℓ d p q hℓ ha hb hza hzb
  obtain ⟨W, hW, hsub, hgap, hspan⟩ := InitialMesh.prefix_initial_mesh n ℓ d
    (interleave α β 2) (ExactBlock.digits α β (n + ℓ - 1))
    (ExactBlock.digits α β (n + ℓ)) (ExactBlock.digits α β (n + ℓ + 1)) p q
    hevent.2 hq hqp hpq hcop
    (fun i => le_of_lt (interleave_positive α β hb0 hba0 hab0 i.val))
    hsum hK hblock.1 hblock.2 hsix
  have hsub' : W ⊆ PermanentMesh.prefixSums (PairReindex.sortedTail α β r) (2 * r) := by
    change W ⊆ PermanentMesh.prefixSums (fun j => interleave α β 2 (PairReindex.swapAfter r j)) (2 * r)
    rw [PairReindex.prefixSums_reindex]
    exact hsub
  have hnext : PairReindex.sortedTail α β r (2 * r) ≤ Mesh.span W hW := by
    have hs := ExactBlock.next_small_weight_bound β n ℓ d q hℓ hb hzb
    have he := PairReindex.sortedTail_even α β r 0
    simp only [Nat.mul_zero, Nat.add_zero] at he
    rw [he]
    exact le_trans hs (le_of_lt hspan)
  intro t hrt
  have ht := normalized_bounds α β hb0 hba0 hab0 t
  letI : NeZero (modulus α β t) := ⟨ne_of_gt (modulus_positive α β t ht.1)⟩
  have hmt : (modulus α β t : ℤ) ≤ PairReindex.sortedTail α β r (2 * r + 2 * (t - r)) := by
    rw [PairReindex.sortedTail_even, Nat.add_sub_of_le hrt]
    exact Int.gcd_le_right _ ht.1
  have hp' := PermanentMesh.permanent_projection (PairReindex.sortedTail α β r) (2 * r)
    W hW _ hsub' hgap hnext (PairReindex.sortedTail_positive α β r hb0 hba0 hab0)
    (PairReindex.sortedTail_doubling α β r hb0 hba0 hab0)
    (2 * (t - r)) (modulus α β t) inferInstance hmt
  have hidx : 2 * r + 2 * (t - r) = 2 * t := by omega
  rw [hidx] at hp'
  change CyclicGaps.gap (Mesh.residues
    (PermanentMesh.prefixSums (fun j => interleave α β 2 (PairReindex.swapAfter r j)) (2 * t))
    (modulus α β t)) _ ≤ _ at hp'
  simp only [PairReindex.prefixSums_reindex, oldResidues_prefix] at hp'
  change gapAt α β t ht.1 ≤ max 1 (gapAt α β n hn.1) - 1 at hp'
  have heq : max 1 (gapAt α β n hn.1) - 1 = gapAt α β n hn.1 - 1 := by omega
  rwa [heq] at hp'

/-- Arrival-indexed version: the next event after n occurs at m. The effective
update starts at m+3, not at m or m+1. -/
theorem next_event_descent (α β : ℝ) (n m : ℕ)
    (hb0 : 0 < term β 0) (hba0 : term β 0 < term α 0) (hab0 : term α 0 < 2 * term β 0)
    (hnm : n < m) (hno : ∀ t, n < t → t < m → ¬ ExactBlock.IsEvent α β t)
    (hm : ExactBlock.IsEvent α β m)
    (hK : InitialMesh.threshold (pCoord α β n) (qCoord α β n) ≤ (2 : ℤ) ^ (m - n)) :
    ∀ t, m + 3 ≤ t →
      gapAt α β t (normalized_bounds α β hb0 hba0 hab0 t).1 ≤
        gapAt α β n (normalized_bounds α β hb0 hba0 hab0 n).1 - 1 := by
  have he : n + (m - n) = m := Nat.add_sub_of_le (le_of_lt hnm)
  have h := long_block_descent α β n (m - n) hb0 hba0 hab0 (by omega)
    (ExactBlock.no_events_zero_digits α β n m hno) (by rwa [he]) hK
  simpa only [he] using h

end Dyadic354.FloorDescent
