import Dyadic354.NodeRepresentations
import Dyadic354.CertificateData
import Dyadic354.Mesh

namespace Dyadic354.InitialMesh

open NodeRepresentations

def threshold (p q : ℤ) : ℤ := 2 * q * (p - 1) + 4 * (p + q) + 64

def leftEnd (d K p q S : ℤ) : ℤ := d * K * (p + 2 * q) + margin d p q S
def rightEnd (d K p q S : ℤ) : ℤ := d * K * (7 * p + 6 * q) - margin d p q S

theorem margin_budget (d K p q S : ℤ) (hd : 0 < d)
    (hS : S ≤ d * (p + q) - 1) (hK : threshold p q ≤ K) :
    64 * d - 42 ≤ d * K - 2 * margin d p q S ∧
    22 * d ≤ d * K - 2 * margin d p q S := by
  have hmul := mul_le_mul_of_nonneg_left hK (le_of_lt hd)
  dsimp [threshold] at hmul
  dsimp [margin]
  constructor <;> nlinarith

/-- Scale and trim the verified chain. Integer strictness pays for one unit
before scaling; no monotonicity of the sequence of endpoints is assumed. -/
theorem trimmed_chain_covers (t : Certificate.Template) (p q Q B a : ℤ) (k : ℕ)
    (ht : Certificate.ChainMeaning t p q) (hQ : 0 ≤ Q)
    (hbudget : (k : ℤ) - 1 ≤ Q - 2 * B)
    (halo : Q * (p + 2 * q) + B ≤ a)
    (hahi : a + (k : ℤ) - 1 ≤ Q * (7 * p + 6 * q) - B) :
    ∃ i : Fin t.chain.length,
      Q * (Certificate.nodeAt t i.val).lo.eval p q + B ≤ a ∧
      a + (k : ℤ) - 1 ≤ Q * (Certificate.nodeAt t i.val).hi.eval p q - B := by
  obtain ⟨hn, _, hlinks, hfirst, hlast, _⟩ := ht
  have links : ∀ i < t.chain.length - 1,
      Q * (Certificate.nodeAt t (i + 1)).lo.eval p q + B ≤
      Q * (Certificate.nodeAt t i).hi.eval p q - B - (k : ℤ) + 1 := by
    intro i hi
    have hlink := (hlinks ⟨i, hi⟩).1
    change (Certificate.nodeAt t (i + 1)).lo.eval p q <
      (Certificate.nodeAt t i).hi.eval p q at hlink
    have hsep : (Certificate.nodeAt t (i + 1)).lo.eval p q + 1 ≤
        (Certificate.nodeAt t i).hi.eval p q := by omega
    have hmul := mul_le_mul_of_nonneg_left hsep hQ
    nlinarith
  have hstart : Q * (Certificate.nodeAt t 0).lo.eval p q + B ≤ a := by
    have hmul := mul_le_mul_of_nonneg_left hfirst hQ
    omega
  have hend : a ≤ Q * (Certificate.nodeAt t (t.chain.length - 1)).hi.eval p q - B -
      (k : ℤ) + 1 := by
    have hmul := mul_le_mul_of_nonneg_left hlast hQ
    omega
  obtain ⟨i, hi, hil, hiu⟩ := Certificate.interval_chain_covers
    (fun i => Q * (Certificate.nodeAt t i).lo.eval p q + B)
    (fun i => Q * (Certificate.nodeAt t i).hi.eval p q - B - (k : ℤ) + 1)
    (t.chain.length - 1) links a hstart hend
  refine ⟨⟨i, by omega⟩, hil, ?_⟩
  change a + (k : ℤ) - 1 ≤ Q * (Certificate.nodeAt t i).hi.eval p q - B
  omega

theorem chain_windows (n ℓ d : ℕ) [NeZero d] (old : Fin (2 * n) → ℤ)
    (t : Certificate.Template) (third : Certificate.Digits) (p q S a : ℤ) (k : ℕ)
    (hq : 0 < q) (hqp : q < p) (hK : p ≤ (2 : ℤ) ^ ℓ) (hcop : IsCoprime p q)
    (hbounds : ∀ f, IsSubsetSum old f → 0 ≤ f ∧ f ≤ S)
    (ht : Certificate.ChainMeaning t p q) (hk : 0 < k)
    (hg : CyclicGaps.gap (oldResidues n d old) (oldResidues_nonempty n d old) ≤ k)
    (hbudget : (k : ℤ) - 1 ≤ (d : ℤ) * (2 : ℤ) ^ ℓ - 2 * margin d p q S)
    (halo : leftEnd d (2 ^ ℓ) p q S ≤ a)
    (hahi : a + (k : ℤ) - 1 ≤ rightEnd d (2 ^ ℓ) p q S) :
    ∃ z, IsSubsetSum (Representations.packedWeights n ℓ old t.first t.second third d p q) z ∧
      a ≤ z ∧ z < a + (k : ℤ) := by
  obtain ⟨i, hil, hiu⟩ := trimmed_chain_covers t p q (d * (2 : ℤ) ^ ℓ)
    (margin d p q S) a k ht (by positivity) hbudget halo hahi
  exact node_window n ℓ d old t.first t.second third (Certificate.nodeAt t i.val)
    p q S a k hq hqp hK hcop hbounds (ht.2.1 i) hk hg hil hiu

/-- Turn window hitting into the manuscript's actual finite mesh, not an
abstract periodic set. Both endpoint losses are explicitly bounded by k-1. -/
theorem mesh_from_windows (P : Finset ℤ) (lo hi : ℤ) (k : ℕ)
    (hlen : lo + (k : ℤ) - 1 ≤ hi)
    (hw : ∀ a : ℤ, lo ≤ a → a + (k : ℤ) - 1 ≤ hi →
      ∃ z ∈ P, a ≤ z ∧ z < a + (k : ℤ)) :
    let W := P.filter (fun z => lo ≤ z ∧ z ≤ hi)
    ∃ hW : W.Nonempty, W.min' hW ≤ lo + (k : ℤ) - 1 ∧
      hi - (k : ℤ) + 1 ≤ W.max' hW ∧ Mesh.gap W ≤ k ∧
      hi - lo - 2 * ((k : ℤ) - 1) ≤ Mesh.span W hW := by
  let W := P.filter (fun z => lo ≤ z ∧ z ≤ hi)
  change ∃ hW : W.Nonempty, W.min' hW ≤ lo + (k : ℤ) - 1 ∧
    hi - (k : ℤ) + 1 ≤ W.max' hW ∧ Mesh.gap W ≤ k ∧
    hi - lo - 2 * ((k : ℤ) - 1) ≤ Mesh.span W hW
  obtain ⟨u, hu, hlu, huk⟩ := hw lo (le_refl _) hlen
  have huW : u ∈ W := Finset.mem_filter.mpr ⟨hu, hlu, by omega⟩
  have hW : W.Nonempty := ⟨u, huW⟩
  obtain ⟨v, hv, hlv, hvk⟩ := hw (hi - (k : ℤ) + 1) (by omega) (by omega)
  have hvW : v ∈ W := Finset.mem_filter.mpr ⟨hv, by omega, by omega⟩
  have hmin := W.min'_le u huW
  have hmax := W.le_max' v hvW
  refine ⟨hW, by omega, by omega, ?_, ?_⟩
  · apply (Mesh.gap_le_iff W k).mpr
    intro a b hab
    have ha := (Finset.mem_filter.mp hab.1).2
    have hb := (Finset.mem_filter.mp hab.2.1).2
    by_cases hfit : a + (k : ℤ) ≤ hi
    · obtain ⟨z, hz, haz, hzk⟩ := hw (a + 1) (by omega) (by omega)
      have hzW : z ∈ W := Finset.mem_filter.mpr ⟨hz, by omega, by omega⟩
      have hbz := hab.2.2.2 z hzW (by omega)
      omega
    · omega
  · dsimp [Mesh.span]
    omega

/-- The manuscript's numerical surplus is strictly positive even for d=1.
This also guarantees that the global interval contains a complete k-window. -/
theorem span_budget (d K p q S : ℤ) (k : ℕ) (hd : 0 < d)
    (hq : 0 < q) (hqp : q < p) (hK : 0 ≤ K) (hk : (k : ℤ) ≤ d)
    (hbudget : 22 * d ≤ d * K - 2 * margin d p q S) :
    leftEnd d K p q S + (k : ℤ) - 1 ≤ rightEnd d K p q S ∧
    8 * d * K * q + 15 <
      rightEnd d K p q S - leftEnd d K p q S - 2 * ((k : ℤ) - 1) := by
  have hQ : 0 ≤ d * K := mul_nonneg (le_of_lt hd) hK
  have hsep : 1 ≤ 6 * p - 4 * q := by omega
  have hmul := mul_le_mul_of_nonneg_left hsep hQ
  have hweight : 0 ≤ d * K * q := mul_nonneg hQ (le_of_lt hq)
  dsimp [leftEnd, rightEnd]
  constructor <;> nlinarith

/-- The original 12-template certificate now constructs a mesh of actual
finite subset sums, with enough span for the first future weight. The inputs
are precisely the local exact-block algebraic hypotheses, not FE/DB/BG. -/
theorem certificate_initial_mesh (n ℓ d : ℕ) [NeZero d] (old : Fin (2 * n) → ℤ)
    (first second third : Certificate.Digits) (p q : ℤ)
    (hfirst : first ≠ (false, false)) (hq : 0 < q) (hqp : q < p) (hpq : p < 2 * q)
    (hcop : IsCoprime p q) (hpos : ∀ i, 0 ≤ old i)
    (hS : (∑ i, old i) < (d : ℤ) * (p + q))
    (hK : threshold p q ≤ (2 : ℤ) ^ ℓ) :
    let S := ∑ i, old i
    let k := max 1 (CyclicGaps.gap (oldResidues n d old) (oldResidues_nonempty n d old))
    let P := finiteSubsetSums (Representations.packedWeights n ℓ old first second third d p q)
      Finset.univ
    let W := P.filter (fun z => leftEnd d (2 ^ ℓ) p q S ≤ z ∧ z ≤ rightEnd d (2 ^ ℓ) p q S)
    ∃ hW : W.Nonempty, Mesh.gap W ≤ k ∧
      rightEnd d (2 ^ ℓ) p q S - leftEnd d (2 ^ ℓ) p q S - 2 * ((k : ℤ) - 1) ≤
        Mesh.span W hW ∧
      8 * (d : ℤ) * (2 : ℤ) ^ ℓ * q + 15 < Mesh.span W hW := by
  let S := ∑ i, old i
  let k := max 1 (CyclicGaps.gap (oldResidues n d old) (oldResidues_nonempty n d old))
  let P := finiteSubsetSums (Representations.packedWeights n ℓ old first second third d p q)
    Finset.univ
  have hd : (0 : ℤ) < d := by exact_mod_cast NeZero.pos d
  have hk : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hgd := CyclicGaps.gap_lt_modulus (oldResidues n d old) (oldResidues_nonempty n d old)
  have hkd : (k : ℤ) ≤ d := by dsimp [k]; omega
  have hg : CyclicGaps.gap (oldResidues n d old) (oldResidues_nonempty n d old) ≤ k :=
    le_max_right _ _
  have hbudget := (margin_budget d (2 ^ ℓ) p q S hd (by omega) hK).2
  have hKp : p ≤ (2 : ℤ) ^ ℓ := by
    have hprod : 0 ≤ q * (p - 1) := mul_nonneg (le_of_lt hq) (by omega)
    dsimp [threshold] at hK
    nlinarith
  have hb := span_budget d (2 ^ ℓ) p q S k hd hq hqp (by positivity) hkd hbudget
  have hw : ∀ a : ℤ, leftEnd d (2 ^ ℓ) p q S ≤ a →
      a + (k : ℤ) - 1 ≤ rightEnd d (2 ^ ℓ) p q S →
      ∃ z ∈ P, a ≤ z ∧ z < a + (k : ℤ) := by
    intro a halo hahi
    obtain ⟨t, _, hf, hs, ht⟩ := Certificate.certificate_correct first second hfirst p q hq hqp hpq
    obtain ⟨z, hz, hza, hzk⟩ := chain_windows n ℓ d old t third p q S a k hq hqp hKp hcop
      (old_sum_bounds n old hpos) ht hk hg (by omega) halo hahi
    rw [hf, hs] at hz
    obtain ⟨s, he⟩ := hz
    exact ⟨z, (mem_finiteSubsetSums _ _ _).mpr ⟨s, Finset.subset_univ _, he⟩, hza, hzk⟩
  obtain ⟨hW, _, _, hgap, hspan⟩ := mesh_from_windows P
    (leftEnd d (2 ^ ℓ) p q S) (rightEnd d (2 ^ ℓ) p q S) k hb.1 hw
  exact ⟨hW, hgap, hspan, lt_of_lt_of_le hb.2 hspan⟩

/-- Original-prefix version. The exact doubling identities and six following
weights are explicit hypotheses to be obtained from the floor recurrence.
Every resulting mesh point uses a finite set of original indices once each. -/
theorem prefix_initial_mesh (n ℓ d : ℕ) [NeZero d] (v : ℕ → ℤ)
    (first second third : Certificate.Digits) (p q : ℤ)
    (hfirst : first ≠ (false, false)) (hq : 0 < q) (hqp : q < p) (hpq : p < 2 * q)
    (hcop : IsCoprime p q) (hpos : ∀ i : Fin (2 * n), 0 ≤ v i.val)
    (hS : (∑ i : Fin (2 * n), v i.val) < (d : ℤ) * (p + q))
    (hK : threshold p q ≤ (2 : ℤ) ^ ℓ)
    (ha : ∀ i : Fin ℓ, v (2 * n + 2 * i.val) = (d : ℤ) * p * 2 ^ i.val)
    (hb : ∀ i : Fin ℓ, v (2 * n + 2 * i.val + 1) = (d : ℤ) * q * 2 ^ i.val)
    (hsix : ∀ i : Fin 6, v (2 * n + 2 * ℓ + i.val) =
      Certificate.weights first second third d (2 ^ ℓ) p q i) :
    let old : Fin (2 * n) → ℤ := fun i => v i.val
    let k := max 1 (CyclicGaps.gap (oldResidues n d old) (oldResidues_nonempty n d old))
    ∃ W : Finset ℤ, ∃ hW : W.Nonempty,
      W ⊆ finiteSubsetSums v (Finset.range (2 * (n + ℓ + 3))) ∧
      Mesh.gap W ≤ k ∧ 8 * (d : ℤ) * (2 : ℤ) ^ ℓ * q + 15 < Mesh.span W hW := by
  let old : Fin (2 * n) → ℤ := fun i => v i.val
  let P := finiteSubsetSums (Representations.packedWeights n ℓ old first second third d p q)
    Finset.univ
  let W := P.filter (fun z => leftEnd d (2 ^ ℓ) p q (∑ i, old i) ≤ z ∧
    z ≤ rightEnd d (2 ^ ℓ) p q (∑ i, old i))
  obtain ⟨hW, hgap, _, hspan⟩ := certificate_initial_mesh n ℓ d old first second third p q
    hfirst hq hqp hpq hcop hpos hS hK
  refine ⟨W, hW, ?_, hgap, hspan⟩
  intro z hz
  have hzP : z ∈ P := (Finset.mem_filter.mp hz).1
  obtain ⟨s, _, he⟩ := (mem_finiteSubsetSums _ _ _).mp hzP
  exact Representations.packed_to_prefix n ℓ old first second third d p q v
    (Representations.packed_weights_match n ℓ v first second third d p q ha hb hsix) z ⟨s, he⟩

end Dyadic354.InitialMesh
