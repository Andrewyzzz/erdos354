import Dyadic354.CoefficientInterval
import Dyadic354.Certificate

/-! Legal finite-index representations, including an explicit injection into
the old prefix, exact doubling block, and following six original positions. -/

namespace Dyadic354.Representations

theorem subsetSum_disjSum {ι κ : Type*} (a : ι → ℤ) (b : κ → ℤ) (x y : ℤ)
    (hx : IsSubsetSum a x) (hy : IsSubsetSum b y) :
    IsSubsetSum (Sum.elim a b) (x + y) := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hy
  exact ⟨s.disjSum t, by simp [Finset.sum_disjSum, hs, ht]⟩

/-- Transfer along an injection preserves the no-repeated-index condition. -/
theorem subsetSum_embed {ι κ : Type*} [DecidableEq κ] (a : ι → ℤ) (b : κ → ℤ)
    (e : ι → κ) (he : Function.Injective e) (hw : ∀ i, b (e i) = a i)
    (s : Finset κ) (hb : ∀ i, e i ∈ s) (z : ℤ) (hz : IsSubsetSum a z) :
    z ∈ finiteSubsetSums b s := by
  obtain ⟨t, ht⟩ := hz
  apply (mem_finiteSubsetSums b s z).mpr
  refine ⟨t.image e, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hb j
  · rw [Finset.sum_image (fun i _ j _ hij => he hij)]
    simpa only [hw] using ht

theorem binary_scaled (ℓ : ℕ) (a x : ℤ) (hx0 : 0 ≤ x) (hx : x < (2 : ℤ) ^ ℓ) :
    IsSubsetSum (fun i : Fin ℓ => a * 2 ^ i.val) (a * x) := by
  have hxN : x.toNat < 2 ^ ℓ := by
    have hcast : (x.toNat : ℤ) < (2 : ℤ) ^ ℓ := by
      simpa only [Int.toNat_of_nonneg hx0] using hx
    exact_mod_cast hcast
  obtain ⟨s, hs, heq⟩ := CoefficientInterval.binary_sum_exists ℓ x.toNat hxN
  let e : {i // i ∈ s} → Fin ℓ := fun i => ⟨i.val, Finset.mem_range.mp (hs i.property)⟩
  have he : Function.Injective e := by
    intro i j hij
    exact Subtype.ext (congrArg Fin.val hij)
  refine ⟨s.attach.image e, ?_⟩
  rw [Finset.sum_image (fun i _ j _ hij => he hij), ← Finset.mul_sum]
  congr 1
  change x = ∑ i ∈ s.attach, (2 : ℤ) ^ i.val
  rw [Finset.sum_attach]
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) heq
  simpa only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat, Int.toNat_of_nonneg hx0] using hcast

abbrev BlockIndex (ℓ : ℕ) := Fin ℓ ⊕ Fin ℓ

def blockWeights (ℓ : ℕ) (d p q : ℤ) : BlockIndex ℓ → ℤ :=
  Sum.elim (fun i => d * p * 2 ^ i.val) (fun i => d * q * 2 ^ i.val)

/-- The entire coefficient interval is represented by distinct exact-block indices. -/
theorem block_interval (ℓ : ℕ) (d p q z : ℤ) (hq : 0 < q) (hqp : q < p)
    (hK : p ≤ (2 : ℤ) ^ ℓ) (hcop : IsCoprime p q)
    (hzlo : q * (p - 1) ≤ z)
    (hzhi : z ≤ (p + q) * ((2 : ℤ) ^ ℓ - 1) - q * (p - 1)) :
    IsSubsetSum (blockWeights ℓ d p q) (d * z) := by
  obtain ⟨x, y, hx0, hxK, hy0, hyK, heq⟩ :=
    CoefficientInterval.bounded_interval p q (2 ^ ℓ) z hq hqp hK hcop hzlo hzhi
  have h := subsetSum_disjSum _ _ _ _
    (binary_scaled ℓ (d * p) x hx0 hxK) (binary_scaled ℓ (d * q) y hy0 hyK)
  have heq' : d * p * x + d * q * y = d * z := by rw [← heq]; ring
  simpa only [blockWeights, heq'] using h

abbrev PackedIndex (n ℓ : ℕ) := Fin (2 * n) ⊕ (BlockIndex ℓ ⊕ Fin 6)

def packedWeights (n ℓ : ℕ) (old : Fin (2 * n) → ℤ)
    (first second third : Certificate.Digits) (d p q : ℤ) : PackedIndex n ℓ → ℤ :=
  Sum.elim old (Sum.elim (blockWeights ℓ d p q)
    (Certificate.weights first second third d (2 ^ ℓ) p q))

/-- These four alternatives occupy consecutive, pairwise disjoint index ranges. -/
def position (n ℓ : ℕ) : PackedIndex n ℓ → ℕ
  | .inl i => i.val
  | .inr (.inl (.inl i)) => 2 * n + 2 * i.val
  | .inr (.inl (.inr i)) => 2 * n + 2 * i.val + 1
  | .inr (.inr i) => 2 * n + 2 * ℓ + i.val

theorem position_injective (n ℓ : ℕ) : Function.Injective (position n ℓ) := by
  intro i j hij
  rcases i with i | ((i | i) | i) <;> rcases j with j | ((j | j) | j)
  all_goals simp only [position] at hij
  all_goals try simp only [Sum.inl.injEq, Sum.inr.injEq]
  all_goals first | (apply Fin.ext; omega) | omega

theorem position_lt (n ℓ : ℕ) (i : PackedIndex n ℓ) :
    position n ℓ i < 2 * (n + ℓ + 3) := by
  rcases i with i | ((i | i) | i) <;> simp only [position] <;> omega

theorem packed_weights_match (n ℓ : ℕ) (v : ℕ → ℤ)
    (first second third : Certificate.Digits) (d p q : ℤ)
    (ha : ∀ i : Fin ℓ, v (2 * n + 2 * i.val) = d * p * 2 ^ i.val)
    (hb : ∀ i : Fin ℓ, v (2 * n + 2 * i.val + 1) = d * q * 2 ^ i.val)
    (hsix : ∀ i : Fin 6, v (2 * n + 2 * ℓ + i.val) =
      Certificate.weights first second third d (2 ^ ℓ) p q i) :
    ∀ i, v (position n ℓ i) =
      packedWeights n ℓ (fun j => v j.val) first second third d p q i := by
  intro i
  rcases i with i | ((i | i) | i)
  · rfl
  · exact ha i
  · exact hb i
  · exact hsix i

/-- A local model becomes a genuine prefix subset sum when its weights match
the original sequence at the explicit positions; no collision is permitted. -/
theorem packed_to_prefix (n ℓ : ℕ) (old : Fin (2 * n) → ℤ)
    (first second third : Certificate.Digits) (d p q : ℤ) (v : ℕ → ℤ)
    (hw : ∀ i, v (position n ℓ i) = packedWeights n ℓ old first second third d p q i)
    (z : ℤ) (hz : IsSubsetSum (packedWeights n ℓ old first second third d p q) z) :
    z ∈ finiteSubsetSums v (Finset.range (2 * (n + ℓ + 3))) := by
  exact subsetSum_embed _ v (position n ℓ) (position_injective n ℓ) hw _
    (fun i => Finset.mem_range.mpr (position_lt n ℓ i)) z hz

theorem prefix_block_offset (n ℓ : ℕ) (old : Fin (2 * n) → ℤ)
    (first second third : Certificate.Digits) (d p q f u : ℤ) (mask tm : ℕ)
    (hf : IsSubsetSum old f) (hq : 0 < q) (hqp : q < p)
    (hK : p ≤ (2 : ℤ) ^ ℓ) (hcop : IsCoprime p q)
    (hulo : q * (p - 1) ≤ u)
    (huhi : u ≤ (p + q) * ((2 : ℤ) ^ ℓ - 1) - q * (p - 1)) :
    IsSubsetSum (packedWeights n ℓ old first second third d p q)
      (f + (d * u + (d * (2 : ℤ) ^ ℓ * (Certificate.coefficient mask tm).eval p q +
        Certificate.constant first second third mask tm))) := by
  exact subsetSum_disjSum _ _ _ _ hf (subsetSum_disjSum _ _ _ _
    (block_interval ℓ d p q u hq hqp hK hcop hulo huhi)
    (Certificate.offset_isSubsetSum first second third d (2 ^ ℓ) p q mask tm))

end Dyadic354.Representations
