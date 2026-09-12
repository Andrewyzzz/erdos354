import Dyadic354.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Dyadic354
namespace Certificate

abbrev Digits := Bool × Bool

def digit (b : Bool) : ℤ := if b then 1 else 0

/-- Positions 0,2,4 belong to the first column; 1,3,5 to the second. -/
def aCoeff : Fin 6 → ℤ := ![1, 0, 2, 0, 4, 0]
def bCoeff : Fin 6 → ℤ := ![0, 1, 0, 2, 0, 4]

def constants (first second third : Digits) : Fin 6 → ℤ :=
  ![digit first.1, digit first.2,
    2 * digit first.1 + digit second.1, 2 * digit first.2 + digit second.2,
    4 * digit first.1 + 2 * digit second.1 + digit third.1,
    4 * digit first.2 + 2 * digit second.2 + digit third.2]

/-- The first mask addresses four positions; the shared third mask addresses two. -/
def support (mask thirdMask : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter (fun i =>
    if i.val < 4 then mask.testBit i.val else thirdMask.testBit (i.val - 4))

def coefficient (mask thirdMask : ℕ) : Linear :=
  ⟨∑ i ∈ support mask thirdMask, aCoeff i, ∑ i ∈ support mask thirdMask, bCoeff i⟩

def constant (first second third : Digits) (mask thirdMask : ℕ) : ℤ :=
  ∑ i ∈ support mask thirdMask, constants first second third i

def weights (first second third : Digits) (d K p q : ℤ) (i : Fin 6) : ℤ :=
  d * K * (aCoeff i * p + bCoeff i * q) + constants first second third i

/-- Affine mask evaluation is exactly the sum on its original finite support. -/
theorem offset_eq_sum (first second third : Digits) (d K p q : ℤ) (mask tm : ℕ) :
    d * K * (coefficient mask tm).eval p q + constant first second third mask tm =
      ∑ i ∈ support mask tm, weights first second third d K p q i := by
  simp only [weights, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, coefficient, Linear.eval, constant]

theorem offset_isSubsetSum (first second third : Digits) (d K p q : ℤ) (mask tm : ℕ) :
    IsSubsetSum (weights first second third d K p q)
      (d * K * (coefficient mask tm).eval p q + constant first second third mask tm) :=
  ⟨support mask tm, offset_eq_sum first second third d K p q mask tm⟩

/-- This spells out the six actual weights from manuscript §3. -/
theorem weights_explicit (first second third : Digits) (d K p q : ℤ) :
    weights first second third d K p q =
      ![d*K*p + digit first.1, d*K*q + digit first.2,
        2*d*K*p + 2*digit first.1 + digit second.1,
        2*d*K*q + 2*digit first.2 + digit second.2,
        4*d*K*p + 4*digit first.1 + 2*digit second.1 + digit third.1,
        4*d*K*q + 4*digit first.2 + 2*digit second.2 + digit third.2] := by
  funext i
  fin_cases i <;> simp [weights, aCoeff, bCoeff, constants] <;> ring

structure Node where
  mask0 : ℕ
  mask1 : ℕ
  thirdMask : ℕ
  lo : Linear
  hi : Linear
  deriving DecidableEq, Repr, Inhabited

def unit : Linear := ⟨1, 1⟩

/-- Claimed endpoints must equal the recomputed max/min in a verified cone order. -/
def EndpointsCheck (n : Node) : Prop :=
  let a := coefficient n.mask0 n.thirdMask
  let b := coefficient n.mask1 n.thirdMask
  (n.lo = a ∧ n.hi = b.add unit ∧ (a.sub b).Nonneg) ∨
    (n.lo = b ∧ n.hi = a.add unit ∧ (b.sub a).Nonneg)

def NodeChecks (first second : Digits) (n : Node) : Prop :=
  n.mask0 < 16 ∧ n.mask1 < 16 ∧ n.thirdMask < 4 ∧
  EndpointsCheck n ∧ (n.hi.sub n.lo).Positive ∧
  ∀ third : Digits,
    0 ≤ constant first second third n.mask0 n.thirdMask ∧
    constant first second third n.mask1 n.thirdMask =
      constant first second third n.mask0 n.thirdMask + 1 ∧
    constant first second third n.mask1 n.thirdMask ≤ 22

instance (n : Node) : Decidable (EndpointsCheck n) := by unfold EndpointsCheck; infer_instance
instance (f s : Digits) (n : Node) : Decidable (NodeChecks f s n) := by
  unfold NodeChecks
  infer_instance

/-- Mathematical node meaning, including two alternative legal representations. -/
def NodeMeaning (first second : Digits) (n : Node) (p q : ℤ) : Prop :=
  n.mask0 < 16 ∧ n.mask1 < 16 ∧ n.thirdMask < 4 ∧
  n.lo.eval p q = max ((coefficient n.mask0 n.thirdMask).eval p q)
    ((coefficient n.mask1 n.thirdMask).eval p q) ∧
  n.hi.eval p q = min ((coefficient n.mask0 n.thirdMask).eval p q)
    ((coefficient n.mask1 n.thirdMask).eval p q) + p + q ∧
  n.lo.eval p q < n.hi.eval p q ∧
  ∀ third : Digits, ∃ c : ℤ, 0 ≤ c ∧ c + 1 ≤ 22 ∧
    constant first second third n.mask0 n.thirdMask = c ∧
    constant first second third n.mask1 n.thirdMask = c + 1 ∧
    ∀ d K : ℤ,
      IsSubsetSum (weights first second third d K p q)
        (d*K*(coefficient n.mask0 n.thirdMask).eval p q + c) ∧
      IsSubsetSum (weights first second third d K p q)
        (d*K*(coefficient n.mask1 n.thirdMask).eval p q + c + 1)

theorem endpoints_sound (n : Node) (h : EndpointsCheck n) (p q : ℤ)
    (hqp : q < p) (hpq : p < 2*q) :
    n.lo.eval p q = max ((coefficient n.mask0 n.thirdMask).eval p q)
      ((coefficient n.mask1 n.thirdMask).eval p q) ∧
    n.hi.eval p q = min ((coefficient n.mask0 n.thirdMask).eval p q)
      ((coefficient n.mask1 n.thirdMask).eval p q) + p + q := by
  rcases h with ⟨hl, hu, hc⟩ | ⟨hl, hu, hc⟩
  · have ho := Linear.nonneg_on_cone _ hc p q (le_of_lt hqp) (le_of_lt hpq)
    simp only [Linear.eval_sub] at ho
    have ho' := sub_nonneg.mp ho
    rw [hl, hu, max_eq_left ho', min_eq_right ho', Linear.eval_add]
    simp [unit, Linear.eval, add_assoc]
  · have ho := Linear.nonneg_on_cone _ hc p q (le_of_lt hqp) (le_of_lt hpq)
    simp only [Linear.eval_sub] at ho
    have ho' := sub_nonneg.mp ho
    rw [hl, hu, max_eq_right ho', min_eq_left ho', Linear.eval_add]
    simp [unit, Linear.eval, add_assoc]

theorem node_sound (first second : Digits) (n : Node) (h : NodeChecks first second n)
    (p q : ℤ) (hqp : q < p) (hpq : p < 2*q) : NodeMeaning first second n p q := by
  rcases h with ⟨hm0, hm1, htm, he, hw, hc⟩
  obtain ⟨hl, hu⟩ := endpoints_sound n he p q hqp hpq
  have width := Linear.positive_on_cone _ hw p q hqp hpq
  simp only [Linear.eval_sub] at width
  refine ⟨hm0, hm1, htm, hl, hu, by omega, ?_⟩
  intro third
  obtain ⟨h0, h1, h22⟩ := hc third
  refine ⟨constant first second third n.mask0 n.thirdMask, h0, by omega, rfl, h1, ?_⟩
  intro d K
  constructor
  · exact offset_isSubsetSum first second third d K p q n.mask0 n.thirdMask
  · have hr := offset_isSubsetSum first second third d K p q n.mask1 n.thirdMask
    rw [h1] at hr
    simpa only [add_assoc] using hr

structure Template where
  first : Digits
  second : Digits
  chain : List Node
  deriving DecidableEq, Repr, Inhabited

def nodeAt (t : Template) (i : ℕ) : Node := t.chain[i]?.getD default

def ChainChecks (t : Template) : Prop :=
  0 < t.chain.length ∧
  (∀ i : Fin t.chain.length, NodeChecks t.first t.second (nodeAt t i.val)) ∧
  (∀ i : Fin (t.chain.length - 1),
    ((nodeAt t i.val).hi.sub (nodeAt t (i.val+1)).lo).Positive ∧
    ((nodeAt t (i.val+1)).hi.sub (nodeAt t i.val).lo).Positive) ∧
  ((⟨1,2⟩ : Linear).sub (nodeAt t 0).lo).Nonneg ∧
  ((nodeAt t (t.chain.length-1)).hi.sub ⟨7,6⟩).Nonneg

instance (t : Template) : Decidable (ChainChecks t) := by unfold ChainChecks; infer_instance

/-- A path of intervals covers between its first lower and last upper endpoints.
No monotonicity of either sequence of endpoints is assumed. -/
theorem interval_chain_covers (lo hi : ℕ → ℤ) (n : ℕ)
    (links : ∀ i < n, lo (i+1) ≤ hi i) (z : ℤ)
    (hlo : lo 0 ≤ z) (hhi : z ≤ hi n) :
    ∃ i ≤ n, lo i ≤ z ∧ z ≤ hi i := by
  induction n with
  | zero => exact ⟨0, le_refl _, hlo, hhi⟩
  | succ n ih =>
    by_cases hz : z ≤ hi n
    · obtain ⟨i, hin, hil, hiu⟩ := ih (fun i h => links i (by omega)) hz
      exact ⟨i, by omega, hil, hiu⟩
    · exact ⟨n+1, le_refl _, by have := links n (by omega); omega, hhi⟩

def ChainMeaning (t : Template) (p q : ℤ) : Prop :=
  0 < t.chain.length ∧
  (∀ i : Fin t.chain.length, NodeMeaning t.first t.second (nodeAt t i.val) p q) ∧
  (∀ i : Fin (t.chain.length-1),
    (nodeAt t (i.val+1)).lo.eval p q < (nodeAt t i.val).hi.eval p q ∧
    (nodeAt t i.val).lo.eval p q < (nodeAt t (i.val+1)).hi.eval p q) ∧
  (nodeAt t 0).lo.eval p q ≤ p+2*q ∧
  7*p+6*q ≤ (nodeAt t (t.chain.length-1)).hi.eval p q ∧
  (∀ z : ℤ, p+2*q ≤ z → z ≤ 7*p+6*q →
    ∃ i : Fin t.chain.length, (nodeAt t i.val).lo.eval p q ≤ z ∧
      z ≤ (nodeAt t i.val).hi.eval p q)

theorem chain_sound (t : Template) (h : ChainChecks t) (p q : ℤ)
    (hqp : q < p) (hpq : p < 2*q) : ChainMeaning t p q := by
  rcases h with ⟨hn, hnodes, hlinks, hfirst, hlast⟩
  have hnodes' := fun i => node_sound t.first t.second (nodeAt t i.val) (hnodes i) p q hqp hpq
  have hlinks' : ∀ i : Fin (t.chain.length-1),
      (nodeAt t (i.val+1)).lo.eval p q < (nodeAt t i.val).hi.eval p q ∧
      (nodeAt t i.val).lo.eval p q < (nodeAt t (i.val+1)).hi.eval p q := by
    intro i
    have h1 := Linear.positive_on_cone _ (hlinks i).1 p q hqp hpq
    have h2 := Linear.positive_on_cone _ (hlinks i).2 p q hqp hpq
    simp only [Linear.eval_sub] at h1 h2
    constructor <;> omega
  have hf := Linear.nonneg_on_cone _ hfirst p q (le_of_lt hqp) (le_of_lt hpq)
  have hl := Linear.nonneg_on_cone _ hlast p q (le_of_lt hqp) (le_of_lt hpq)
  simp only [Linear.eval_sub] at hf hl
  change 0 ≤ (1*p+2*q) - (nodeAt t 0).lo.eval p q at hf
  change 0 ≤ (nodeAt t (t.chain.length-1)).hi.eval p q - (7*p+6*q) at hl
  have hf' : (nodeAt t 0).lo.eval p q ≤ p+2*q := by omega
  have hl' : 7*p+6*q ≤ (nodeAt t (t.chain.length-1)).hi.eval p q := by
    omega
  refine ⟨hn, hnodes', hlinks', hf', hl', ?_⟩
  intro z hz0 hz1
  obtain ⟨i, hi, hil, hiu⟩ := interval_chain_covers
    (fun i => (nodeAt t i).lo.eval p q) (fun i => (nodeAt t i).hi.eval p q)
    (t.chain.length-1)
    (fun i hi => le_of_lt (hlinks' ⟨i, hi⟩).1) z (le_trans hf' hz0) (le_trans hz1 hl')
  exact ⟨⟨i, by omega⟩, hil, hiu⟩

/-- Total coverage of all 3 nonzero first pairs and all 4 second pairs. -/
def CertificateChecks (data : List Template) : Prop :=
  ∀ first second : Digits, first ≠ (false, false) →
    ∃ t ∈ data, t.first = first ∧ t.second = second ∧ ChainChecks t

instance (data : List Template) : Decidable (CertificateChecks data) := by
  unfold CertificateChecks
  infer_instance

def checkCertificate (data : List Template) : Bool := decide (CertificateChecks data)

def MathematicallyCorrect (data : List Template) : Prop :=
  ∀ first second : Digits, first ≠ (false, false) →
    ∀ p q : ℤ, 0 < q → q < p → p < 2*q →
      ∃ t ∈ data, t.first = first ∧ t.second = second ∧ ChainMeaning t p q

/-- A successful finite check implies universal mathematical coverage and legal masks. -/
theorem checkCertificate_sound (data : List Template) (h : checkCertificate data = true) :
    MathematicallyCorrect data := by
  have hc : CertificateChecks data := of_decide_eq_true h
  intro first second hn p q _hq hqp hpq
  obtain ⟨t, ht, hf, hs, hc⟩ := hc first second hn
  exact ⟨t, ht, hf, hs, chain_sound t hc p q hqp hpq⟩

end Certificate
end Dyadic354
