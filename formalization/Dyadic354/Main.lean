import Dyadic354.SetBridge

namespace Dyadic354

open FloorSequence Normalization SetBridge

/-- The manuscript's full set-valued strong completeness claim. Arbitrary
finite deletions are avoided by actual upward tails; normalized values
are injective, so the representing finite set has no repeated value. -/
theorem erdos354_strong_completeness : StrongCompleteness := by
  intro α β hα hβ hirr D hD
  obtain ⟨B, hB⟩ := hD.bddAbove
  obtain ⟨u, v, hBv, hb, hba, hab⟩ := above_bound α β hα hβ hirr B
  let α' := (2 : ℝ) ^ u * α
  let β' := (2 : ℝ) ^ v * β
  have hi := shifted_irrational α β hirr u v
  have hc := BG.normalized_complete α' β' hb hba hab hi
  have hs := indexed_to_set (interleave α' β' 2) (normalized_injective α' β' hb hba hab) hc
  apply setComplete_mono _ _ ?_ hs
  rintro z ⟨i, rfl⟩
  have hlo := normalized_lower_bound α' β' hb hba hab i
  have hmem := shifted_range_subset α β u v (Set.mem_range_self i)
  refine ⟨⟨hmem, ?_⟩, ?_⟩
  · simp only [Set.mem_singleton_iff]
    change interleave α' β' 2 i ≠ 0
    exact ne_of_gt (hb.trans_le hlo)
  · intro hz
    exact (not_le_of_gt (hBv.trans_le hlo)) (hB hz)

/-- The exact frozen positive statement of Erdős 354(i), for all positive
real parameters. No FE/DB/BG or normalization premises remain. -/
theorem erdos354_part_i : PartI := by
  intro α β hα hβ hirr
  have hs := erdos354_strong_completeness α β hα hβ hirr ∅ Set.finite_empty
  have hc : SetComplete (dyadicValueSet α β) := by simpa using hs
  apply set_to_indexed
  exact setComplete_mono _ _ (fun _ hx => hx.1) hc

end Dyadic354
