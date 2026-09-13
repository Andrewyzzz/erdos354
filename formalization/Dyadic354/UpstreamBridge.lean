import Dyadic354.Main
import Dyadic354.UpstreamDefinitions

namespace Dyadic354.UpstreamBridge

theorem floorMultiples_eq (α γ : ℝ) : Erdos354.FloorMultiples α γ = floorMultiples α γ := rfl

theorem interleave_eq (α β γ : ℝ) :
    Erdos354.FloorMultiples.interleave α β γ = interleave α β γ := rfl

theorem indexedComplete_iff (w : ℕ → ℤ) : IsAddCompleteNatSeq' w ↔ IndexedComplete w := Iff.rfl

theorem setComplete_iff (A : Set ℤ) : IsAddComplete A ↔ SetComplete A := Iff.rfl

theorem strongComplete_iff (A : Set ℤ) : IsAddStronglyComplete A ↔ SetStronglyComplete A := by
  constructor
  · intro h B hB
    exact h hB
  · intro h B hB
    exact h B hB

/-- Exact positive right-hand side of the pinned upstream part (i).
The only difference from its source is removal of the answer wrapper. -/
def PartITarget : Prop := ∀ᵉ (α > 0) (β > 0), Irrational (α / β) →
    IsAddCompleteNatSeq' (Erdos354.FloorMultiples.interleave α β 2)

theorem partITarget_iff : PartITarget ↔ PartI := by
  constructor
  · intro h α β hα hβ hirr
    exact h α hα β hβ hirr
  · intro h α hα β hβ hirr
    exact h α β hα hβ hirr

theorem erdos354_part_i_upstream : PartITarget := partITarget_iff.mpr erdos354_part_i

theorem erdos354_strong_upstream (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hirr : Irrational (α / β)) :
    IsAddStronglyComplete (Set.range (Erdos354.FloorMultiples.interleave α β 2) \ {0}) :=
  (strongComplete_iff _).mpr (erdos354_strong_completeness α β hα hβ hirr)

end Dyadic354.UpstreamBridge
