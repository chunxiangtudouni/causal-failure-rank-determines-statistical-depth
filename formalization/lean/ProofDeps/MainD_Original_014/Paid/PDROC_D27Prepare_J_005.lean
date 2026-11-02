module

public import Paid.PDROC_D27Prepare_Q_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid.Computation

namespace PDROC.D27Prepare.Q

theorem MemoryProgress.mono {R S : Finset ℕ} {before after : State}
    (h : MemoryProgress R before after) (subset : R ⊆ S) : MemoryProgress S before after := by
  constructor
  · constructor
    · intro address outside
      exact h.1.1 address (fun member => outside (subset member))
    · intro address outside
      exact h.1.2 address (fun member => outside (subset member))
  · exact h.2

theorem Segment.widen_region {R S : Finset ℕ} {input : List Cell} {before after : State}
    {H B budget : ℕ} (segment : Segment R input before after H B budget) (subset : R ⊆ S) :
    Segment S input before after H B budget := by
  obtain ⟨trace, head, last, chain, length, bounds, frames⟩ := segment.witness
  exact ⟨⟨trace, head, last, chain, length, bounds,
    fun state member => (frames state member).mono subset⟩, segment.output, segment.fresh⟩

theorem MemoryProgress.slot {R : Finset ℕ} {before after : State}
    (progress : MemoryProgress R before after) (address : ℕ) (outside : address ∉ R)
    (value : Cell) (old : PDROC.D27Prepare.Search.SlotHas before address value) :
    PDROC.D27Prepare.Search.SlotHas after address value :=
  ⟨progress.2 old.1, (progress.1.1 address outside).trans old.2⟩

end PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.J

def region : Finset ℕ := {10, 32, 43, 44, 45, 46, 47}

end PDROC.D27Prepare.J
