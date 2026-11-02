module

public import Paid.PDCompute_SolverHeaderFrame_099

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation

/-- The actual existing output remains counted. A callee may reuse
arbitrarily live cells inside its workspace; its live-space increase is
bounded by the true region cardinality rather than a freshness premise. -/
theorem RegionMemory.workingCells_le {before after : State} {region : Finset ℕ}
    (memory : RegionMemory before after region) : workingCells after ≤ workingCells before+region.card := by
  have liveBound : after.live.card ≤ before.live.card+region.card :=
    (Finset.card_le_card memory.2.1).trans (Finset.card_union_le before.live region)
  unfold workingCells
  rw [memory.2.2.2]
  omega

theorem workspace_card_le (base n k : ℕ) : (workspace base n k).card ≤ workspaceSize n k := by
  unfold workspace
  exact Finset.card_image_le.trans (by simp)

theorem RegionMemory.workspace_workingCells {before after : State} {base n k : ℕ}
    (memory : RegionMemory before after (workspace base n k)) :
    workingCells after ≤ workingCells before+62*entryCount n k := by
  have cells:=memory.workingCells_le
  have size:=(workspace_card_le base n k).trans (workspaceSize_linear n k)
  omega

end PDCompute.Solver
