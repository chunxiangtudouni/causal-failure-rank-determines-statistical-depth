module

public import Paid.PDLower_CalibrationCompute_Fresh_013
public import Paid.PDLower_CalibrationCompute_Header_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem enter_can_execute (input : List Cell) (before : State) (base : ℕ)
    (fresh : before.register .fresh = .natural base) :
    ∃ after,linearExecute input (basicBlock .enter).body before = some after := by
  refine ⟨prologueResult before base,?_⟩
  exact prologue_execute input before base fresh

theorem original_entry_can_execute (input : List Cell) (P : Parameters) (base endpoints returnPC : ℕ)
    (before : State) (entry : Entry P base endpoints returnPC before) :
    ∃ after,linearExecute input (basicBlock .enter).body before = some after ∧ after.register .fresh = .natural base := by
  obtain ⟨after,run⟩ := enter_can_execute input before base entry.1
  exact ⟨after,run,(kernel_body_preserves_fresh input .enter before after run).trans entry.1⟩

end PDLower.CalibrationCompute
