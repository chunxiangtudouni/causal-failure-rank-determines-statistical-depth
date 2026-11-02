module

public import Paid.PDLower_CalibrationCompute_Trace_012
public import Paid.PDMenu_ComputeFrame_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def readOnly : Instruction→Bool
  | .store _ _ | .release _ | .output _ => false
  | _ => true

theorem readOnly_writesWithin (instruction : Instruction) (safe : readOnly instruction=true)
    (region : Finset ℕ) (before : State) : PDMenu.ComputeFrame.WritesWithin region instruction before := by
  cases instruction <;> simp_all [readOnly,PDMenu.ComputeFrame.WritesWithin]

theorem readOnly_noOutput (instruction : Instruction) (safe : readOnly instruction=true) :
    PDMenu.ComputeFrame.NoOutputInstruction instruction := by
  cases instruction <;> simp_all [readOnly,PDMenu.ComputeFrame.NoOutputInstruction]

/-- Successful execution of a genuinely read-only instruction list keeps
the entire physical heap/live set and output, for every caller state. -/
theorem linearReadOnly_frame (input : List Cell) (code : List Instruction) (before after : State)
    (safe : code.all readOnly=true) (run : linearExecute input code before=some after) :
    PDMenu.ComputeFrame.MemoryFrame ∅ before after ∧ after.output=before.output := by
  induction code generalizing before with
  | nil =>
    have same : before=after := Option.some.inj run
    subst after
    exact ⟨PDMenu.ComputeFrame.MemoryFrame.refl ∅ before,rfl⟩
  | cons instruction rest ih =>
    have parts : readOnly instruction=true ∧ rest.all readOnly=true := by
      simpa only [List.all_cons,Bool.and_eq_true] using safe
    obtain ⟨middle,one,later⟩ := Option.bind_eq_some_iff.mp run
    have firstFrame := PDMenu.ComputeFrame.execute_memoryFrame ∅ instruction input before middle
      (readOnly_writesWithin instruction parts.1 ∅ before) one
    have firstOutput := PDMenu.ComputeFrame.execute_output_eq_of_noOutput instruction input before middle
      (readOnly_noOutput instruction parts.1) one
    have following := ih middle parts.2 later
    exact ⟨firstFrame.trans following.1,following.2.trans firstOutput⟩

theorem linearReadOnly_heap (input : List Cell) (code : List Instruction) (before after : State)
    (safe : code.all readOnly=true) (run : linearExecute input code before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  have frame := linearReadOnly_frame input code before after safe run
  refine ⟨funext (fun address => frame.1.1 address (by simp)),?_,frame.2⟩
  apply Finset.ext
  intro address
  exact frame.1.2 address (by simp)

theorem weight_readOnly : (basicBlock .weight).body.all readOnly=true := rfl
theorem divide_readOnly : (basicBlock .divide).body.all readOnly=true := rfl
theorem zeroWeight_readOnly : (basicBlock .zeroWeight).body.all readOnly=true := rfl
theorem sumGate_readOnly : (basicBlock .sumGate).body.all readOnly=true := rfl
theorem levelGate_readOnly : (basicBlock .levelGate).body.all readOnly=true := rfl
theorem finish_readOnly : (basicBlock .finish).body.all readOnly=true := rfl

end PDLower.CalibrationCompute
