module

public import Paid.PDLower_CalibrationCompute_Fetch_009
public import Paid.PDMenu_ComputeFrame_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def straight : Instruction → Bool
  | .branchZero _ _ _ | .jump _ | .jumpIndirect _ | .halt => false
  | _ => true

theorem straight_correct (instruction : Instruction) :
    straight instruction = true ↔ PDMenu.ComputeFrame.StraightInstruction instruction := by
  cases instruction <;> simp [straight,PDMenu.ComputeFrame.StraightInstruction]

set_option maxRecDepth 4096 in
theorem basicBlock_straight (label : Label) : PDMenu.ComputeFrame.StraightCode (basicBlock label).body := by
  have all : (basicBlock label).body.all straight = true := by cases label <;> rfl
  intro instruction member
  exact (straight_correct instruction).mp ((List.all_eq_true.mp all) instruction member)

/-- This identifies the actual global literal fetch at every body offset;
no phase counter or caller fetch oracle is passed to the final program. -/
theorem kernel_body_trace (origin : ℕ) (label : Label) (input : List Cell) (before after : State)
    (position : before.pc = labelAddress origin label)
    (run : linearExecute input (basicBlock label).body before = some after) :
    ∃ trace : List State,trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length = (basicBlock label).body.length+1 ∧
      trace.IsChain (fun first later => step (PDMenu.ComputeFrame.locatedBlock origin (kernel origin)) input first = some later) ∧
      after.pc = labelAddress origin label+(basicBlock label).body.length ∧
      time (PDMenu.ComputeFrame.locatedBlock origin (kernel origin)) trace ≤ 15*((basicBlock label).body.length+1) ∧
      ∀ state ∈ trace.dropLast,∃ count < (basicBlock label).body.length,
        linearExecute input ((basicBlock label).body.take count) before = some state := by
  have fetch : PDMenu.ComputeFrame.FetchesCode (PDMenu.ComputeFrame.locatedBlock origin (kernel origin)) before.pc
      (basicBlock label).body := by
    intro offset inside
    rw [position]
    exact kernel_body_fetch origin label offset inside
  obtain ⟨trace,head,last,length,chain,prefixRuns⟩ :=
    PDMenu.ComputeFrame.linearExecute_trace (PDMenu.ComputeFrame.locatedBlock origin (kernel origin)) input
      (basicBlock label).body (basicBlock_straight label) before after fetch run
  refine ⟨trace,head,last,length,chain,?_,?_,prefixRuns⟩
  · simpa only [position] using PDMenu.ComputeFrame.linearExecute_pc input (basicBlock label).body
      (basicBlock_straight label) before after run
  · simpa only [length] using PDMenu.ComputeFrame.time_le_length
      (PDMenu.ComputeFrame.locatedBlock origin (kernel origin)) trace

theorem kernel_block_trace (origin : ℕ) (label : Label) (input : List Cell) (before middle after : State)
    (position : before.pc = labelAddress origin label)
    (run : linearExecute input (basicBlock label).body before = some middle)
    (control : (controlInstruction origin (basicBlock label).control).execute input middle = some after) :
    ∃ trace : List State,trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun first later => step (PDMenu.ComputeFrame.locatedBlock origin (kernel origin)) input first = some later) ∧
      time (PDMenu.ComputeFrame.locatedBlock origin (kernel origin)) trace ≤
        15*((basicBlock label).body.length+1)+15 := by
  obtain ⟨body,head,last,_length,chain,middlePC,cost,_prefix⟩ := kernel_body_trace origin label input before middle position run
  have step : step (PDMenu.ComputeFrame.locatedBlock origin (kernel origin)) input middle = some after := by
    rw [kernel_control_step origin label input middle middlePC]
    exact control
  have joined := PDMenu.ComputeFrame.chain_append_control (PDMenu.ComputeFrame.locatedBlock origin (kernel origin))
    input body middle after chain last step
  refine ⟨body++[after],?_,?_,joined.1,joined.2.trans (by omega)⟩
  · cases body with
    | nil => cases head
    | cons first rest => exact head
  · simp

end PDLower.CalibrationCompute
