module

public import Paid.PDLower_CalibrationCompute_StandaloneSegment_057

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def bootstrapEndCode : List Instruction :=
  [.constant .old (.natural 2),.natOp .multiply .fresh .total .old,
   .constant .old (.natural 3),.natOp .add .fresh .fresh .old,
   .constant .address (.natural 0),.constant .old (.natural (mainStart+27))]

def bootstrapEndBodyResult (before : State) (M : ℕ) : State :=
  {before with
    pc:=before.pc+6,
    register:=Function.update
      (Function.update
        (Function.update before.register .fresh (.natural (rowWidth M)))
        .address (.natural 0))
      .old (.natural (mainStart+27))}

def bootstrapEndResult (before : State) (M : ℕ) : State :=
  {bootstrapEndBodyResult before M with pc:=1}

theorem bootstrapEnd_execute (input : List Cell) (before : State) (M : ℕ)
    (total : before.register .total=.natural M) :
    linearExecute input bootstrapEndCode before=some (bootstrapEndBodyResult before M) := by
  simp [bootstrapEndCode,linearExecute,Instruction.execute,State.set,NatOp.eval,
    Cell.nat?,total,bootstrapEndBodyResult,rowWidth,Nat.add_assoc,Nat.mul_comm]
  funext register
  cases register <;> simp

theorem bootstrapEnd_straight : PDMenu.ComputeFrame.StraightCode bootstrapEndCode := by
  intro instruction member
  simp only [bootstrapEndCode,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with eq|eq|eq|eq|eq|eq <;> subst instruction <;> trivial

theorem bootstrapEnd_fetch (offset : ℕ) (inside : offset<bootstrapEndCode.length) :
    calibrate[(mainStart+20)+offset]?=bootstrapEndCode[offset]? := by
  rw [Nat.add_assoc,calibrate_bootstrap_fetch]
  have bound : offset<6 := inside
  interval_cases offset <;> rfl

/-- The original seven post-copy operations restore the fresh workspace,
set the true return address, and actually jump into the fixed kernel. -/
theorem bootstrapEnd_segment (input : List Cell) (before : State) (M : ℕ)
    (position : before.pc=mainStart+20) (total : before.register .total=.natural M) :
    StandaloneSegment input before (bootstrapEndResult before M) 120 := by
  let middle := bootstrapEndBodyResult before M
  let after := bootstrapEndResult before M
  have fetch : PDMenu.ComputeFrame.FetchesCode calibrate before.pc bootstrapEndCode := by
    intro offset inside
    rw [position]
    exact bootstrapEnd_fetch offset inside
  obtain ⟨trace,head,last,length,chain,_prefix⟩ :=
    PDMenu.ComputeFrame.linearExecute_trace calibrate input bootstrapEndCode bootstrapEnd_straight before middle fetch
      (bootstrapEnd_execute input before M total)
  have actual : step calibrate input middle=some after := by
    have pc : middle.pc=mainStart+26 := by dsimp [middle,bootstrapEndBodyResult]; omega
    simp only [step,pc,calibrate_call_fetch,Instruction.execute]
    rfl
  have joined := PDMenu.ComputeFrame.chain_append_control calibrate input trace middle after chain last actual
  refine ⟨trace++[after],?_,?_,joined.1,?_⟩
  · cases trace with
    | nil => cases head
    | cons first rest => exact head
  · simp only [List.getLast?_append_cons,List.getLast?_singleton,after]
  · have cost := PDMenu.ComputeFrame.time_le_length calibrate trace
    have size : trace.length=7 := length
    exact joined.2.trans (by omega)

end PDLower.CalibrationCompute
