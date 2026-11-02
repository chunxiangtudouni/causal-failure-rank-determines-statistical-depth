module

public import Paid.PDROC_CalibrationRow_Init_001
public import Paid.PDROC_CalibrationRow_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem initCell_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State) :
    LinearFrames region input (basicBlock .initCell).body before := by
  apply LinearFrames.of_static
  intro instruction member state
  simp only [basicBlock,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (h|h|h)|(h|h) <;> subst instruction <;> trivial

theorem initCenter_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State) :
    LinearFrames region input (basicBlock .initCenter).body before := by
  apply LinearFrames.of_static
  intro instruction member state
  simp only [basicBlock,List.mem_cons,List.not_mem_nil,or_false] at member
  subst instruction
  trivial

def initCellNext (origin : ℕ) (before : State) (base level cursor : ℕ) : State :=
  {initCellResult before base level cursor with
    pc:=labelAddress origin (if cursor=level then .initCenter else .initStore)}

theorem initCell_control_execute (origin : ℕ) (input : List Cell) (before : State) (base level cursor : ℕ) :
    (controlInstruction origin (basicBlock .initCell).control).execute input
      (initCellResult before base level cursor)=some (initCellNext origin before base level cursor) := by
  have flag := (initCell_fields before base level cursor).2.2.2.2.1
  change (Instruction.branchZero .flag (labelAddress origin .initStore) (labelAddress origin .initCenter)).execute
    input (initCellResult before base level cursor)=some (initCellNext origin before base level cursor)
  rw [execute_branchZero .flag (labelAddress origin .initStore) (labelAddress origin .initCenter)
    input (initCellResult before base level cursor) (if cursor=level then 1 else 0) flag]
  by_cases center : cursor=level <;> simp [center,initCellNext]

theorem initCell_next_value (origin : ℕ) (before : State) (base level cursor : ℕ) :
    (initCellNext origin before base level cursor).register .value=.rational 0 ∧
    (initCellNext origin before base level cursor).register .index=before.register .index := by
  have fields := initCell_fields before base level cursor
  exact ⟨fields.2.2.2.2.2.1,fields.2.2.2.1⟩

theorem initCell_trace (origin : ℕ) (input : List Cell) (before : State) (base level cursor : ℕ)
    (position : before.pc=labelAddress origin .initCell)
    (fresh : before.register .fresh=.natural base)
    (live : base+5 ∈ before.live) (levelValue : before.heap (base+5)=.natural level)
    (index : before.register .index=.natural cursor) :
    ∃ trace : List State,trace.head?=some before ∧
      trace.getLast?=some (initCellNext origin before base level cursor) ∧
      trace.length=7 ∧
      trace.IsChain (fun a b => step (locatedBlock origin (kernel origin)) input a=some b) ∧
      time (locatedBlock origin (kernel origin)) trace≤105 ∧
      ∀ state∈trace,state.output=before.output ∧ state.register .fresh=before.register .fresh := by
  exact row_block_trace origin input .initCell (by rfl) before (initCellResult before base level cursor)
    (initCellNext origin before base level cursor) position
    (initCell_execute input before base level cursor fresh live levelValue index)
    (initCell_control_execute origin input before base level cursor)

def initCenterNext (origin : ℕ) (before : State) : State :=
  {initCenterResult before with pc:=labelAddress origin .initStore}

theorem initCenter_control_execute (origin : ℕ) (input : List Cell) (before : State) :
    (controlInstruction origin (basicBlock .initCenter).control).execute input
      (initCenterResult before)=some (initCenterNext origin before) := rfl

theorem initCenter_trace (origin : ℕ) (input : List Cell) (before : State)
    (position : before.pc=labelAddress origin .initCenter) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (initCenterNext origin before) ∧
      trace.length=3 ∧
      trace.IsChain (fun a b => step (locatedBlock origin (kernel origin)) input a=some b) ∧
      time (locatedBlock origin (kernel origin)) trace≤45 ∧
      ∀ state∈trace,state.output=before.output ∧ state.register .fresh=before.register .fresh := by
  exact row_block_trace origin input .initCenter (by rfl) before (initCenterResult before)
    (initCenterNext origin before) position (initCenter_execute input before)
    (initCenter_control_execute origin input before)

end PDROC.CalibrationRow
