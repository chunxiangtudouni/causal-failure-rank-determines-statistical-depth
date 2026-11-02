module

public import Paid.PDCompute_SolverCutoffScan_036
public import Paid.PDMenu_ComputeFrame_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (loadSlot)
open PDMenu.ComputeFrame

/-- ONE fixed112-instruction endpoint scan loop. All direct labels use
their final absolute origin. Endpoint values, M, candidate scores, index
and cache pointer are read from the original actual live state. -/
def scanKernel (mode : ReaderMode) (origin : ℕ) : List Instruction :=
  rangeCompareCode++[.branchZero .flag (origin+112) (origin+8)]++
    loadSlot 39 .address++endpointHeaderCode mode++headerCode candidateCommands++
      minimumUpdateCode (origin+75)++addNatSlot 25 1++addNatSlot 39 2++[.jump origin]

theorem scanKernel_length (mode : ReaderMode) (origin : ℕ) : (scanKernel mode origin).length=112 := rfl

private def noOutput : Instruction → Bool
  | .output _ => false
  | _ => true

private theorem noOutput_correct (instruction : Instruction) : noOutput instruction=true ↔ NoOutputInstruction instruction := by
  cases instruction <;> simp [noOutput,NoOutputInstruction]

private def noInput : Instruction → Bool
  | .loadInput _ _ => false
  | _ => true

private theorem noInput_correct (instruction : Instruction) : noInput instruction=true ↔ NoInputInstruction instruction := by
  cases instruction <;> simp [noInput,NoInputInstruction]

theorem scanKernel_noOutput (mode : ReaderMode) (origin : ℕ) (instruction : Instruction)
    (member : instruction ∈ scanKernel mode origin) : NoOutputInstruction instruction := by
  have hall : (scanKernel mode origin).all noOutput=true := by cases mode <;> rfl
  exact (noOutput_correct instruction).mp ((List.all_eq_true.mp hall) instruction member)

theorem scanKernel_heap_noInput (origin : ℕ) (instruction : Instruction)
    (member : instruction ∈ scanKernel .liveHeap origin) : NoInputInstruction instruction := by
  have hall : (scanKernel .liveHeap origin).all noInput=true := rfl
  exact (noInput_correct instruction).mp ((List.all_eq_true.mp hall) instruction member)

end PDCompute.Solver
