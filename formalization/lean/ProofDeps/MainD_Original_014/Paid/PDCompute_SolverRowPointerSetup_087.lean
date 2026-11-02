module

public import Paid.PDCompute_SolverRowPointers_086

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (storeSlot storeSlotResult)
open PDMenu.ComputeFrame

def rowPointerSetupCode : List Instruction := storeSlot 47 .fresh++runtimeCode rowPointerCommands

/-- The base B is SAVED by real code from fresh, before it is read by
the fixed natural address block. No prefilled base-slot premise remains. -/
theorem rowPointerSetup_trace_memory (program : Program) (input : List Cell) (before : State)
    (base n k row column : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hk : values 4=.natural k) (hr : values 19=.natural row) (hc : values 20=.natural column)
    (fetch : FetchesCode program before.pc rowPointerSetupCode) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 5010 ∧
      Header after base (rowPointerValues (Function.update values 47 (.natural base)) base k row column) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+rowPointerSetupCode.length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  let saved:=storeSlotResult before base 47 .fresh
  let savedValues:=Function.update values 47 (.natural base)
  have fields : saved.heap=Function.update before.heap (base+47) (before.register .fresh) ∧
      saved.live=insert (base+47) before.live ∧ saved.register .fresh=before.register .fresh ∧
      saved.pc=before.pc+3 ∧ saved.output=before.output := ⟨rfl,rfl,rfl,rfl,rfl⟩
  have fetchSave : FetchesCode program before.pc (storeSlot 47 .fresh) := fetch.append_left
  obtain ⟨saveTrace,saveHead,saveLast,saveChain,saveTime,saveMemory⟩ :=
    header.storeSlot_trace_memory program input 47 .fresh (by decide) hbase (by decide) fetchSave
  have savedHeap : saved.heap=Function.update before.heap (base+47) (.natural base) := by
    simpa only [hbase] using fields.1
  have savedHeader : Header saved base savedValues := by
    apply Header.update header 47 (.natural base) savedHeap
    rw [fields.2.1]
    exact Finset.subset_insert _ _
  have savedBase : saved.register .fresh=.natural base := fields.2.2.1.trans hbase
  have savedFrame : Frame before saved base n k :=
    slotWrite_frame before saved base 47 n k (.natural base) (by decide) savedHeap fields.2.1
  have fetchPointers : FetchesCode program saved.pc (runtimeCode rowPointerCommands) := by
    rw [fields.2.2.2.1]
    exact fetch.append_right
  obtain ⟨pointerTrace,after,pointerHead,pointerLast,pointerChain,pointerTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,pointerMemory⟩ :=
    rowPointer_trace_memory program input saved base n k row column savedValues savedHeader savedBase rfl hk hr hc fetchPointers
  have joined:=joinTrace_spec program input saveTrace pointerTrace before saved after 60 4950
    saveHead saveLast pointerHead pointerLast saveChain pointerChain saveTime pointerTime
  refine ⟨joinTrace saveTrace pointerTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,afterHeader,
    afterBase,?_,savedFrame.trans afterFrame,afterOutput.trans fields.2.2.2.2,
    joinTrace_memory saveTrace pointerTrace before saved base saveLast saveMemory pointerMemory⟩
  have lengthEq : rowPointerSetupCode.length=3+(runtimeCode rowPointerCommands).length := by
    rw [rowPointerSetupCode,List.length_append]
    rfl
  calc
    after.pc = saved.pc+(runtimeCode rowPointerCommands).length := afterPC
    _ = before.pc+3+(runtimeCode rowPointerCommands).length :=
      congrArg (·+(runtimeCode rowPointerCommands).length) fields.2.2.2.1
    _ = before.pc+(3+(runtimeCode rowPointerCommands).length) := Nat.add_assoc _ _ _
    _ = before.pc+rowPointerSetupCode.length := by rw [lengthEq]

end PDCompute.Solver
