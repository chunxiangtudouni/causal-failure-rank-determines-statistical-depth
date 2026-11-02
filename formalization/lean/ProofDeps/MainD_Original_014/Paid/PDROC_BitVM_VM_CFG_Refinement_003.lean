module

public import Paid.PDROC_BitVM_VM_CFG_Refinement_002
public import Paid.PDROC_BitVM_VM_ISA_ControlCatalog_003
public import Paid.PDROC_BitVM_VM_Source_RAMTrace_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Refinement

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Common.IO

/-- The bound is proof data from a subsequent actual source fetch.
It excludes the scanner's None result; it never selects a runtime PC
from a host value, and is not an additional original input condition. -/
theorem nextMatches_some (code : Program) (choice : Option (Program.PC code)) (target : Nat)
    (meaning : ISA.ControlCatalog.NextMatches code choice target) (valid : target < code.size) :
    choice = some ⟨target, valid⟩ := by
  cases choice with
  | none =>
    change code.size ≤ target at meaning
    omega
  | some actual =>
    change actual.val = target at meaning
    exact congrArg some (Fin.ext meaning)

theorem control_local (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code)
    (control : ISA.ControlInstruction) (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool)
    (ready : Source.Ready input logical events contents)
    (success : Instruction.execute input control.val logical = some next) (valid : next.pc < code.size) :
    ∃ (run : List (LocalState backend code (.inr control))) (final : LocalState backend code (.inr control)),
      LocalActualRun backend core code (.inr control) contents run final ∧
      Source.Observables input next (events ++ (Log.eventOf control.val logical).toList) final.stk ∧
      Program.choiceNext backend code pc (.inr control) final.var = some ⟨next.pc, valid⟩ := by
  obtain ⟨run, final, actual, observed, meaning⟩ :=
    ISA.ControlCatalog.execute_runs code control input logical next events contents ready success
  exact ⟨run, final, actual, observed,
    nextMatches_some code (ISA.ControlCatalog.observedNext code control final.var) next.pc meaning valid⟩

/-- Exhaustive static SUM refinement, using AllData and the control
owner's same-run contract. HALT has no original executeSome case. No
Instruction value, logical state, trace or target is a new runtime field. -/
theorem choice_local (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code)
    (choice : Program.Choice) (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool)
    (size : input.length = Log.BankMount.fieldCount core) (ready : Source.Ready input logical events contents)
    (position : logical.pc = pc.val) (success : Instruction.execute input (instructionOf choice) logical = some next)
    (valid : next.pc < code.size) :
    ∃ (run : List (LocalState backend code choice)) (final : LocalState backend code choice),
      LocalActualRun backend core code choice contents run final ∧
      Source.Observables input next (events ++ (Log.eventOf (instructionOf choice) logical).toList) final.stk ∧
      Program.choiceNext backend code pc choice final.var = some ⟨next.pc, valid⟩ := by
  cases choice with
  | inl data =>
    obtain ⟨_C, _D, _positiveC, _positiveD, chosen⟩ := data_local backend core code pc data
    obtain ⟨run, final, actual, observed, selected, _time⟩ :=
      chosen input logical next events contents size ready position success valid
    exact ⟨run, final, actual, observed, selected⟩
  | inr control =>
    exact control_local backend core code pc control input logical next events contents ready success valid

theorem opcode_local (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code)
    (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool)
    (size : input.length = Log.BankMount.fieldCount core) (ready : Source.Ready input logical events contents)
    (position : logical.pc = pc.val)
    (success : Instruction.execute input (code[pc.val]'pc.isLt) logical = some next) (valid : next.pc < code.size) :
    ∃ (run : List (OpcodeState backend code pc)) (final : OpcodeState backend code pc),
      LocalActualRun backend core code (Program.localChoice code pc) contents run final ∧
      Source.Observables input next (events ++ (Log.eventOf (code[pc.val]'pc.isLt) logical).toList) final.stk ∧
      Program.opcodeNext backend code pc final.var = some ⟨next.pc, valid⟩ := by
  have chosenSuccess : Instruction.execute input (instructionOf (Program.localChoice code pc)) logical = some next := by
    rw [instructionOf_localChoice]
    exact success
  obtain ⟨run, final, actual, observed, selected⟩ := choice_local backend core code pc
    (Program.localChoice code pc) input logical next events contents size ready position chosenSuccess valid
  refine ⟨run, final, actual, ?_, selected⟩
  simpa only [instructionOf_localChoice] using observed

/-- INTERNAL next-fetch-valid lemma. The final theorem below obtains
validity from the SAME original Runs, rather than adding it to the paper
input predicate. The endpoint uses the ACTUALLY produced finite choice,
saved by real metadata load and preserved through true cleanup. -/
theorem instruction_step (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code)
    (store : Program.Store backend code) (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool)
    (size : input.length = Log.BankMount.fieldCount core) (ready : Source.Ready input logical events contents)
    (position : logical.pc = pc.val)
    (success : Instruction.execute input (code[pc.val]'pc.isLt) logical = some next) (valid : next.pc < code.size) :
    ∃ (run : List (OpcodeState backend code pc)) (final : OpcodeState backend code pc)
      (nextStore : Program.Store backend code)
      (path : ActualPath (TM2.step (Program.program backend core code))
        (Program.atEntry backend code pc store contents)
        (Program.atEntry backend code ⟨next.pc, valid⟩ nextStore (Cleanup.cleaned final.stk))),
      LocalActualRun backend core code (Program.localChoice code pc) contents run final ∧
      Source.Ready input next (events ++ (Log.eventOf (code[pc.val]'pc.isLt) logical).toList) (Cleanup.cleaned final.stk) ∧
      path.posts.length ≤ run.length + 20 * (Cleanup.dataSize final.stk + 1) + 8 := by
  obtain ⟨run, final, actual, observed, selected⟩ :=
    opcode_local backend core code pc input logical next events contents size ready position success valid
  obtain ⟨nextStore, path, done, time⟩ := lift_local backend core code pc ⟨next.pc, valid⟩ store contents
    run final actual input next (events ++ (Log.eventOf (code[pc.val]'pc.isLt) logical).toList) observed selected
  exact ⟨run, final, nextStore, path, actual, done, time⟩

/-- Exact original source-step bridge. Its fetch is the fixed array
entry, while the local machine is exactly Program.program. -/
theorem source_step (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code)
    (store : Program.Store backend code) (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool)
    (size : input.length = Log.BankMount.fieldCount core) (ready : Source.Ready input logical events contents)
    (position : logical.pc = pc.val) (success : PaperProofs.Paid.Computation.step code input logical = some next)
    (valid : next.pc < code.size) :
    ∃ (run : List (OpcodeState backend code pc)) (final : OpcodeState backend code pc)
      (nextStore : Program.Store backend code)
      (path : ActualPath (TM2.step (Program.program backend core code))
        (Program.atEntry backend code pc store contents)
        (Program.atEntry backend code ⟨next.pc, valid⟩ nextStore (Cleanup.cleaned final.stk))),
      LocalActualRun backend core code (Program.localChoice code pc) contents run final ∧
      Source.Ready input next (events ++ (Log.eventOf (code[pc.val]'pc.isLt) logical).toList) (Cleanup.cleaned final.stk) ∧
      path.posts.length ≤ run.length + 20 * (Cleanup.dataSize final.stk + 1) + 8 := by
  have executed : Instruction.execute input (code[pc.val]'pc.isLt) logical = some next := by
    simpa only [PaperProofs.Paid.Computation.step, position, Array.getElem?_eq_getElem pc.isLt,
      Option.bind_eq_bind, Option.bind_some] using success
  exact instruction_step backend core code pc store input logical next events contents size ready position executed valid

/-- The actual original Runs derives the needed next-fetch validity.
No new input qualification, PC oracle or runtime host cast is supplied.
The parent's chain induction provides nextMember from its original edge. -/
theorem on_original_runs (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code)
    (store : Program.Store backend code) (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool)
    (original : List PaperProofs.Paid.Computation.State) (originalFinal : PaperProofs.Paid.Computation.State)
    (originalRuns : Runs code input original originalFinal) (nextMember : next ∈ original)
    (size : input.length = Log.BankMount.fieldCount core) (ready : Source.Ready input logical events contents)
    (position : logical.pc = pc.val) (success : PaperProofs.Paid.Computation.step code input logical = some next) :
    ∃ (target : Program.PC code) (run : List (OpcodeState backend code pc)) (final : OpcodeState backend code pc)
      (nextStore : Program.Store backend code)
      (path : ActualPath (TM2.step (Program.program backend core code))
        (Program.atEntry backend code pc store contents)
        (Program.atEntry backend code target nextStore (Cleanup.cleaned final.stk))),
      target.val = next.pc ∧ LocalActualRun backend core code (Program.localChoice code pc) contents run final ∧
      Source.Ready input next (events ++ (Log.eventOf (code[pc.val]'pc.isLt) logical).toList) (Cleanup.cleaned final.stk) ∧
      path.posts.length ≤ run.length + 20 * (Cleanup.dataSize final.stk + 1) + 8 := by
  have valid := Source.runs_pc_valid code input original originalFinal originalRuns next nextMember
  obtain ⟨run, final, nextStore, path, actual, done, time⟩ :=
    source_step backend core code pc store input logical next events contents size ready position success valid
  exact ⟨⟨next.pc, valid⟩, run, final, nextStore, path, rfl, actual, done, time⟩

end PDROC.BitVM.VM.CFG.Refinement
