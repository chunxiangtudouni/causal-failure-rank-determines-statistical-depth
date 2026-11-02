module

public import Paid.PDROC_BitVM_VM_CFG_Refinement_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Refinement

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Common.IO

/-- A fetched original HALT is implemented by the old two-state Nop
callee, not by a fictitious successful Instruction.execute HALT step. -/
theorem halt_local (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code)
    (choice : Program.Choice) (contents : ISA.Stack → List Bool) (fetchedSyntax : instructionOf choice = .halt) :
    ∃ (run : List (LocalState backend code choice)) (final : LocalState backend code choice),
      LocalActualRun backend core code choice contents run final ∧ final.stk = contents ∧
      Program.choiceNext backend code pc choice final.var = none ∧ run.length = 2 := by
  cases choice with
  | inl data =>
    rcases data with ⟨instruction, eligible⟩
    change instruction = .halt at fetchedSyntax
    subst instruction
    cases eligible
  | inr control =>
    rcases control with ⟨instruction, eligible⟩
    change instruction = .halt at fetchedSyntax
    subst instruction
    obtain ⟨run, head, chain, last, halt, length⟩ := ISA.ControlCatalog.nop_runs contents
    exact ⟨run, ⟨none, (), contents⟩, ⟨head, chain, last, halt⟩, rfl, rfl, length⟩

/-- ONE actual fetched-HALT path: real entry/reset, Nop return, actual
metadata None load, genuine shared nine-clear, metadata port, true HALT.
The finite caller store is arbitrary and the logical data is preserved. -/
theorem halt_step (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code)
    (store : Program.Store backend code) (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool)
    (ready : Source.Ready input logical events contents) (fetchedSyntax : (code[pc.val]'pc.isLt) = .halt) :
    ∃ (terminal : Program.State backend code),
      TM2.step (Program.program backend core code) terminal = none ∧
      Source.Ready input logical events terminal.stk ∧
      ∃ path : ActualPath (TM2.step (Program.program backend core code))
        (Program.atEntry backend code pc store contents) terminal,
        path.posts.length ≤ 30 * (Kernel.NatInstruction.dataSize contents + 1) := by
  have chosenSyntax : instructionOf (Program.localChoice code pc) = .halt :=
    (instructionOf_localChoice code pc).trans fetchedSyntax
  obtain ⟨run, final, actual, data, selected, length⟩ :=
    halt_local backend core code pc (Program.localChoice code pc) contents chosenSyntax
  have observed : Source.Observables input logical events final.stk := by
    rw [data]
    exact ready.toObservables
  have selectedReturned : Program.chooseNext backend code pc
      (Step.opcodeStore (Program.OpcodeStore backend code) pc store final.var) = none := by
    change Program.opcodeNext backend code pc
      (Step.opcodeStore (Program.OpcodeStore backend code) pc store final.var (.opcode pc)) = none
    rw [returned_store_self]
    exact selected
  obtain ⟨path, done, time⟩ := Step.step_none
    (Program.OpcodeLabel backend code) (Program.OpcodeStore backend code)
    (Program.opcodeProgram backend core code) (Program.opcodeStart backend code) (Program.opcodeInitial backend code)
    (Program.chooseNext backend code) pc store contents run final
    actual.1 actual.2.1 actual.2.2.1 actual.2.2.2 input logical events observed selectedReturned
  let terminal : Program.State backend code :=
    ⟨none, Step.cleanStore (Program.OpcodeStore backend code)
      (Step.metadataStore (Program.OpcodeStore backend code) (Program.chooseNext backend code) pc
        (Step.opcodeStore (Program.OpcodeStore backend code) pc store final.var)), Cleanup.cleaned final.stk⟩
  have numericData : Cleanup.dataSize final.stk = Kernel.NatInstruction.dataSize contents := by
    rw [data]
    rfl
  refine ⟨terminal, rfl, done, path, ?_⟩
  calc
    path.posts.length ≤ run.length + 20 * (Cleanup.dataSize final.stk + 1) + 8 := time
    _ = 2 + 20 * (Kernel.NatInstruction.dataSize contents + 1) + 8 := by rw [length, numericData]
    _ ≤ 30 * (Kernel.NatInstruction.dataSize contents + 1) := by omega

/-- Exact optional-fetch interface for the original Runs terminal
callback. It requires no executeSome HALT premise, source width, padding,
workspace oracle or externally provided answer. -/
theorem fetched_halt (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code)
    (store : Program.Store backend code) (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool)
    (ready : Source.Ready input logical events contents) (position : logical.pc = pc.val)
    (fetched : code[logical.pc]? = some .halt) :
    ∃ (terminal : Program.State backend code),
      TM2.step (Program.program backend core code) terminal = none ∧
      Source.Ready input logical events terminal.stk ∧
      ∃ path : ActualPath (TM2.step (Program.program backend core code))
        (Program.atEntry backend code pc store contents) terminal,
        path.posts.length ≤ 30 * (Kernel.NatInstruction.dataSize contents + 1) := by
  have fetchedSyntax : (code[pc.val]'pc.isLt) = .halt := by
    apply Option.some.inj
    simpa only [position, Array.getElem?_eq_getElem pc.isLt] using fetched
  exact halt_step backend core code pc store input logical events contents ready fetchedSyntax

theorem fetched_halt_polynomial (backend : ISA.RatBackend) (core : Bool) (code : Program) :
    ∃ C D : Nat, 0 < C ∧ 0 < D ∧
      ∀ (pc : Program.PC code) (store : Program.Store backend code) (input : List Cell)
        (logical : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool),
        Source.Ready input logical events contents → logical.pc = pc.val → code[logical.pc]? = some .halt →
        ∃ (terminal : Program.State backend code), TM2.step (Program.program backend core code) terminal = none ∧
          Source.Ready input logical events terminal.stk ∧
          ∃ path : ActualPath (TM2.step (Program.program backend core code))
            (Program.atEntry backend code pc store contents) terminal,
            path.posts.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  refine ⟨30, 1, by decide, by decide, ?_⟩
  intro pc store input logical events contents ready position fetched
  obtain ⟨terminal, halted, done, path, time⟩ := fetched_halt backend core code pc store input logical events contents ready position fetched
  refine ⟨terminal, halted, done, path, ?_⟩
  rw [pow_one]
  exact time.trans (Nat.mul_le_mul_left 30 (by omega))

end PDROC.BitVM.VM.CFG.Refinement
