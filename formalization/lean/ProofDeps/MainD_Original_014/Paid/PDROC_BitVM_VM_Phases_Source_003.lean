module

public import Paid.PDROC_BitVM_VM_Phases_Calls_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Calls

open Turing PaperProofs.Paid.Computation

def sourcePhase (core : Bool) : Phase := if core then .core else .prepare
def sourceCode (core : Bool) (prepareCode coreCode : Program) : Program := if core then coreCode else prepareCode

/-- Map the SAME compiled-source witness into the eight-phase caller.
The source VM proof supplies its own real halt, observable event tapes
and clock; this bridge does not assume or inject a prepared13 tape. -/
theorem source_call (backend : ISA.RatBackend) (prepareCode coreCode : Program) (core : Bool)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool)
    (post : (ISA.Stack → List Bool) → Prop) (bound : ℕ)
    (run : List (CFG.Program.State backend (sourceCode core prepareCode coreCode)))
    (final : CFG.Program.State backend (sourceCode core prepareCode coreCode))
    (head : run.head? = some (CFG.Program.before backend (sourceCode core prepareCode coreCode) contents))
    (chain : run.IsChain (fun a b => TM2.step (CFG.Program.program backend core (sourceCode core prepareCode coreCode)) a = some b))
    (last : run.getLast? = some final)
    (halt : TM2.step (CFG.Program.program backend core (sourceCode core prepareCode coreCode)) final = none)
    (represented : post final.stk) (time : run.length ≤ bound) :
    CallerRun backend prepareCode coreCode (sourcePhase core) store contents post bound := by
  apply local_to_caller
  cases core
  · exact ⟨run,final,head,chain,last,halt,represented,time⟩
  · exact ⟨run,final,head,chain,last,halt,represented,time⟩

/-- Turn a source ActualPath, including its genuine final halt state,
into the one list consumed by source_call. The extra initial state is
charged in the clock and is the actual existing entry, not a reset. -/
theorem source_path_call (backend : ISA.RatBackend) (prepareCode coreCode : Program) (core : Bool)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool)
    (post : (ISA.Stack → List Bool) → Prop) (bound : ℕ)
    (final : CFG.Program.State backend (sourceCode core prepareCode coreCode))
    (path : PDROC.BitVM.Common.IO.ActualPath
      (TM2.step (CFG.Program.program backend core (sourceCode core prepareCode coreCode)))
      (CFG.Program.before backend (sourceCode core prepareCode coreCode) contents) final)
    (halt : TM2.step (CFG.Program.program backend core (sourceCode core prepareCode coreCode)) final = none)
    (represented : post final.stk) (time : path.posts.length+1 ≤ bound) :
    CallerRun backend prepareCode coreCode (sourcePhase core) store contents post bound :=
  source_call backend prepareCode coreCode core store contents post bound
    (CFG.Program.before backend (sourceCode core prepareCode coreCode) contents :: path.posts)
    final rfl path.chain path.last halt represented time

end PDROC.BitVM.VM.Phases.Calls
