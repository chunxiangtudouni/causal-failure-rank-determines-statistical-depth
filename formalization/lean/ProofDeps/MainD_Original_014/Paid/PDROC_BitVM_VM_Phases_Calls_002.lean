module

public import Paid.PDROC_BitVM_VM_Phases_Calls_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Calls

open Turing PaperProofs.Paid.Computation

/-- Physical raw6/prepared13 remount, including arbitrary old caller
words and banks. No source evaluator, bank override or free ROM switch.
Full Mounted data/frame and exact old-input cost survive the SAME map. -/
theorem mount_call (backend : ISA.RatBackend) (prepareCode coreCode : Program) (core : Bool)
    (store : Store backend prepareCode coreCode) (cells : List Cell) (contents : ISA.Stack → List Bool)
    (size : cells.length = Log.BankMount.fieldCount core) (input : contents 0 = encodeBits cells) :
    CallerRun backend prepareCode coreCode (mountPhase core) store contents
      (Log.BankMount.Mounted contents cells [])
      (1000 * (Log.BankMount.preCap contents + (encodeBits cells).length + 1)) := by
  let physical : Log.BankMount.State := ⟨some Log.BankMount.startLabel, default, contents⟩
  obtain ⟨run, final, head, chain, last, halt, done, flag, mounted, time⟩ :=
    Log.BankMount.runs_poly core cells [] physical rfl size (by simpa only [List.append_nil] using input)
  have original : ∃ (selected : List Log.BankMount.State) (returned : Log.BankMount.State),
      selected.head? = some physical ∧
      selected.IsChain (fun a b => TM2.step (Log.BankMount.program core) a = some b) ∧
      selected.getLast? = some returned ∧ TM2.step (Log.BankMount.program core) returned = none ∧
      Log.BankMount.Mounted contents cells [] returned.stk ∧
      selected.length ≤ 1000 * (Log.BankMount.preCap contents + (encodeBits cells).length + 1) :=
    ⟨run, final, head, chain, last, halt, mounted, time⟩
  have callee : LocalRun backend prepareCode coreCode (mountPhase core) contents
      (Log.BankMount.Mounted contents cells [])
      (1000 * (Log.BankMount.preCap contents + (encodeBits cells).length + 1)) := by
    cases core <;> exact original
  exact local_to_caller backend prepareCode coreCode (mountPhase core) store contents _ _ callee

end PDROC.BitVM.VM.Phases.Calls
