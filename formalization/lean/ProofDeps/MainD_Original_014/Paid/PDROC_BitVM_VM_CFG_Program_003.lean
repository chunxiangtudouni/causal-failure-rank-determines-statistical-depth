module

public import Paid.PDROC_BitVM_VM_CFG_Program_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Program

open Turing PaperProofs.Paid.Computation

/-- The entry/reset is one actual source transition, with its literal
finite store loaded by the old family program. All 32 stacks carry.
This lemma is not a free workspace initialization. -/
def afterEntry (backend : ISA.RatBackend) (code : Program) (phase : Phase code)
    (store : Store backend code) (contents : ISA.Stack → List Bool) : State backend code :=
  ⟨some (Source.localLabel (Source.Dispatch.LocalLabel (OpcodeLabel backend code) Cleanup.Label)
      phase (localStart backend code phase)),
    Function.update store phase (localInitial backend code phase), contents⟩

theorem entry_edge (backend : ISA.RatBackend) (core : Bool) (code : Program) (phase : Phase code)
    (store : Store backend code) (contents : ISA.Stack → List Bool) :
    TM2.step (program backend core code) (⟨some (phaseEntry backend code phase), store, contents⟩ : State backend code) =
      some (afterEntry backend code phase store contents) := rfl

theorem opcode_return_edge (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : PC code)
    (store : Store backend code) (contents : ISA.Stack → List Bool) :
    TM2.step (program backend core code)
      (⟨some (phaseReturn backend code (.opcode pc)), store, contents⟩ : State backend code) =
      some ⟨some (cleanupEntry backend code), setSelected backend code (chooseNext backend code pc store) store, contents⟩ := by
  exact Source.Dispatch.opcode_return_edge (OpcodeLabel backend code) (OpcodeStore backend code) Cleanup.Label (Cleanup.Store Unit)
    (opcodeProgram backend core code) (opcodeStart backend code) (opcodeInitial backend code)
    (Cleanup.program Unit) Cleanup.startLabel (none, ()) (chooseNext backend code) pc store contents

theorem selected_set (backend : ISA.RatBackend) (code : Program) (next : Option (PC code))
    (store : Store backend code) :
    selected backend code (setSelected backend code next store) = next :=
  Source.Dispatch.selected_set (OpcodeStore backend code) (Cleanup.Store Unit) next store

theorem cleanup_reset_preserves_selected (backend : ISA.RatBackend) (code : Program) (store : Store backend code) :
    selected backend code (Function.update store .cleanup (localInitial backend code .cleanup)) =
      selected backend code store :=
  Source.Dispatch.cleanup_reset_preserves_selected (OpcodeStore backend code) (Cleanup.Store Unit)
    (opcodeInitial backend code) (none, ()) store

theorem cleanup_return_some (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : PC code)
    (store : Store backend code) (contents : ISA.Stack → List Bool) (observed : selected backend code store = some pc) :
    TM2.step (program backend core code)
      (⟨some (phaseReturn backend code .cleanup), store, contents⟩ : State backend code) =
      some (atEntry backend code pc store contents) := by
  exact Source.Dispatch.cleanup_return_some (OpcodeLabel backend code) (OpcodeStore backend code) Cleanup.Label (Cleanup.Store Unit)
    (opcodeProgram backend core code) (opcodeStart backend code) (opcodeInitial backend code)
    (Cleanup.program Unit) Cleanup.startLabel (none, ()) (chooseNext backend code) pc store contents observed

theorem cleanup_return_none (backend : ISA.RatBackend) (core : Bool) (code : Program)
    (store : Store backend code) (contents : ISA.Stack → List Bool) (observed : selected backend code store = none) :
    TM2.step (program backend core code)
      (⟨some (phaseReturn backend code .cleanup), store, contents⟩ : State backend code) =
      some ⟨some (metadataHalt backend code), store, contents⟩ := by
  exact Source.Dispatch.cleanup_return_none (OpcodeLabel backend code) (OpcodeStore backend code) Cleanup.Label (Cleanup.Store Unit)
    (opcodeProgram backend core code) (opcodeStart backend code) (opcodeInitial backend code)
    (Cleanup.program Unit) Cleanup.startLabel (none, ()) (chooseNext backend code) store contents observed

theorem metadata_halt_edge (backend : ISA.RatBackend) (core : Bool) (code : Program)
    (store : Store backend code) (contents : ISA.Stack → List Bool) :
    TM2.step (program backend core code) (⟨some (metadataHalt backend code), store, contents⟩ : State backend code) =
      some ⟨none, store, contents⟩ := rfl

theorem terminal_halts (backend : ISA.RatBackend) (core : Bool) (code : Program)
    (store : Store backend code) (contents : ISA.Stack → List Bool) :
    TM2.step (program backend core code) (⟨none, store, contents⟩ : State backend code) = none := rfl

end PDROC.BitVM.VM.CFG.Program
