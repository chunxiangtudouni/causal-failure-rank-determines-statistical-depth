module

public import Paid.PDROC_BitVM_VM_CFG_Refinement_001
public import Paid.PDROC_BitVM_VM_CFG_Step_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Refinement

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Common.IO

abbrev OpcodeState (backend : ISA.RatBackend) (code : Program) (pc : Program.PC code) :=
  LocalState backend code (Program.localChoice code pc)

/-- The actual returned opcode field is recovered from the existing Pi
split, not recomputed from a logical RAM state or an expected answer. -/
theorem returned_store_self (backend : ISA.RatBackend) (code : Program) (pc : Program.PC code)
    (store : Program.Store backend code) (value : Program.OpcodeStore backend code pc) :
    Step.opcodeStore (Program.OpcodeStore backend code) pc store value (.opcode pc) = value :=
  congrArg Prod.fst
    ((Equiv.piSplitAt (Source.Dispatch.Phase.opcode pc)
      (Step.FamilyStores (Program.OpcodeStore backend code))).apply_symm_apply
      (value, fun other => store other.val))

/-- One local actual run is embedded once, then the real metadata load,
cleaner entry/reset, nine clears, cleanup return and selected next-entry
edge are appended on that SAME path. No physical state is replaced. -/
theorem lift_local (backend : ISA.RatBackend) (core : Bool) (code : Program)
    (pc target : Program.PC code) (store : Program.Store backend code) (contents : ISA.Stack → List Bool)
    (run : List (OpcodeState backend code pc)) (final : OpcodeState backend code pc)
    (actual : LocalActualRun backend core code (Program.localChoice code pc) contents run final)
    (input : List Cell) (next : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent)
    (observed : Source.Observables input next events final.stk)
    (selected : Program.opcodeNext backend code pc final.var = some target) :
    ∃ (nextStore : Program.Store backend code)
      (path : ActualPath (TM2.step (Program.program backend core code))
        (Program.atEntry backend code pc store contents)
        (Program.atEntry backend code target nextStore (Cleanup.cleaned final.stk))),
      Source.Ready input next events (Cleanup.cleaned final.stk) ∧
      path.posts.length ≤ run.length + 20 * (Cleanup.dataSize final.stk + 1) + 8 := by
  have selectedReturned : Program.chooseNext backend code pc
      (Step.opcodeStore (Program.OpcodeStore backend code) pc store final.var) = some target := by
    change Program.opcodeNext backend code pc
      (Step.opcodeStore (Program.OpcodeStore backend code) pc store final.var (.opcode pc)) = some target
    rw [returned_store_self]
    exact selected
  obtain ⟨path, ready, time⟩ := Step.step_some
    (Program.OpcodeLabel backend code) (Program.OpcodeStore backend code)
    (Program.opcodeProgram backend core code) (Program.opcodeStart backend code) (Program.opcodeInitial backend code)
    (Program.chooseNext backend code) pc target store contents run final
    actual.1 actual.2.1 actual.2.2.1 actual.2.2.2 input next events observed selectedReturned
  exact ⟨_, path, ready, time⟩

end PDROC.BitVM.VM.CFG.Refinement
