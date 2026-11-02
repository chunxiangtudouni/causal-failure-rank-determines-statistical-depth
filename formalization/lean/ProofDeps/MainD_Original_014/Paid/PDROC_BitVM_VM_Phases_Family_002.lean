module

public import Paid.PDROC_BitVM_VM_Phases_Program_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Phases

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native

theorem source_supports (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase) :
    TM2.Supports (source backend prepareCode coreCode phase)
      (Finset.univ : Finset (LocalLabel backend prepareCode coreCode phase)) := by
  cases phase with
  | mountRaw => exact Log.BankMount.supports false
  | mountPrepared => exact Log.BankMount.supports true
  | resetPrepare | resetCore => exact Kernel.Reset.supports
  | prepare => exact CFG.Program.supports backend false prepareCode
  | core => exact CFG.Program.supports backend true coreCode
  | finalizePrepare | finalizeCore => exact Codec.Finalize.supports

theorem supports (backend : ISA.RatBackend) (prepareCode coreCode : Program) :
    TM2.Supports (program backend prepareCode coreCode) (Finset.univ : Finset (Label backend prepareCode coreCode)) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    exact Control.Indirect.statement_support (program backend prepareCode coreCode label)

def lowerBefore (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (contents : ISA.Stack → List Bool) :
    TM2.Cfg ISA.Alphabet (LocalLabel backend prepareCode coreCode phase) (LocalStore backend prepareCode coreCode phase) :=
  ⟨some (start backend prepareCode coreCode phase),initial backend prepareCode coreCode phase,contents⟩

def entryState (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool) : State backend prepareCode coreCode :=
  ⟨some (Kernel.CallFamily.labels (LocalLabel backend prepareCode coreCode) phase (start backend prepareCode coreCode phase)),
    Function.update store phase (initial backend prepareCode coreCode phase),contents⟩

theorem initialized_cfg (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool) :
    Kernel.CallFamily.cfg (LocalLabel backend prepareCode coreCode) (LocalStore backend prepareCode coreCode) phase
      (fun other => store other.val) (lowerBefore backend prepareCode coreCode phase contents) =
      entryState backend prepareCode coreCode phase store contents := by
  change (⟨some (Kernel.CallFamily.labels (LocalLabel backend prepareCode coreCode) phase (start backend prepareCode coreCode phase)),
    Kernel.CallFamily.split (LocalStore backend prepareCode coreCode) phase
      (initial backend prepareCode coreCode phase,fun other => store other.val),contents⟩ : State backend prepareCode coreCode) = _
  congr 1

theorem initial_cfg (backend : ISA.RatBackend) (prepareCode coreCode : Program) (contents : ISA.Stack → List Bool) :
    entryState backend prepareCode coreCode .mountRaw (initial backend prepareCode coreCode) contents =
      before backend prepareCode coreCode contents := by
  change (⟨some (Kernel.CallFamily.labels (LocalLabel backend prepareCode coreCode) .mountRaw
    (start backend prepareCode coreCode .mountRaw)),
    Function.update (initial backend prepareCode coreCode) .mountRaw ((initial backend prepareCode coreCode) .mountRaw),
    contents⟩ : State backend prepareCode coreCode) = _
  rw [Function.update_eq_self]
  rfl

/-- Genuine next-phase load/goto, paid separately from every callee.
Its hypothesis is a fixed code equation, never a per-input run oracle. -/
theorem advance (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase next : Phase)
    (follows : resume backend prepareCode coreCode phase = entry backend prepareCode coreCode next)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool) :
    TM2.step (program backend prepareCode coreCode)
      (⟨some (Kernel.CallFamily.returnLabel (LocalLabel backend prepareCode coreCode) phase),store,contents⟩ :
        State backend prepareCode coreCode) = some (entryState backend prepareCode coreCode next store contents) := by
  change some (TM2.stepAux (resume backend prepareCode coreCode phase) store contents) = _
  rw [follows]
  rfl

theorem finish (backend : ISA.RatBackend) (prepareCode coreCode : Program)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool) :
    TM2.step (program backend prepareCode coreCode)
      (⟨some (Kernel.CallFamily.returnLabel (LocalLabel backend prepareCode coreCode) .finalizeCore),store,contents⟩ :
        State backend prepareCode coreCode) = some ⟨none,store,contents⟩ := rfl

end PDROC.BitVM.VM.Phases
