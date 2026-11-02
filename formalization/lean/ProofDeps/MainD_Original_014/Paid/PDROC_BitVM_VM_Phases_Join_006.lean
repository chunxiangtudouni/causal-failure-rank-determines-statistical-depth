module

public import Paid.PDROC_BitVM_VM_Phases_Calls_001
public import Paid.PDROC_BitVM_Common_IO_Paths_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Calls

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Common.IO

/-- Re-express the selected list witness as a path, without selecting a
second run or altering its physical endpoint. The only discarded list
entry is the duplicated starting configuration, and its cost is retained. -/
theorem caller_path (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool)
    (post : (ISA.Stack → List Bool) → Prop) (bound : ℕ)
    (actual : CallerRun backend prepareCode coreCode phase store contents post bound) :
    ∃ returned : State backend prepareCode coreCode,
      returned.l = some (Kernel.CallFamily.returnLabel (LocalLabel backend prepareCode coreCode) phase) ∧
      post returned.stk ∧
      ∃ path : ActualPath (TM2.step (program backend prepareCode coreCode))
        (entryState backend prepareCode coreCode phase store contents) returned,
        path.posts.length+1 ≤ bound := by
  obtain ⟨run,returned,head,chain,last,label,represented,_saved,time⟩ := actual
  cases run with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have same : start = entryState backend prepareCode coreCode phase store contents := Option.some.inj head
    subst start
    exact ⟨returned,label,represented,⟨rest,chain,last⟩,time⟩

/-- The transition between two source phases is the existing REAL
load/goto. No readonly bank, data tape or local store is replaced here. -/
theorem advance_path (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase next : Phase)
    (follows : resume backend prepareCode coreCode phase = entry backend prepareCode coreCode next)
    (returned : State backend prepareCode coreCode)
    (label : returned.l = some (Kernel.CallFamily.returnLabel (LocalLabel backend prepareCode coreCode) phase)) :
    ∃ path : ActualPath (TM2.step (program backend prepareCode coreCode)) returned
      (entryState backend prepareCode coreCode next returned.var returned.stk), path.posts.length = 1 := by
  have edge : TM2.step (program backend prepareCode coreCode) returned =
      some (entryState backend prepareCode coreCode next returned.var returned.stk) := by
    rcases returned with ⟨current,finiteStore,physical⟩
    change current = some (Kernel.CallFamily.returnLabel (LocalLabel backend prepareCode coreCode) phase) at label
    subst current
    exact advance backend prepareCode coreCode phase next follows finiteStore physical
  exact ⟨ActualPath.single edge,rfl⟩

/-- Fetched core HALT has already run the real scratch cleaner, then
Finalize supplied forward bytes on0. This final caller edge preserves
those exact bytes and genuinely halts the whole phase program. -/
theorem finish_path (backend : ISA.RatBackend) (prepareCode coreCode : Program)
    (returned : State backend prepareCode coreCode)
    (label : returned.l = some (Kernel.CallFamily.returnLabel (LocalLabel backend prepareCode coreCode) .finalizeCore)) :
    ∃ terminal : State backend prepareCode coreCode,
      TM2.step (program backend prepareCode coreCode) terminal = none ∧ terminal.stk = returned.stk ∧
      ∃ path : ActualPath (TM2.step (program backend prepareCode coreCode)) returned terminal,
        path.posts.length = 1 := by
  let terminal : State backend prepareCode coreCode := ⟨none,returned.var,returned.stk⟩
  have edge : TM2.step (program backend prepareCode coreCode) returned = some terminal := by
    rcases returned with ⟨current,finiteStore,physical⟩
    change current = some (Kernel.CallFamily.returnLabel (LocalLabel backend prepareCode coreCode) .finalizeCore) at label
    subst current
    exact finish backend prepareCode coreCode finiteStore physical
  exact ⟨terminal,rfl,rfl,ActualPath.single edge,rfl⟩

end PDROC.BitVM.VM.Phases.Calls
