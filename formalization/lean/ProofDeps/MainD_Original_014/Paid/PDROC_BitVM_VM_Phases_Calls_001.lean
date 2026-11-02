module

public import Paid.PDROC_BitVM_VM_Phases_Family_002
public import Paid.PDROC_BitVM_VM_Source_Representation_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Calls

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native

abbrev LocalState (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase) :=
  TM2.Cfg ISA.Alphabet (LocalLabel backend prepareCode coreCode phase) (LocalStore backend prepareCode coreCode phase)

/-- A proof-only selected genuine local callee, with its fixed actual
entry store. Concrete adapters below obtain this from old checked runs;
it is never a new original input, machine field or whole-run oracle. -/
def LocalRun (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (contents : ISA.Stack → List Bool) (post : (ISA.Stack → List Bool) → Prop) (bound : ℕ) : Prop :=
  ∃ (run : List (LocalState backend prepareCode coreCode phase)) (final : LocalState backend prepareCode coreCode phase),
    run.head? = some (lowerBefore backend prepareCode coreCode phase contents) ∧
    run.IsChain (fun a b => TM2.step (source backend prepareCode coreCode phase) a = some b) ∧
    run.getLast? = some final ∧ TM2.step (source backend prepareCode coreCode phase) final = none ∧
    post final.stk ∧ run.length ≤ bound

/-- The same actual local list after CallFamily's label/store map.
entryState is precisely the post-load state produced by the existing
Phases.advance edge. Its initialization changes no physical stack. -/
def CallerRun (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool)
    (post : (ISA.Stack → List Bool) → Prop) (bound : ℕ) : Prop :=
  ∃ (run : List (State backend prepareCode coreCode)) (returned : State backend prepareCode coreCode),
    run.head? = some (entryState backend prepareCode coreCode phase store contents) ∧
    run.IsChain (fun a b => TM2.step (program backend prepareCode coreCode) a = some b) ∧
    run.getLast? = some returned ∧
    returned.l = some (Kernel.CallFamily.returnLabel (LocalLabel backend prepareCode coreCode) phase) ∧
    post returned.stk ∧
    (∀ other, other ≠ phase → returned.var other = store other) ∧ run.length ≤ bound

theorem split_other (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase other : Phase)
    (different : other ≠ phase) (value : LocalStore backend prepareCode coreCode phase)
    (store : Store backend prepareCode coreCode) :
    Kernel.CallFamily.split (LocalStore backend prepareCode coreCode) phase
      (value, fun index => store index.val) other = store other := by
  change (if same : other = phase then same.symm.rec value else store other) = store other
  exact dite_eq_right different

/-- One given callee witness, not an independently chosen semantic and
resource trace. The source HALT edge becomes the real caller return;
the path's length and every physical endpoint stack are identical. -/
theorem local_to_caller (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool)
    (post : (ISA.Stack → List Bool) → Prop) (bound : ℕ)
    (localRun : LocalRun backend prepareCode coreCode phase contents post bound) :
    CallerRun backend prepareCode coreCode phase store contents post bound := by
  obtain ⟨run, final, head, chain, last, halt, represented, time⟩ := localRun
  obtain ⟨actual, returned, actualHead, actualChain, actualLast, label, data, vars, length⟩ :=
    Kernel.CallFamily.actual_return_trace (LocalLabel backend prepareCode coreCode) (LocalStore backend prepareCode coreCode)
      (source backend prepareCode coreCode) (resume backend prepareCode coreCode) phase
      (fun other => store other.val) run (lowerBefore backend prepareCode coreCode phase contents) final
      head chain last halt
  rw [initialized_cfg backend prepareCode coreCode phase store contents] at actualHead
  refine ⟨actual, returned, actualHead, actualChain, actualLast, label, ?_, ?_, ?_⟩
  · rw [data]
    exact represented
  · intro other different
    rw [vars]
    exact split_other backend prepareCode coreCode phase other different final.var store
  · rw [length]
    exact time

/-- Pure budget weakening on the SAME already selected caller path. -/
theorem CallerRun.mono (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool)
    (post : (ISA.Stack → List Bool) → Prop) (before after : ℕ)
    (actual : CallerRun backend prepareCode coreCode phase store contents post before) (larger : before ≤ after) :
    CallerRun backend prepareCode coreCode phase store contents post after := by
  obtain ⟨run, returned, head, chain, last, label, represented, saved, time⟩ := actual
  exact ⟨run, returned, head, chain, last, label, represented, saved, time.trans larger⟩

def mountPhase (core : Bool) : Phase := if core then .mountPrepared else .mountRaw
def resetPhase (core : Bool) : Phase := if core then .resetCore else .resetPrepare
def finalizePhase (core : Bool) : Phase := if core then .finalizeCore else .finalizePrepare

end PDROC.BitVM.VM.Phases.Calls
