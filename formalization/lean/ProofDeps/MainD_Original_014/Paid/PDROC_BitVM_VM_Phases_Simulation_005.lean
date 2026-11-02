module

public import Paid.PDROC_BitVM_VM_Phases_Source_003
public import Paid.PDROC_BitVM_VM_CFG_Complete_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Calls

open Turing PaperProofs.Paid.Computation

/-- Both actual source phases use the complete original-RAM simulation.
The compiler, positive coefficient and degree are fixed before inputs.
The source Runs certificate and true bank/reset Ready are supplied by
their actual producers; no callback is an original paper premise. -/
theorem source_local (backend : ISA.RatBackend) (prepareCode coreCode : Program) (core : Bool) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      ∀ (input : List Cell) (states : List PaperProofs.Paid.Computation.State)
        (logicalFinal : PaperProofs.Paid.Computation.State) (contents : ISA.Stack → List Bool),
        input.length = Log.BankMount.fieldCount core →
        Runs (sourceCode core prepareCode coreCode) input states logicalFinal →
        Source.Ready input PaperProofs.Paid.Computation.initial [] contents →
        LocalRun backend prepareCode coreCode (sourcePhase core) contents
          (fun data => Source.Ready input logicalFinal
            (BoundaryBudget.actualHistory (sourceCode core prepareCode coreCode) states) data)
          (CFG.Complete.totalBudget C d (sourceCode core prepareCode coreCode) input states + 1) := by
  obtain ⟨C,d,positiveC,positiveD,compiled⟩ :=
    CFG.Complete.complete_trace backend core (sourceCode core prepareCode coreCode)
  refine ⟨C,d,positiveC,positiveD,?_⟩
  intro input states logicalFinal contents size actual ready
  obtain ⟨trace,terminal,head,chain,last,halt,represented,time⟩ :=
    compiled input states logicalFinal contents size actual ready
  cases core
  · exact ⟨trace,terminal,head,chain,last,halt,represented,time⟩
  · exact ⟨trace,terminal,head,chain,last,halt,represented,time⟩

/-- The SAME selected complete source trace is inlined into the actual
eight-phase code. Other phase stores remain finite saved control, and
the endpoint's observable tape relation is unchanged. -/
theorem source_caller (backend : ISA.RatBackend) (prepareCode coreCode : Program) (core : Bool) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      ∀ (input : List Cell) (states : List PaperProofs.Paid.Computation.State)
        (logicalFinal : PaperProofs.Paid.Computation.State) (contents : ISA.Stack → List Bool)
        (store : Store backend prepareCode coreCode),
        input.length = Log.BankMount.fieldCount core →
        Runs (sourceCode core prepareCode coreCode) input states logicalFinal →
        Source.Ready input PaperProofs.Paid.Computation.initial [] contents →
        CallerRun backend prepareCode coreCode (sourcePhase core) store contents
          (fun data => Source.Ready input logicalFinal
            (BoundaryBudget.actualHistory (sourceCode core prepareCode coreCode) states) data)
          (CFG.Complete.totalBudget C d (sourceCode core prepareCode coreCode) input states + 1) := by
  obtain ⟨C,d,positiveC,positiveD,compiled⟩ := source_local backend prepareCode coreCode core
  refine ⟨C,d,positiveC,positiveD,?_⟩
  intro input states logicalFinal contents store size actual ready
  exact local_to_caller backend prepareCode coreCode (sourcePhase core) store contents _ _
    (compiled input states logicalFinal contents size actual ready)

end PDROC.BitVM.VM.Phases.Calls
