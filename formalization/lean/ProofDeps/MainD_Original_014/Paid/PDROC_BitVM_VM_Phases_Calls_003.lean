module

public import Paid.PDROC_BitVM_VM_Phases_Calls_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Calls

open Turing PaperProofs.Paid.Computation
open scoped BigOperators

/-- The genuine reset keeps the already mounted physical readonly bank
and produces ORIGINAL RAM.initial, including true empty history/output/
allwork. No original source run or new bank is manufactured here. -/
theorem reset_call (backend : ISA.RatBackend) (prepareCode coreCode : Program) (core : Bool)
    (store : Store backend prepareCode coreCode) (input : List Cell) (contents : ISA.Stack → List Bool)
    (bankAt : Log.InputLoad.BankAt input contents) :
    CallerRun backend prepareCode coreCode (resetPhase core) store contents
      (fun data => Source.Ready input PaperProofs.Paid.Computation.initial [] data ∧
        ∀ role, Kernel.Reset.readonly role = true → data role = contents role)
      (32 * ((∑ role : ISA.Stack, (contents role).length) + 7) + 2) := by
  obtain ⟨run, final, head, chain, last, halt, registers, bank, empty, time⟩ :=
    Kernel.Reset.initial_ram_runs contents none
  have actualBank : Log.InputLoad.BankAt input final.stk := by
    intro field
    have read : Kernel.Reset.readonly (Log.BankDrain.bankSlot field) = true := by
      simp only [Kernel.Reset.readonly, decide_eq_true_eq]
      change 1 ≤ field.val + 1 ∧ field.val + 1 ≤ 13
      omega
    exact (bank (Log.BankDrain.bankSlot field) read).trans (bankAt field)
  have actualEmpty : ∀ role : ISA.Stack, role.val = 0 ∨ 21 ≤ role.val → final.stk role = [] := by
    intro role shape
    apply empty role
    rcases shape with zero | large
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr large
  have represented : Source.Ready input PaperProofs.Paid.Computation.initial [] final.stk :=
    Source.initial_ready input final.stk registers actualBank actualEmpty
  have original : ∃ (selected : List Kernel.Reset.State) (returned : Kernel.Reset.State),
      selected.head? = some (⟨some (Kernel.Reset.clearLabel 0), (none, ()), contents⟩ : Kernel.Reset.State) ∧
      selected.IsChain (fun a b => TM2.step Kernel.Reset.program a = some b) ∧
      selected.getLast? = some returned ∧ TM2.step Kernel.Reset.program returned = none ∧
      (Source.Ready input PaperProofs.Paid.Computation.initial [] returned.stk ∧
        ∀ role, Kernel.Reset.readonly role = true → returned.stk role = contents role) ∧
      selected.length ≤ 32 * ((∑ role : ISA.Stack, (contents role).length) + 7) + 2 :=
    ⟨run, final, head, chain, last, halt, ⟨represented, bank⟩, time⟩
  have callee : LocalRun backend prepareCode coreCode (resetPhase core) contents
      (fun data => Source.Ready input PaperProofs.Paid.Computation.initial [] data ∧
        ∀ role, Kernel.Reset.readonly role = true → data role = contents role)
      (32 * ((∑ role : ISA.Stack, (contents role).length) + 7) + 2) := by
    cases core <;> exact original
  exact local_to_caller backend prepareCode coreCode (resetPhase core) store contents _ _ callee

end PDROC.BitVM.VM.Phases.Calls
