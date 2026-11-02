module

public import Paid.PDROC_BitVM_VM_Phases_Calls_001
public import Paid.PDROC_BitVM_Common_Occupancy_003
public import Paid.PDROC_BitVM_Kernel_NatInstruction_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Calls

open Turing PaperProofs.Paid.Computation
open scoped BigOperators

/-! SOURCE ONLY. The push allowance belongs to the FIXED whole eight-
phase program, before ALL inputs, physical callers, stores and paths.
Every old stack is charged by its actual entry dataSize. -/

def globalPushCap (backend : ISA.RatBackend) (prepareCode coreCode : Program) : ℕ :=
  Common.sourcePushCap (program backend prepareCode coreCode)
    (Finset.univ : Finset (Label backend prepareCode coreCode))

/-- Occupancy of the given caller list, not another selected run. The
real return configuration is a member of this same path. Summing the32
actual stack bounds includes old readonly, registers, heap and scratch. -/
theorem caller_data_bound (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool) (bound : ℕ)
    (run : List (State backend prepareCode coreCode)) (returned : State backend prepareCode coreCode)
    (head : run.head? = some (entryState backend prepareCode coreCode phase store contents))
    (chain : run.IsChain (fun a b => TM2.step (program backend prepareCode coreCode) a = some b))
    (last : run.getLast? = some returned) (clock : run.length ≤ bound) :
    Kernel.NatInstruction.dataSize returned.stk ≤
      32 * (Kernel.NatInstruction.dataSize contents + globalPushCap backend prepareCode coreCode * bound) := by
  cases run with
  | nil => simp only [List.head?_nil, reduceCtorEq] at head
  | cons first rest =>
    have same : first = entryState backend prepareCode coreCode phase store contents := Option.some.inj head
    subst first
    have supported : (entryState backend prepareCode coreCode phase store contents).l ∈
        Finset.insertNone (Finset.univ : Finset (Label backend prepareCode coreCode)) :=
      Finset.some_mem_insertNone.mpr (Finset.mem_univ _)
    have initial : ∀ role : ISA.Stack,
        ((entryState backend prepareCode coreCode phase store contents).stk role).length ≤
          Kernel.NatInstruction.dataSize contents := Kernel.NatInstruction.dataSize_each contents
    have occupied := Common.source_path_occupancy (program backend prepareCode coreCode)
      (Finset.univ : Finset (Label backend prepareCode coreCode))
      (PDROC.BitVM.VM.Phases.supports backend prepareCode coreCode)
      (entryState backend prepareCode coreCode phase store contents) rest
      (Kernel.NatInstruction.dataSize contents) supported initial chain
    have member : returned ∈ entryState backend prepareCode coreCode phase store contents :: rest :=
      List.mem_of_getLast? last
    have restBound : rest.length ≤ bound := by simp only [List.length_cons] at clock; omega
    have every : ∀ role : ISA.Stack, (returned.stk role).length ≤
        Kernel.NatInstruction.dataSize contents + globalPushCap backend prepareCode coreCode * bound := by
      intro role
      have actual := (occupied returned member).2 role
      change (returned.stk role).length ≤ Kernel.NatInstruction.dataSize contents +
        globalPushCap backend prepareCode coreCode * rest.length at actual
      exact actual.trans (Nat.add_le_add_left
        (Nat.mul_le_mul_left (globalPushCap backend prepareCode coreCode) restBound) _)
    change (Finset.univ : Finset ISA.Stack).sum (fun role => (returned.stk role).length) ≤ _
    calc
      _ ≤ (Finset.univ : Finset ISA.Stack).sum (fun _ => Kernel.NatInstruction.dataSize contents +
          globalPushCap backend prepareCode coreCode * bound) := Finset.sum_le_sum (fun role _ => every role)
      _ = _ := by simp

/-- Strengthen precisely the supplied CallerRun: same list, returned
state, return label, semantic post, Pi-store frame and original clock.
Only a proof of the actual endpoint size is added for the next phase. -/
theorem CallerRun.with_data_bound (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool)
    (post : (ISA.Stack → List Bool) → Prop) (bound : ℕ)
    (actual : CallerRun backend prepareCode coreCode phase store contents post bound) :
    CallerRun backend prepareCode coreCode phase store contents
      (fun data => post data ∧ Kernel.NatInstruction.dataSize data ≤
        32 * (Kernel.NatInstruction.dataSize contents + globalPushCap backend prepareCode coreCode * bound)) bound := by
  obtain ⟨run, returned, head, chain, last, label, represented, saved, clock⟩ := actual
  exact ⟨run, returned, head, chain, last, label,
    ⟨represented, caller_data_bound backend prepareCode coreCode phase store contents bound
      run returned head chain last clock⟩, saved, clock⟩

end PDROC.BitVM.VM.Phases.Calls
