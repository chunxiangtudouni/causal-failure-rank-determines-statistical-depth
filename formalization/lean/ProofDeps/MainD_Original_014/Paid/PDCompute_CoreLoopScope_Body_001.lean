module

public import Paid.PDCompute_CoreSearchLoop_BodyCalls_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.CoreLoopScope

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver hiding HeapList
open PDMenu.ComputeFrame RootD27.Core PDCompute.CoreSearchLoop

/-- Exactly CallBodySpec008, with the lower PC bound added to the SAME
existential trace. This is an internal literal-body certificate for Root;
it is not a new premise on any original input or an independent witness. -/
def CallBodyLowerSpec (program : Program) (labels : RoutineLabels) (input : List Cell)
    (P : Parameters) (fee : ℚ) (origin : ℕ) (body : List Instruction)
    (budget : ℕ) (region : Finset ℕ) (bodyCost callConstant : ℕ) : Prop :=
  ∀ j : ℕ, j < P.bisectionBudget fee → ∀ before : State,
    before.pc=bodyPC origin → Ready P fee before →
    SearchStateRep P fee before (source P fee j) →
    before.heap 28=.natural (P.bisectionBudget fee-j) →
    RootD27.Bits.SafeBits before budget → FetchesCode program before.pc body →
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace ≤ bodyCost ∧ after.pc=decrementPC origin body ∧
      Ready P fee after ∧ SearchStateRep P fee after (source P fee (j+1)) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      (∀ state∈trace, RegionMemory before state region) ∧
      (∀ state∈trace, RootD27.Bits.SafeBits state budget) ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace ≤ 1 ∧
      actualSolveRequests labels trace=P.nextSolveRequests fee (source P fee j) ∧
      SolverCallRefinement program labels P fee callConstant trace ∧
      ∀ state∈trace, origin ≤ state.pc

theorem CallBodyLowerSpec.thin {program : Program} {labels : RoutineLabels} {input : List Cell}
    {P : Parameters} {fee : ℚ} {origin : ℕ} {body : List Instruction}
    {budget : ℕ} {region : Finset ℕ} {bodyCost callConstant : ℕ}
    (actual : CallBodyLowerSpec program labels input P fee origin body budget region bodyCost callConstant) :
    CallBodySpec program labels input P fee origin body budget region bodyCost callConstant := by
  intro j inside before position ready represented counter safe fetched
  obtain ⟨trace,after,head,last,chain,cost,pc,afterReady,afterRep,afterCounter,output,memory,bits,count,requests,refinement,_lower⟩:=
    actual j inside before position ready represented counter safe fetched
  exact ⟨trace,after,head,last,chain,cost,pc,afterReady,afterRep,afterCounter,output,memory,bits,count,requests,refinement⟩

end PDCompute.CoreLoopScope
