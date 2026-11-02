module

public import Paid.PDCompute_CoreSearchLoop_CallWindows_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.CoreSearchLoop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver hiding HeapList
open PDMenu.ComputeFrame RootD27.Core

/-- Strengthening of the frozen resource ABI, using ONE existential trace
for all resources, the exact original next-request list and every ORIGINAL
common-epilogue solver window. Root supplies its actual body construction. -/
def CallBodySpec (program : Program) (labels : RoutineLabels) (input : List Cell)
    (P : Parameters) (fee : ℚ) (origin : ℕ) (body : List Instruction)
    (budget : ℕ) (region : Finset ℕ) (bodyCost callConstant : ℕ) : Prop :=
  ∀ j : ℕ,j<P.bisectionBudget fee → ∀ before : State,
    before.pc=bodyPC origin → Ready P fee before →
    SearchStateRep P fee before (source P fee j) →
    before.heap 28=.natural (P.bisectionBudget fee-j) →
    RootD27.Bits.SafeBits before budget → FetchesCode program before.pc body →
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤bodyCost ∧ after.pc=decrementPC origin body ∧
      Ready P fee after ∧ SearchStateRep P fee after (source P fee (j+1)) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state region) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace≤1 ∧
      actualSolveRequests labels trace=P.nextSolveRequests fee (source P fee j) ∧
      SolverCallRefinement program labels P fee callConstant trace

theorem CallBodySpec.resources {program : Program} {labels : RoutineLabels} {input : List Cell}
    {P : Parameters} {fee : ℚ} {origin : ℕ} {body : List Instruction}
    {budget : ℕ} {region : Finset ℕ} {bodyCost callConstant : ℕ}
    (actual : CallBodySpec program labels input P fee origin body budget region bodyCost callConstant) :
    BodySpec program labels input P fee origin body budget region bodyCost := by
  intro j inside before position ready represented counter safe fetched
  obtain ⟨trace,after,head,last,chain,cost,pc,afterReady,afterRep,afterCounter,output,memory,bits,count,_⟩:=
    actual j inside before position ready represented counter safe fetched
  exact ⟨trace,after,head,last,chain,cost,pc,afterReady,afterRep,afterCounter,output,memory,bits,count⟩

/-- Source requests contributed by exactly these remaining iterations.
No initialized endpoint request is re-counted in the loop. -/
def tailRequests (P : Parameters) (fee : ℚ) (start : ℕ) : ℕ→List ℚ
  | 0=>[]
  | remaining+1=>tailRequests P fee start remaining++P.nextSolveRequests fee (source P fee (start+remaining))

theorem tailRequests_head (P : Parameters) (fee : ℚ) (start remaining : ℕ) :
    tailRequests P fee start (remaining+1)=P.nextSolveRequests fee (source P fee start)++
      tailRequests P fee (start+1) remaining := by
  induction remaining with
  | zero => simp only [tailRequests,Nat.add_zero,List.nil_append,List.append_nil]
  | succ remaining ih =>
    rw [tailRequests,ih,tailRequests,List.append_assoc]
    have position : start+(remaining+1)=start+1+remaining:=by omega
    rw [position]

theorem tailRequests_source_log (P : Parameters) (fee : ℚ) (start remaining : ℕ) :
    (P.cachedSearchWithLog P.endpointCache fee (start+remaining)).2=
      (P.cachedSearchWithLog P.endpointCache fee start).2++tailRequests P fee start remaining := by
  induction remaining with
  | zero => simp only [Nat.add_zero,tailRequests,List.append_nil]
  | succ remaining ih =>
    have position : start+(remaining+1)=start+remaining+1:=by omega
    rw [position]
    change (P.cachedSearchWithLog P.endpointCache fee (start+remaining)).2++
      P.nextSolveRequests fee (P.cachedSearchWithLog P.endpointCache fee (start+remaining)).1=_
    rw [cachedSearchWithLog_state,ih,tailRequests,List.append_assoc]
    rfl

theorem tailRequests_full (P : Parameters) (fee : ℚ) :
    [0,P.Lambda]++tailRequests P fee 0 (P.bisectionBudget fee)=
      (P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2 := by
  have original:=tailRequests_source_log P fee 0 (P.bisectionBudget fee)
  simpa only [Nat.zero_add,cachedSearchWithLog] using original.symm

end PDCompute.CoreSearchLoop
