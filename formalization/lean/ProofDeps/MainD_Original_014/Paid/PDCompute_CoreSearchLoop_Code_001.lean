module

public import Paid.RootD27Core_SearchRepresentation_056
public import Paid.PDCompute_Nat_IncrementResources_016
public import Paid.PDCompute_SolverRegionSpace_124

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.CoreSearchLoop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver hiding HeapList
open PDMenu.ComputeFrame RootD27.Core
open PDLower.CalibrationCompute (HeapList loadSlot storeSlot)

def bodyPC (origin : ℕ) : ℕ := origin+4
def decrementPC (origin : ℕ) (body : List Instruction) : ℕ := origin+4+body.length
def backPC (origin : ℕ) (body : List Instruction) : ℕ := origin+12+body.length
def exitPC (origin : ℕ) (body : List Instruction) : ℕ := origin+body.length+13

/-- The original counter is physically loaded, decremented and stored.
The source exact/stopped cases still execute this outer counter update. -/
def decrementCode : List Instruction :=
  loadSlot 28 .index++[.constant .flag (.natural 1),.natOp .subtract .index .index .flag]++storeSlot 28 .index

def guardCode (origin : ℕ) (body : List Instruction) : List Instruction :=
  loadSlot 28 .index++[.branchZero .index (exitPC origin body) (bodyPC origin)]

/-- Fixed literal outer code. The body is an explicitly certified internal
component, later instantiated by Root's actual midpoint/solver/update code. -/
def code (origin : ℕ) (body : List Instruction) : List Instruction :=
  guardCode origin body++(body++(decrementCode++[.jump origin]))

theorem decrement_length : decrementCode.length=8 := rfl
theorem guard_length (origin : ℕ) (body : List Instruction) : (guardCode origin body).length=4 := rfl
theorem code_length (origin : ℕ) (body : List Instruction) : (code origin body).length=body.length+13 := by
  simp only [code,List.length_append,guard_length,decrement_length,List.length_cons,List.length_nil]
  omega

theorem body_fetch (program : Program) (origin : ℕ) (body : List Instruction)
    (fetched : FetchesCode program origin (code origin body)) :
    FetchesCode program (bodyPC origin) body := by
  have rest:=fetched.append_right
  simpa only [guard_length,bodyPC] using rest.append_left

theorem decrement_fetch (program : Program) (origin : ℕ) (body : List Instruction)
    (fetched : FetchesCode program origin (code origin body)) :
    FetchesCode program (decrementPC origin body) decrementCode := by
  have rest:=fetched.append_right.append_right
  simpa only [guard_length,decrementPC] using rest.append_left

theorem back_fetch (program : Program) (origin : ℕ) (body : List Instruction)
    (fetched : FetchesCode program origin (code origin body)) :
    program[backPC origin body]?=some (.jump origin) := by
  have last:=fetched.append_right.append_right.append_right
  have one:=last 0 (by change 0<1;decide)
  have actual : program[origin+4+body.length+8]?=some (.jump origin):=by
    simpa only [guard_length,decrement_length,Nat.add_zero,List.getElem?_cons_zero] using one
  have position : origin+4+body.length+8=backPC origin body:=by unfold backPC;omega
  simpa only [position] using actual

theorem guard_branch_fetch (program : Program) (origin : ℕ) (body : List Instruction)
    (fetched : FetchesCode program origin (code origin body)) :
    program[origin+3]?=some (.branchZero .index (exitPC origin body) (bodyPC origin)) := by
  have guard:=fetched.append_left
  exact guard 3 (by change 3<4;decide)

/-- Only genuine physically live caller data. Dirty old workspace and
output are unrestricted; their numerical budget is carried unchanged. -/
structure Ready (P : Parameters) (fee : ℚ) (state : State) : Prop where
  header : Header state 0 (fun slot=>state.heap slot)
  fresh : state.register .fresh=.natural 0
  prepared : HeapList state 0 (preparedInput P fee)
  cache : HeapList state 96 (encodeList encodeEndpoint P.endpointCache.toList)

def source (P : Parameters) (fee : ℚ) (j : ℕ) : MultiplierState :=
  P.cachedMultiplierSearch P.endpointCache fee j

/-- INTERNAL actual-body certificate, never an original-input hypothesis.
Every resource, source update and solver-entry bound concerns the SAME
fetched execution. Root constructs it from the literal original body. -/
def BodySpec (program : Program) (labels : RoutineLabels) (input : List Cell)
    (P : Parameters) (fee : ℚ) (origin : ℕ) (body : List Instruction)
    (budget : ℕ) (region : Finset ℕ) (bodyCost : ℕ) : Prop :=
  ∀ j : ℕ, j<P.bisectionBudget fee → ∀ before : State,
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
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace≤1

end PDCompute.CoreSearchLoop
