module

public import Paid.RootD27Core_HeaderCode_045
public import Paid.PDLower_CoreSearch_TargetMemory_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver
open PDLower.CoreSearch

/-- Only static tags/zero occur in code. Lambda and the original J are
copied from the thirteen actually prepared live input cells. -/
def searchInitializeCommands : List HeaderCommand :=
  [.constant 13 (.natural 1),.constant 14 (.rational 0),.copy 11 15,.copy 10 28]

def searchInitializeValues (values : ℕ→Cell) : ℕ→Cell :=
  Function.update (Function.update (Function.update (Function.update values 13 (.natural 1))
    14 (.rational 0)) 15 (values 11)) 28 (values 10)

theorem searchInitialize_valid : ∀ command∈searchInitializeCommands,command.Valid := by
  intro command member
  simp only [searchInitializeCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same|same|same|same <;> subst command <;> dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem searchInitialize_targets : ∀ command∈searchInitializeCommands,commandTarget command∈scalarRegion := by
  intro command member
  simp only [searchInitializeCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same|same|same|same <;> subst command <;> decide

theorem searchInitialize_length : (headerCode searchInitializeCommands).length=20:=rfl

theorem searchInitialize_eval (values : ℕ→Cell) :
    headerEval searchInitializeCommands values=some (searchInitializeValues values) := by
  simp [searchInitializeCommands,searchInitializeValues,headerEval,HeaderCommand.eval]

/-- Actual source initialization of the bracket tag/multipliers and J.
No scalar metadata is assumed initially. The original raw13 and all
retained-copy cells remain untouched throughout the same true trace. -/
theorem search_initialize_actual (P : Parameters) (fee : ℚ) (program : Program) (input : List Cell)
    (before : State) (values : ℕ→Cell) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0) (prepared : HeapList before 0 (preparedInput P fee))
    (fetched : FetchesCode program before.pc (headerCode searchInitializeCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤315 ∧
      Header after 0 (searchInitializeValues values) ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+20 ∧
      after.heap 13=.natural 1 ∧ after.heap 14=.rational 0 ∧ after.heap 15=.rational P.Lambda ∧
      after.heap 28=.natural (P.bisectionBudget fee) ∧ after.output=before.output ∧ after.live=before.live ∧
      peakCells trace≤workingCells before ∧
      (∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) := by
  have lambda:=PDLower.CalibrationCompute.HeapList.value prepared 11 (by change 11<13;decide)
  have count:=PDLower.CalibrationCompute.HeapList.value prepared 10 (by change 10<13;decide)
  change before.heap 11=.rational P.Lambda at lambda
  change before.heap 10=.natural (P.bisectionBudget fee) at count
  have lambdaValue : values 11=.rational P.Lambda:=(header.value 11 (by decide)).symm.trans lambda
  have countValue : values 10=.natural (P.bisectionBudget fee):=(header.value 10 (by decide)).symm.trans count
  obtain ⟨trace,after,head,last,chain,cost,_run,afterHeader,afterFresh,pc,output,memory⟩:=
    commands_trace_scalar searchInitializeCommands program input before values (searchInitializeValues values)
      searchInitialize_valid searchInitialize_targets header fresh (searchInitialize_eval values) fetched
  have afterMemory:=memory after (List.mem_of_getLast? last)
  have tag : after.heap 13=.natural 1 := by simpa [searchInitializeValues] using afterHeader.value 13 (by decide)
  have zero : after.heap 14=.rational 0 := by simpa [searchInitializeValues] using afterHeader.value 14 (by decide)
  have upper : after.heap 15=.rational P.Lambda := by simpa [searchInitializeValues,lambdaValue] using afterHeader.value 15 (by decide)
  have remaining : after.heap 28=.natural (P.bisectionBudget fee) := by simpa [searchInitializeValues,countValue] using afterHeader.value 28 (by decide)
  refine ⟨trace,after,head,last,chain,by simpa only [searchInitialize_length] using cost,afterHeader,afterFresh,
    by simpa only [searchInitialize_length] using pc,tag,zero,upper,remaining,output,afterMemory.2.2.1,?_,memory⟩
  apply PDLower.CalibrationCompute.peakCells_le_of_forall
  intro state member
  have fields:=memory state member
  have same : workingCells state=workingCells before:=by
    unfold workingCells
    rw [fields.2.2.1,fields.2.2.2]
  exact same.le

end RootD27.Core
