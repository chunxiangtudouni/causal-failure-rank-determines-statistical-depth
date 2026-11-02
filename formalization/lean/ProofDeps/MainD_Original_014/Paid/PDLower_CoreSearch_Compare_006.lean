module

public import Paid.PDLower_CoreSearch_TargetMemory_001
public import Paid.PDCompute_SolverRatCompare_097
public import Paid.PDLower_CalibrationCompute_ReadOnly_051

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute linearExecute_append loadSlotResult storeSlot storeSlotResult storeSlot_execute readOnly linearReadOnly_heap)

namespace PDLower.CoreSearch

/-- Reuse the frozen original seven-op comparison, then actually store
its Bool-as-Nat in40. The same genuine result remains in.flag for Root's
real denominator/stop/selector branches. -/
def comparisonStoredCode (comparison : Comparison) (left right : ℕ) : List Instruction :=
  rationalCompareCode comparison left right++storeSlot 40 .flag

def comparisonStoredResult (before : State) (left right : ℕ) (value : Bool) : State :=
  storeSlotResult (PDROC.D27Prepare.Program.comparisonResult before 0 left right value) 0 40 .flag

theorem comparisonStored_length (comparison : Comparison) (left right : ℕ) :
    (comparisonStoredCode comparison left right).length=10 := rfl

theorem comparisonStored_straight (comparison : Comparison) (left right : ℕ) :
    StraightCode (comparisonStoredCode comparison left right) := by
  intro instruction member
  rcases List.mem_append.mp member with first|last
  · exact rationalCompareCode_straight comparison left right instruction first
  · simp only [storeSlot,List.mem_cons,List.not_mem_nil,or_false] at last
    rcases last with same|same|same <;> subst instruction <;> trivial

theorem comparisonStored_fields (before : State) (left right : ℕ) (value : Bool) :
    (comparisonStoredResult before left right value).heap=Function.update before.heap 40 (.natural (if value then 1 else 0)) ∧
    (comparisonStoredResult before left right value).live=insert 40 before.live ∧
    (comparisonStoredResult before left right value).register .fresh=before.register .fresh ∧
    (comparisonStoredResult before left right value).register .flag=.natural (if value then 1 else 0) ∧
    (comparisonStoredResult before left right value).pc=before.pc+10 ∧
    (comparisonStoredResult before left right value).output=before.output := by
  obtain ⟨heap,live,fresh,flag,pc,output⟩ := PDROC.D27Prepare.Program.comparisonResult_fields before 0 left right value
  simp [comparisonStoredResult,storeSlotResult,heap,live,fresh,flag,pc,output,Nat.add_assoc]

theorem comparisonStored_execute (comparison : Comparison) (left right : ℕ) (x y : ℚ)
    (input : List Cell) (before : State) (values : ℕ→Cell) (header : Header before 0 values)
    (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : values left=.rational x) (rightValue : values right=.rational y)
    (fresh : before.register .fresh=.natural 0) :
    linearExecute input (comparisonStoredCode comparison left right) before=
      some (comparisonStoredResult before left right (comparison.rat x y)) := by
  let compared := PDROC.D27Prepare.Program.comparisonResult before 0 left right (comparison.rat x y)
  have compareRun : linearExecute input (rationalCompareCode comparison left right) before=some compared :=
    PDROC.D27Prepare.Program.ratCompareSlots_execute input before 0 left right x y comparison fresh
      (header.live left leftInside) (header.live right rightInside)
      ((header.value left leftInside).trans leftValue) ((header.value right rightInside).trans rightValue)
  have fields := PDROC.D27Prepare.Program.comparisonResult_fields before 0 left right (comparison.rat x y)
  rw [comparisonStoredCode,linearExecute_append,compareRun,Option.bind_some]
  exact storeSlot_execute input compared 0 40 .flag (fields.2.2.1.trans fresh) (by decide)

theorem comparisonStored_prefix_memory (comparison : Comparison) (left right : ℕ) (x y : ℚ)
    (input : List Cell) (before after : State) (values : ℕ→Cell) (header : Header before 0 values)
    (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : values left=.rational x) (rightValue : values right=.rational y)
    (fresh : before.register .fresh=.natural 0) (count : ℕ) (bounded : count≤10)
    (executed : linearExecute input ((comparisonStoredCode comparison left right).take count) before=some after) :
    MemoryFrame scalarRegion before after ∧ HeaderMemory before after 0 := by
  by_cases short : count<10
  · have readonlyPrefix : ((comparisonStoredCode comparison left right).take count).all readOnly=true := by
      interval_cases count <;> rfl
    have old := linearReadOnly_heap input _ before after readonlyPrefix executed
    exact ⟨⟨fun address _ => congrFun old.1 address,fun address _ => by rw [old.2.1]⟩,
      HeaderMemory.of_unchanged 0 old.1 old.2.1 old.2.2⟩
  · have exactCount : count=10 := by omega
    subst count
    have full : linearExecute input (comparisonStoredCode comparison left right) before=some after := executed
    rw [comparisonStored_execute comparison left right x y input before values header leftInside rightInside leftValue rightValue fresh] at full
    have same := Option.some.inj full
    subst after
    have fields := comparisonStored_fields before left right (comparison.rat x y)
    have broad : HeaderMemory before (comparisonStoredResult before left right (comparison.rat x y)) 0 :=
      HeaderMemory.write header 40 (by decide) _ fields.1 fields.2.1 fields.2.2.2.2.2
    refine ⟨⟨?_,fun address _ => by rw [broad.2.1]⟩,broad⟩
    intro address outside
    have different : address≠40 := by
      intro same
      apply outside
      rw [same]
      decide
    rw [fields.1]
    exact Function.update_of_ne different _ _

theorem comparisonStored_trace (comparison : Comparison) (left right : ℕ) (x y : ℚ)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : values left=.rational x) (rightValue : values right=.rational y)
    (fresh : before.register .fresh=.natural 0)
    (fetched : FetchesCode program before.pc (comparisonStoredCode comparison left right)) :
    ∃ trace : List State,trace.head?=some before ∧
      trace.getLast?=some (comparisonStoredResult before left right (comparison.rat x y)) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤165 ∧
      Header (comparisonStoredResult before left right (comparison.rat x y)) 0
        (Function.update values 40 (.natural (if comparison.rat x y then 1 else 0))) ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  let after := comparisonStoredResult before left right (comparison.rat x y)
  have run := comparisonStored_execute comparison left right x y input before values header leftInside rightInside leftValue rightValue fresh
  obtain ⟨trace,head,last,chain,cost,prefixes⟩ := linearExecute_trace_time program input
    (comparisonStoredCode comparison left right) (comparisonStored_straight comparison left right) before after fetched run
  have fields := comparisonStored_fields before left right (comparison.rat x y)
  have afterHeader : Header after 0 (Function.update values 40 (.natural (if comparison.rat x y then 1 else 0))) :=
    header.update 40 _ fields.1 (by rw [fields.2.1];exact Finset.subset_insert _ _)
  refine ⟨trace,head,last,chain,by simpa only [comparisonStored_length] using cost,afterHeader,?_⟩
  intro state member
  have split := List.dropLast_append_getLast? after (by rw [last];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|finalState
  · obtain ⟨count,bound,execute⟩ := prefixes state proper
    exact comparisonStored_prefix_memory comparison left right x y input before state values header leftInside rightInside leftValue rightValue fresh count
      (by simpa only [comparisonStored_length] using bound.le) execute
  · have same := List.mem_singleton.mp finalState
    subst state
    exact comparisonStored_prefix_memory comparison left right x y input before after values header leftInside rightInside leftValue rightValue fresh 10
      (le_refl _) run

end PDLower.CoreSearch
