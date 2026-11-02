module

public import Paid.PDCompute_SolverScanCallerMemory_070

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot)
open PDMenu.ComputeFrame

/-- Read the actual selected level and original cache pointer, multiply
and add using the original typed ISA, then save the selected cache-pair
address. No host indexing or level-dependent program is introduced. -/
def selectedPointerCode : List Instruction :=
  loadSlot 23 .index++
    [.constant .flag (.natural 2),.natOp .multiply .index .flag .index,
     .constant .flag (.natural 1),.natOp .add .index .flag .index]++
    loadSlot 0 .value++[.natOp .add .index .value .index]++storeSlot 39 .index

def selectedPointerResult (before : State) (base source level : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update
      (Function.update before.register .address (.natural (base+39))) .index (.natural (source+(1+2*level))))
      .flag (.natural 1)) .value (.natural source)
    heap:=Function.update before.heap (base+39) (.natural (source+(1+2*level)))
    live:=insert (base+39) before.live
    pc:=before.pc+14}

theorem selectedPointerCode_length : selectedPointerCode.length=14 := rfl

theorem selectedPointerResult_header (before : State) (base source level : ℕ) (values : ℕ → Cell)
    (header : Header before base values) :
    Header (selectedPointerResult before base source level) base
      (Function.update values 39 (.natural (source+(1+2*level)))) := by
  apply Header.update header 39 (.natural (source+(1+2*level))) rfl
  exact Finset.subset_insert _ _

theorem selectedPointerResult_frame (before : State) (base source level n k : ℕ) :
    Frame before (selectedPointerResult before base source level) base n k :=
  slotWrite_frame before _ base 39 n k (.natural (source+(1+2*level))) (by decide) rfl rfl

theorem selectedPointerCode_straight : StraightCode selectedPointerCode := by
  intro instruction member
  simp only [selectedPointerCode,loadSlot,storeSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst instruction <;> trivial

theorem selectedPointerCode_execute (input : List Cell) (before : State) (base source level : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hsource : values 0=.natural source) (hlevel : values 23=.natural level) :
    linearExecute input selectedPointerCode before=some (selectedPointerResult before base source level) := by
  have liveSource : base ∈ before.live := by simpa only [Nat.add_zero] using header.live 0 (by decide)
  have liveLevel:=header.live 23 (by decide)
  have sourceCell : before.heap base=.natural source := by
    simpa only [Nat.add_zero] using (header.value 0 (by decide)).trans hsource
  have levelCell:=(header.value 23 (by decide)).trans hlevel
  simp [selectedPointerCode,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    hbase,liveSource,liveLevel,sourceCell,levelCell,selectedPointerResult,Nat.add_assoc]
  funext register
  cases register <;> simp

theorem selectedPointerCode_prefix_memory (input : List Cell) (before after : State) (base source level : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hsource : values 0=.natural source) (hlevel : values 23=.natural level)
    (count : ℕ) (bound : count ≤ 14)
    (execute : linearExecute input (selectedPointerCode.take count) before=some after) :
    HeaderMemory before after base := by
  have liveSource : base ∈ before.live := by simpa only [Nat.add_zero] using header.live 0 (by decide)
  have liveLevel:=header.live 23 (by decide)
  have sourceCell : before.heap base=.natural source := by
    simpa only [Nat.add_zero] using (header.value 0 (by decide)).trans hsource
  have levelCell:=(header.value 23 (by decide)).trans hlevel
  interval_cases count <;>
    simp [selectedPointerCode,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
      hbase,liveSource,liveLevel,sourceCell,levelCell] at execute <;> subst after
  all_goals first
    | exact HeaderMemory.of_unchanged base rfl rfl rfl
    | exact HeaderMemory.write header 39 (by decide) (.natural (source+(1+2*level))) rfl rfl rfl

theorem selectedPointer_trace_memory (program : Program) (input : List Cell) (before : State)
    (base source level : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hsource : values 0=.natural source) (hlevel : values 23=.natural level)
    (fetched : FetchesCode program before.pc selectedPointerCode) :
    ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some (selectedPointerResult before base source level) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 225 ∧ ∀ state ∈ trace, HeaderMemory before state base :=
  linearExecute_trace_memory program input selectedPointerCode selectedPointerCode_straight before
    (selectedPointerResult before base source level) base fetched
    (selectedPointerCode_execute input before base source level values header hbase hsource hlevel)
    (fun count bound state execute => selectedPointerCode_prefix_memory input before state base source level values header hbase hsource hlevel
      count bound execute)

end PDCompute.Solver
