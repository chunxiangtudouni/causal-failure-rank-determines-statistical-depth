module
public import Paid.PDCompute_Pack_ArithmeticMemory_009
public import Paid.PDCompute_SolverSmallTraceMemory_061

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute readOnly linearReadOnly_heap)

def tagDifferenceCode : List Instruction :=
  [.constant .flag (.natural 2),.natOp .subtract .value .flag .value]

def tagDifferenceResult (before : State) (tag : ℕ) : State :=
  {before with register:=Function.update (Function.update before.register .flag (.natural 2)) .value (.natural (2-tag)),pc:=before.pc+2}

theorem tagDifference_execute (input : List Cell) (before : State) (tag : ℕ)
    (value : before.register .value=.natural tag) :
    linearExecute input tagDifferenceCode before=some (tagDifferenceResult before tag) := by
  simp [tagDifferenceCode,tagDifferenceResult,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,value,Nat.add_assoc]

theorem tagDifference_prefix_memory (input : List Cell) (before after : State) (base count : ℕ)
    (execute : linearExecute input (tagDifferenceCode.take count) before=some after) : HeaderMemory before after base := by
  have whole : tagDifferenceCode.all readOnly=true := rfl
  have safe : (tagDifferenceCode.take count).all readOnly=true := by
    apply List.all_eq_true.mpr
    intro instruction member
    exact (List.all_eq_true.mp whole) instruction (List.mem_of_mem_take member)
  have unchanged:=linearReadOnly_heap input (tagDifferenceCode.take count) before after safe execute
  exact HeaderMemory.of_unchanged base unchanged.1 unchanged.2.1 unchanged.2.2

theorem tagDifference_fields (before : State) (tag : ℕ) :
    (tagDifferenceResult before tag).register .fresh=before.register .fresh ∧
    (tagDifferenceResult before tag).register .old=before.register .old ∧
    (tagDifferenceResult before tag).register .value=.natural (2-tag) ∧
    (tagDifferenceResult before tag).pc=before.pc+2 ∧
    (tagDifferenceResult before tag).output=before.output := by simp [tagDifferenceResult]

theorem tagDifference_trace (program : Program) (input : List Cell) (before : State) (base tag : ℕ)
    (value : before.register .value=.natural tag) (fetched : FetchesCode program before.pc tagDifferenceCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (tagDifferenceResult before tag) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤45 ∧
      ∀ state∈trace,HeaderMemory before state base := by
  have straight : StraightCode tagDifferenceCode := by
    intro instruction member
    simp only [tagDifferenceCode,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h <;> subst instruction <;> trivial
  exact linearExecute_trace_memory program input tagDifferenceCode straight before _ base fetched
    (tagDifference_execute input before tag value)
    (fun count _bound state execute=>tagDifference_prefix_memory input before state base count execute)

end PDCompute.Pack
