module
public import Paid.PDCompute_Pack_Fragments_018
public import Paid.PDCompute_Pack_Fetch_005
public import Paid.PDCompute_Pack_ArithmeticMemory_009
public import Paid.PDCompute_SolverSmallTraceMemory_061
public import Paid.PDCompute_SolverMemoryJoin_062

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (loadSlot linearExecute linearReadOnly_heap readOnly)

def returnStraightCode : List Instruction :=
  loadSlot 1 .old++loadSlot outputCursor .index++loadSlot outputStart .address++[.natOp .subtract .index .index .address]
def returnStraightResult (before : State) (returnPC start cursor : ℕ) : State :=
  {before with register:=Function.update (Function.update (Function.update before.register .old (.natural returnPC))
    .address (.natural start)) .index (.natural (cursor-start)),pc:=before.pc+10}
def serializerReturnResult (before : State) (returnPC start cursor : ℕ) : State :=
  {returnStraightResult before returnPC start cursor with pc:=returnPC}

theorem returnCode_decompose : returnCode=returnStraightCode++[.jumpIndirect .old] := by
  simp only [returnCode,returnStraightCode,List.append_assoc,List.singleton_append]

theorem returnStraight_execute (input : List Cell) (before : State) (base returnPC start cursor : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hreturn : values 1=.natural returnPC) (hstart : values outputStart=.natural start)
    (hcursor : values outputCursor=.natural cursor) :
    linearExecute input returnStraightCode before=some (returnStraightResult before returnPC start cursor) := by
  have live1:=header.live 1 (by decide)
  have live43:=header.live outputCursor (by decide)
  have live44:=header.live outputStart (by decide)
  have value1:=(header.value 1 (by decide)).trans hreturn
  have value43:=(header.value outputCursor (by decide)).trans hcursor
  have value44:=(header.value outputStart (by decide)).trans hstart
  simp [returnStraightCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    hbase,live1,live43,live44,value1,value43,value44,returnStraightResult,Nat.add_assoc]
  funext register
  cases register <;> simp

theorem returnStraight_straight : StraightCode returnStraightCode := by
  intro instruction member
  simp only [returnStraightCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with h|h|h|h|h|h|h|h|h|h <;> subst instruction <;> trivial

theorem returnStraight_prefix_memory (input : List Cell) (before after : State) (base count : ℕ)
    (execute : linearExecute input (returnStraightCode.take count) before=some after) : HeaderMemory before after base := by
  have whole : returnStraightCode.all readOnly=true:=rfl
  have safe : (returnStraightCode.take count).all readOnly=true := by
    apply List.all_eq_true.mpr
    intro instruction member
    exact (List.all_eq_true.mp whole) instruction (List.mem_of_mem_take member)
  have memory:=linearReadOnly_heap input (returnStraightCode.take count) before after safe execute
  exact HeaderMemory.of_unchanged base memory.1 memory.2.1 memory.2.2

/-- The actual return loads the saved continuation before the final
address, computes the real serialized length, then jumps indirectly.old. -/
theorem return_trace (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base returnPC start cursor : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+222)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hreturn : values 1=.natural returnPC) (hstart : values outputStart=.natural start)
    (hcursor : values outputCursor=.natural cursor) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (serializerReturnResult before returnPC start cursor) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 180 ∧
      Header (serializerReturnResult before returnPC start cursor) base values ∧
      (serializerReturnResult before returnPC start cursor).register .fresh=.natural base ∧
      (serializerReturnResult before returnPC start cursor).register .old=.natural returnPC ∧
      (serializerReturnResult before returnPC start cursor).register .address=.natural start ∧
      (serializerReturnResult before returnPC start cursor).register .index=.natural (cursor-start) ∧
      (serializerReturnResult before returnPC start cursor).pc=returnPC ∧
      (serializerReturnResult before returnPC start cursor).output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  have fetchReturn : FetchesCode program before.pc (returnStraightCode++[.jumpIndirect .old]) := by
    rw [pc,←returnCode_decompose]
    exact fetch_return program origin code
  have run:=returnStraight_execute input before base returnPC start cursor values header hbase hreturn hstart hcursor
  obtain ⟨straightTrace,hh,hl,hchain,ht,memory⟩:=linearExecute_trace_memory program input returnStraightCode
    returnStraight_straight before _ base fetchReturn.append_left run
    (fun count _bound state execute=>returnStraight_prefix_memory input before state base count execute)
  let prepared:=returnStraightResult before returnPC start cursor
  have preparedPC : prepared.pc=origin+232 := by change before.pc+10=origin+232;omega
  have returnFetch : program[prepared.pc]?=some (.jumpIndirect .old) := by
    rw [preparedPC]
    exact indirect_return_fetch program origin code
  have jump : step program input prepared=some (serializerReturnResult before returnPC start cursor) := by
    simp only [step,returnFetch]
    simp [Instruction.execute,prepared,returnStraightResult,serializerReturnResult,Cell.nat?]
  have joined:=chain_append_control program input straightTrace prepared _ hchain hl jump
  have nonempty : straightTrace≠[] := by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at hh
  have lastMemory:=HeaderMemory.trace_last memory hl
  refine ⟨straightTrace++[_],?_,by simp,joined.1,by change time program straightTrace ≤ 165 at ht;omega,
    header,?_,?_,?_,?_,rfl,rfl,?_⟩
  · simpa only [List.head?_append_of_ne_nil straightTrace nonempty] using hh
  · simp [serializerReturnResult,returnStraightResult,hbase]
  · simp [serializerReturnResult,returnStraightResult]
  · simp [serializerReturnResult,returnStraightResult]
  · simp [serializerReturnResult,returnStraightResult]
  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact memory state earlier
    · have same : state=serializerReturnResult before returnPC start cursor := by simpa only [List.mem_singleton] using last
      subst state
      exact lastMemory

end PDCompute.Pack
