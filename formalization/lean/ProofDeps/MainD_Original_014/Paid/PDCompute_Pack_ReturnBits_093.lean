module
public import Paid.PDCompute_Pack_ReturnStraightBits_092
public import Paid.PDCompute_Pack_Return_043

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

theorem return_trace_safe (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base returnPC start cursor budget : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+222)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hreturn : values 1=.natural returnPC) (hstart : values outputStart=.natural start)
    (hcursor : values outputCursor=.natural cursor)
    (safe : SafeBits before budget) (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (counter : natBits (before.pc+10) ≤ budget) :
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
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have fetchReturn : FetchesCode program before.pc (returnStraightCode++[.jumpIndirect .old]) := by
    rw [pc,←returnCode_decompose]
    exact fetch_return program origin code
  have run:=returnStraight_execute input before base returnPC start cursor values header hbase hreturn hstart hcursor
  obtain ⟨straightTrace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input returnStraightCode
    returnStraight_straight before _ fetchReturn.append_left run (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state execute
      have countBound : count ≤ 10:=bound
      exact ⟨returnStraight_prefix_memory input before state base count execute,
        returnStraight_prefix_safe input before state base returnPC start cursor budget count values header hbase hreturn hstart hcursor
          safe addressBits counter countBound execute⟩)
  have memory : ∀ state∈straightTrace,HeaderMemory before state base:=fun state member=>(invariant state member).1
  have bits : ∀ state∈straightTrace,SafeBits state budget:=fun state member=>(invariant state member).2
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
  have preparedSafe : SafeBits prepared budget:=bits prepared (List.mem_of_getLast? hl)
  have returnBits : natBits returnPC ≤ budget:=by
    have represented:=preparedSafe.register .old
    have oldValue : prepared.register .old=.natural returnPC:=by simp [prepared,returnStraightResult]
    rw [oldValue] at represented
    change 1+natBits returnPC ≤ budget at represented
    omega
  have finalSafe : SafeBits (serializerReturnResult before returnPC start cursor) budget:=preparedSafe.withPC returnPC returnBits
  refine ⟨straightTrace++[_],?_,by simp,joined.1,by change time program straightTrace ≤ 165 at ht;omega,
    header,?_,?_,?_,?_,rfl,rfl,?_,?_⟩
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

  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact bits state earlier
    · have same : state=serializerReturnResult before returnPC start cursor:=by simpa only [List.mem_singleton] using last
      subst state
      exact finalSafe

end PDCompute.Pack
