module

public import Paid.RootD27Endpoint_ScalarTrace_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)

def returnPrefixCode : List Instruction :=
  loadSlot 1 .old++loadSlot 3 .index++
  [.constant .total (.natural 2),.natOp .multiply .index .index .total,
   .constant .total (.natural 3),.natOp .add .index .index .total]++loadSlot 0 .address

def returnPrefixResult (before : State) (base M : ℕ) : State :=
  let loaded:=loadSlotResult (loadSlotResult before base 1 .old) base 3 .index
  let doubled:=(({loaded with pc:=loaded.pc+2}).set .total (.natural 2)).set .index (.natural (M*2))
  let counted:=(({doubled with pc:=doubled.pc+2}).set .total (.natural 3)).set .index (.natural (M*2+3))
  loadSlotResult counted base 0 .address

theorem returnCode_split : returnCode=returnPrefixCode++[.jumpIndirect .old] := rfl

theorem returnPrefix_straight : StraightCode returnPrefixCode := by
  simp [StraightCode,returnPrefixCode,loadSlot,StraightInstruction]

theorem returnPrefix_execute (input : List Cell) (before : State) (base M : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hM : values 3=.natural M) :
    linearExecute input returnPrefixCode before=some (returnPrefixResult before base M) := by
  have rlive:=header.live 1 (by decide)
  have Mlive:=header.live 3 (by decide)
  have Elive : base∈before.live := by simpa using header.live 0 (by decide)
  have Mv:=(header.value 3 (by decide)).trans hM
  simp [returnPrefixCode,returnPrefixResult,loadSlot,loadSlotResult,linearExecute,
    Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,rlive,Mlive,Elive,Mv,Nat.add_assoc]

theorem returnPrefix_fields (before : State) (base M : ℕ) :
    (returnPrefixResult before base M).heap=before.heap ∧
    (returnPrefixResult before base M).live=before.live ∧
    (returnPrefixResult before base M).output=before.output ∧
    (returnPrefixResult before base M).register .fresh=before.register .fresh ∧
    (returnPrefixResult before base M).register .old=before.heap (base+1) ∧
    (returnPrefixResult before base M).register .address=before.heap base ∧
    (returnPrefixResult before base M).register .index=.natural (M*2+3) ∧
    (returnPrefixResult before base M).pc=before.pc+13 := by
  simp [returnPrefixResult,loadSlotResult,State.set,Nat.add_assoc]

theorem returnPrefix_memory (input : List Cell) (before after : State) (base M : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hM : values 3=.natural M)
    (count : ℕ) (hcount : count<13)
    (hexec : linearExecute input (returnPrefixCode.take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  have rlive:=header.live 1 (by decide)
  have Mlive:=header.live 3 (by decide)
  have Mv:=(header.value 3 (by decide)).trans hM
  interval_cases count <;>
    simp [returnPrefixCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,
      Cell.nat?,hbase,rlive,Mlive,Mv] at hexec <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

/-- Restore the original ABI and execute the actual indirect return.
No synthetic return transition or caller-supplied final state is used. -/
theorem return_actual (program : Program) (input : List Cell) (before : State)
    (base E M returnPC : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hE : values 0=.natural E) (hM : values 3=.natural M)
    (hret : values 1=.natural returnPC) (hfetch : FetchesCode program before.pc returnCode) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤225 ∧ after.pc=returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural E ∧ after.register .index=.natural (2*M+3) ∧
      ∀ state∈trace, state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
  let loaded:=returnPrefixResult before base M
  let after : State:={loaded with pc:=returnPC}
  have fields:=returnPrefix_fields before base M
  have ret : before.heap (base+1)=.natural returnPC := (header.value 1 (by decide)).trans hret
  have addr : before.heap base=.natural E := by simpa using (header.value 0 (by decide)).trans hE
  rw [returnCode_split] at hfetch
  obtain ⟨trace,hh,hl,hc,ht,prefixes⟩:=linearExecute_trace_time program input returnPrefixCode
    returnPrefix_straight before loaded hfetch.append_left
    (returnPrefix_execute input before base M values header hbase hM)
  have memory : ∀ state∈trace, state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
    intro state member
    have split:=List.dropLast_append_getLast? loaded (by rw [hl]; simp)
    rw [←split] at member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with proper|last
    · obtain ⟨count,bound,run⟩:=prefixes state proper
      exact returnPrefix_memory input before state base M values header hbase hM count bound run
    · subst state
      exact ⟨fields.1,fields.2.1,fields.2.2.1⟩
  have fetch : program[loaded.pc]?=some (.jumpIndirect .old) := by
    rw [fields.2.2.2.2.2.2.2]
    exact (hfetch 13 (by simp [returnPrefixCode,loadSlot])).trans (by rfl)
  have old : loaded.register .old=.natural returnPC := fields.2.2.2.2.1.trans ret
  have control : step program input loaded=some after := step_jumpIndirect_return program input loaded returnPC fetch old
  have joined:=chain_append_control program input trace loaded after hc hl control
  have nonempty : trace≠[] := by intro eq; simp only [eq,List.head?_nil,reduceCtorEq] at hh
  refine ⟨trace++[after],after,?_,by simp,joined.1,?_,rfl,fields.2.2.2.1.trans hbase,old,
    fields.2.2.2.2.2.1.trans addr,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil trace nonempty] using hh
  · have bound : time program trace≤210 := ht
    omega
  · change loaded.register .index=.natural (2*M+3)
    simpa only [Nat.mul_comm] using fields.2.2.2.2.2.2.1
  · intro state member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with prior|last
    · exact memory state prior
    · subst state
      exact ⟨fields.1,fields.2.1,fields.2.2.1⟩

end RootD27.Endpoint
