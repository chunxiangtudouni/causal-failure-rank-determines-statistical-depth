module

public import Paid.RootD27Endpoint_ScalarTrace_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)

def rowCompareCode : List Instruction :=
  loadSlot 8 .index++loadSlot 3 .total++[.natCompare .lessEqual .flag .index .total]

def rowCompareResult (before : State) (base m M : ℕ) : State :=
  let loaded:=loadSlotResult (loadSlotResult before base 8 .index) base 3 .total
  ({loaded with pc:=loaded.pc+1}).set .flag (.natural (if m≤M then 1 else 0))

theorem rowTest_split (bodyPC returnPC : ℕ) :
    rowTestCode bodyPC returnPC=rowCompareCode++[.branchZero .flag returnPC bodyPC] := rfl

theorem rowCompare_straight : StraightCode rowCompareCode := by
  simp [StraightCode,rowCompareCode,loadSlot,StraightInstruction]

theorem rowCompare_execute (input : List Cell) (before : State) (base m M : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hm : values 8=.natural m) (hM : values 3=.natural M) :
    linearExecute input rowCompareCode before=some (rowCompareResult before base m M) := by
  have mlive:=header.live 8 (by decide)
  have Mlive:=header.live 3 (by decide)
  have mv:=(header.value 8 (by decide)).trans hm
  have Mv:=(header.value 3 (by decide)).trans hM
  simp [rowCompareCode,rowCompareResult,loadSlot,loadSlotResult,linearExecute,
    Instruction.execute,State.set,NatOp.eval,Cell.nat?,Comparison.nat,hbase,mlive,Mlive,mv,Mv]

theorem rowCompare_fields (before : State) (base m M : ℕ) :
    (rowCompareResult before base m M).heap=before.heap ∧
    (rowCompareResult before base m M).live=before.live ∧
    (rowCompareResult before base m M).output=before.output ∧
    (rowCompareResult before base m M).register .fresh=before.register .fresh ∧
    (rowCompareResult before base m M).register .flag=.natural (if m≤M then 1 else 0) ∧
    (rowCompareResult before base m M).pc=before.pc+7 := by
  simp [rowCompareResult,loadSlotResult,State.set]

theorem rowCompare_prefix (input : List Cell) (before after : State) (base m M : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hm : values 8=.natural m) (hM : values 3=.natural M)
    (count : ℕ) (hcount : count<7)
    (hexec : linearExecute input (rowCompareCode.take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  have mlive:=header.live 8 (by decide)
  have Mlive:=header.live 3 (by decide)
  have mv:=(header.value 8 (by decide)).trans hm
  have Mv:=(header.value 3 (by decide)).trans hM
  interval_cases count <;>
    simp [rowCompareCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,
      Cell.nat?,hbase,mlive,Mlive,mv,Mv] at hexec <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

/-- Both outcomes are real fetched steps. Every prefix preserves exact
heap, live cells and output, including the old caller workspace. -/
theorem rowTest_actual (program : Program) (input : List Cell) (before : State)
    (base m M bodyPC returnPC : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hm : values 8=.natural m) (hM : values 3=.natural M)
    (hfetch : FetchesCode program before.pc (rowTestCode bodyPC returnPC)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤135 ∧ after.pc=(if m≤M then bodyPC else returnPC) ∧
      after.register .fresh=.natural base ∧ Header after base values ∧
      ∀ state∈trace, state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
  let compared:=rowCompareResult before base m M
  let after : State:={compared with pc:=if m≤M then bodyPC else returnPC}
  have fields:=rowCompare_fields before base m M
  rw [rowTest_split] at hfetch
  obtain ⟨trace,hh,hl,hc,ht,prefixes⟩:=linearExecute_trace_time program input rowCompareCode
    rowCompare_straight before compared hfetch.append_left
    (rowCompare_execute input before base m M values header hbase hm hM)
  have memory : ∀ state∈trace, state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
    intro state member
    have split:=List.dropLast_append_getLast? compared (by rw [hl]; simp)
    rw [←split] at member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with proper|last
    · obtain ⟨count,bound,run⟩:=prefixes state proper
      exact rowCompare_prefix input before state base m M values header hbase hm hM count bound run
    · subst state
      exact ⟨fields.1,fields.2.1,fields.2.2.1⟩
  have fetch : program[compared.pc]?=some (.branchZero .flag returnPC bodyPC) := by
    rw [fields.2.2.2.2.2]
    exact (hfetch 7 (by simp [rowCompareCode,loadSlot])).trans (by rfl)
  have control : step program input compared=some after := by
    unfold step
    rw [fetch]
    have flag : compared.register .flag=.natural (if m≤M then 1 else 0) := fields.2.2.2.2.1
    by_cases inside : m≤M <;> simp [Instruction.execute,flag,Cell.nat?,inside,after]
  have joined:=chain_append_control program input trace compared after hc hl control
  have nonempty : trace≠[] := by intro eq; simp only [eq,List.head?_nil,reduceCtorEq] at hh
  refine ⟨trace++[after],after,?_,by simp,joined.1,?_,rfl,fields.2.2.2.1.trans hbase,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil trace nonempty] using hh
  · have bound : time program trace≤120 := ht
    omega
  · apply header.frame
    · intro slot inside
      exact congrFun fields.1 (base+slot)
    · intro address member
      change address∈compared.live
      rw [fields.2.1]
      exact member
  · intro state member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with prior|last
    · exact memory state prior
    · subst state
      exact ⟨fields.1,fields.2.1,fields.2.2.1⟩

end RootD27.Endpoint
