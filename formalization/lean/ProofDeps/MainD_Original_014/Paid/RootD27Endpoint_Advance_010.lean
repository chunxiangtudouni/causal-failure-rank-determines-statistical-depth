module

public import Paid.RootD27Endpoint_ScalarTrace_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot loadSlotResult storeSlotResult)

def incrementRowCode : List Instruction :=
  loadSlot 8 .total++[.constant .value (.natural 1),.natOp .add .total .total .value]++storeSlot 8 .total

def incrementRowResult (before : State) (base m : ℕ) : State :=
  let loaded:=loadSlotResult before base 8 .total
  let counted:=(({loaded with pc:=loaded.pc+2}).set .value (.natural 1)).set .total (.natural (m+1))
  storeSlotResult counted base 8 .total

theorem advanceCode_split : advanceCode=headerCode [.rational .multiply 7 6 7]++incrementRowCode := rfl

theorem incrementRow_straight : StraightCode incrementRowCode := by
  simp [StraightCode,incrementRowCode,loadSlot,storeSlot,StraightInstruction]

theorem incrementRow_execute (input : List Cell) (before : State) (base m : ℕ)
    (hbase : before.register .fresh=.natural base)
    (hlive : base+8∈before.live) (hrow : before.heap (base+8)=.natural m) :
    linearExecute input incrementRowCode before=some (incrementRowResult before base m) := by
  simp [incrementRowCode,incrementRowResult,loadSlot,storeSlot,loadSlotResult,storeSlotResult,
    linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,hlive,hrow,Nat.add_assoc]

theorem incrementRow_heap (before : State) (base m : ℕ) :
    (incrementRowResult before base m).heap=Function.update before.heap (base+8) (.natural (m+1)) := by
  simp [incrementRowResult,loadSlotResult,storeSlotResult,State.set]

theorem incrementRow_live (before : State) (base m : ℕ) :
    (incrementRowResult before base m).live=insert (base+8) before.live := rfl

theorem incrementRow_fresh (before : State) (base m : ℕ) :
    (incrementRowResult before base m).register .fresh=before.register .fresh := by
  simp [incrementRowResult,loadSlotResult,storeSlotResult,State.set]

theorem incrementRow_pc (before : State) (base m : ℕ) :
    (incrementRowResult before base m).pc=before.pc+8 := by
  simp [incrementRowResult,loadSlotResult,storeSlotResult,State.set,Nat.add_assoc]

theorem incrementRow_output (before : State) (base m : ℕ) :
    (incrementRowResult before base m).output=before.output := rfl

theorem incrementRow_header (before : State) (base m : ℕ) (values : ℕ → Cell)
    (header : Header before base values) :
    Header (incrementRowResult before base m) base (Function.update values 8 (.natural (m+1))) := by
  apply Header.update header 8 (.natural (m+1)) (incrementRow_heap before base m)
  rw [incrementRow_live]
  exact Finset.subset_insert _ _

theorem incrementRow_memory (before : State) (base m : ℕ) (values : ℕ → Cell)
    (header : Header before base values) : HeaderMemory before (incrementRowResult before base m) base :=
  HeaderMemory.write header 8 (by decide) (.natural (m+1))
    (incrementRow_heap before base m) (incrementRow_live before base m) (incrementRow_output before base m)

theorem incrementRow_prefix (input : List Cell) (before after : State) (base m : ℕ)
    (hbase : before.register .fresh=.natural base) (hlive : base+8∈before.live)
    (hrow : before.heap (base+8)=.natural m) (count : ℕ) (hcount : count<8)
    (hexec : linearExecute input (incrementRowCode.take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  interval_cases count <;>
    simp [incrementRowCode,loadSlot,storeSlot,linearExecute,Instruction.execute,
      State.set,NatOp.eval,Cell.nat?,hbase,hlive,hrow] at hexec <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

theorem incrementRow_actual (program : Program) (input : List Cell) (before : State)
    (base m : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hrow : values 8=.natural m)
    (hfetch : FetchesCode program before.pc incrementRowCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (incrementRowResult before base m) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤135 ∧
      Header (incrementRowResult before base m) base (Function.update values 8 (.natural (m+1))) ∧
      ∀ state∈trace, HeaderMemory before state base := by
  have hv : before.heap (base+8)=.natural m := (header.value 8 (by decide)).trans hrow
  obtain ⟨trace,hh,hl,hc,ht,prefixes⟩ :=
    linearExecute_trace_time program input incrementRowCode incrementRow_straight before
      (incrementRowResult before base m) hfetch
      (incrementRow_execute input before base m hbase (header.live 8 (by decide)) hv)
  refine ⟨trace,hh,hl,hc,ht,incrementRow_header before base m values header,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (incrementRowResult before base m) (by rw [hl]; simp)
  rw [←split] at member
  simp only [List.mem_append,List.mem_singleton] at member
  rcases member with proper|last
  · obtain ⟨count,bound,run⟩:=prefixes state proper
    have frame:=incrementRow_prefix input before state base m hbase (header.live 8 (by decide)) hv count bound run
    exact HeaderMemory.of_unchanged base frame.1 frame.2.1 frame.2.2
  · subst state
    exact incrementRow_memory before base m values header

theorem advance_actual (P : Parameters) (m : ℕ) (program : Program) (input : List Cell)
    (before : State) (base : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hpower : values 7=.rational (powerRecurrence P.certificate.odds m))
    (hodds : values 6=.rational P.certificate.odds) (hrow : values 8=.natural m)
    (hfetch : FetchesCode program before.pc advanceCode) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤465 ∧ after.pc=before.pc+18 ∧ after.register .fresh=.natural base ∧
      Header after base (Function.update
        (Function.update values 7 (.rational (powerRecurrence P.certificate.odds (m+1)))) 8 (.natural (m+1))) ∧
      ∀ state∈trace, HeaderMemory before state base := by
  let next:=Function.update values 7 (.rational (powerRecurrence P.certificate.odds (m+1)))
  have valid : ∀ command∈[HeaderCommand.rational .multiply 7 6 7], command.Valid := by
    intro command member
    simp only [List.mem_singleton] at member
    subst command
    norm_num [HeaderCommand.Valid,headerWords]
  have eval : headerEval [.rational .multiply 7 6 7] values=some next := by
    simp [headerEval,HeaderCommand.eval,Cell.rat?,RatOp.eval,hpower,hodds,next,powerRecurrence]
  rw [advanceCode_split] at hfetch
  obtain ⟨first,middle,hfh,hfl,hfc,hft,mh,mb,mp,_,_,fm⟩ :=
    headerCode_trace_memory [.rational .multiply 7 6 7] program input before base 0 0 values next
      valid header hbase eval hfetch.append_left
  have rowValue : next 8=.natural m := by simp [next,hrow]
  have fetched : FetchesCode program middle.pc incrementRowCode := by
    rw [mp]
    exact hfetch.append_right
  obtain ⟨later,hlh,hll,hlc,hlt,ah,lm⟩ :=
    incrementRow_actual program input middle base m next mh mb rowValue fetched
  have joined:=joinTrace_spec program input first later before middle (incrementRowResult middle base m)
    330 135 hfh hfl hlh hll hfc hlc hft hlt
  have middleMember : middle∈first := by
    have split:=List.dropLast_append_getLast? middle (by rw [hfl]; simp)
    rw [←split]
    simp
  refine ⟨joinTrace first later,incrementRowResult middle base m,
    joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,?_,?_,ah,?_⟩
  · rw [incrementRow_pc,mp]
    rfl
  · exact (incrementRow_fresh middle base m).trans mb
  · intro state member
    simp only [joinTrace,List.mem_append] at member
    rcases member with left|right
    · exact fm state (List.mem_of_mem_dropLast left)
    · exact (fm middle middleMember).trans (lm state right)

end RootD27.Endpoint
