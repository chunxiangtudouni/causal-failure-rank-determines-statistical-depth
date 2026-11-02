module

public import Paid.RootD27Endpoint_Code_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot loadSlotResult storeSlotResult)

def castRowResult (before : State) (base m : ℕ) : State :=
  let loaded:=loadSlotResult before base 8 .total
  let casted:=({loaded with pc:=loaded.pc+1}).set .total (.rational (m:ℚ))
  storeSlotResult casted base 18 .total

theorem castRow_straight : StraightCode castRowCode := by
  intro instruction member
  simp only [castRowCode,loadSlot,storeSlot,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at member
  rcases member with ((h|h|h)|h)|(h|h|h) <;> subst instruction <;> trivial

theorem castRow_execute (input : List Cell) (before : State) (base m : ℕ)
    (hbase : before.register .fresh=.natural base)
    (hlive : base+8∈before.live) (hrow : before.heap (base+8)=.natural m) :
    linearExecute input castRowCode before=some (castRowResult before base m) := by
  simp [castRowCode,loadSlot,storeSlot,castRowResult,loadSlotResult,storeSlotResult,
    linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,hlive,hrow,
    Nat.add_assoc]

theorem castRow_heap (before : State) (base m : ℕ) :
    (castRowResult before base m).heap=
      Function.update before.heap (base+18) (.rational (m:ℚ)) := by
  simp [castRowResult,storeSlotResult,loadSlotResult,State.set]

theorem castRow_live (before : State) (base m : ℕ) :
    (castRowResult before base m).live=insert (base+18) before.live := rfl

theorem castRow_fresh (before : State) (base m : ℕ) :
    (castRowResult before base m).register .fresh=before.register .fresh := by
  simp [castRowResult,storeSlotResult,loadSlotResult,State.set]

theorem castRow_pc (before : State) (base m : ℕ) :
    (castRowResult before base m).pc=before.pc+7 := by
  simp [castRowResult,storeSlotResult,loadSlotResult,State.set,Nat.add_assoc]

theorem castRow_output (before : State) (base m : ℕ) :
    (castRowResult before base m).output=before.output := rfl

theorem castRow_header (before : State) (base m : ℕ) (values : ℕ → Cell)
    (header : Header before base values) :
    Header (castRowResult before base m) base (Function.update values 18 (.rational (m:ℚ))) := by
  apply Header.update header 18 (.rational (m:ℚ)) (castRow_heap before base m)
  rw [castRow_live]
  exact Finset.subset_insert _ _

/-- Genuine original natToRat instruction, following the live natural
counter read. The scalar endpoint phase receives its cast from this run,
not as an unproved caller-provided rational datum. -/
theorem castRow_actual (program : Program) (input : List Cell) (before : State)
    (base m : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hrow : values 8=.natural m)
    (hfetch : FetchesCode program before.pc castRowCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (castRowResult before base m) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤120 ∧
      Header (castRowResult before base m) base (Function.update values 18 (.rational (m:ℚ))) ∧
      (castRowResult before base m).register .fresh=.natural base ∧
      (castRowResult before base m).pc=before.pc+7 := by
  have hvalue:before.heap (base+8)=.natural m := (header.value 8 (by decide)).trans hrow
  obtain ⟨trace,hh,hl,hc,ht,_⟩ :=
    linearExecute_trace_time program input castRowCode castRow_straight before
      (castRowResult before base m) hfetch
      (castRow_execute input before base m hbase (header.live 8 (by decide)) hvalue)
  exact ⟨trace,hh,hl,hc,ht,castRow_header before base m values header,
    (castRow_fresh before base m).trans hbase,castRow_pc before base m⟩

end RootD27.Endpoint
