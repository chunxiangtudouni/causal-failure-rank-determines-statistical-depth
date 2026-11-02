module

public import Paid.RootD27Endpoint_Code_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)

def pairLoaded (before : State) (base : ℕ) : State :=
  loadSlotResult (loadSlotResult (loadSlotResult (loadSlotResult before base 9 .flag)
    base 11 .old) base 8 .index) base 0 .total

def pairStoreResult (before : State) (base E m : ℕ) (error charge : ℚ) : State :=
  let loaded:=pairLoaded before base
  let two:=({loaded with pc:=before.pc+20}).set .value (.natural 2)
  let doubled:=two.set .index (.natural (m*2))
  let one:=doubled.set .value (.natural 1)
  let shifted:=one.set .index (.natural (m*2+1))
  let pointed:=shifted.set .address (.natural (E+(m*2+1)))
  {pointed with
    register:=Function.update pointed.register .address (.natural (E+(m*2+1)+1))
    heap:=Function.update (Function.update before.heap (E+(m*2+1)) (.rational error))
      (E+(m*2+1)+1) (.rational charge)
    live:=insert (E+(m*2+1)+1) (insert (E+(m*2+1)) before.live)}

theorem pairStore_straight : StraightCode pairStoreCode := by
  simp [StraightCode,pairStoreCode,loadSlot,StraightInstruction]

theorem pairStore_execute (input : List Cell) (before : State) (base E m : ℕ)
    (error charge : ℚ) (hbase : before.register .fresh=.natural base)
    (hzero : base∈before.live) (height : base+8∈before.live)
    (hnine : base+9∈before.live) (heleven : base+11∈before.live)
    (hE : before.heap base=.natural E) (hm : before.heap (base+8)=.natural m)
    (he : before.heap (base+9)=.rational error) (hc : before.heap (base+11)=.rational charge) :
    linearExecute input pairStoreCode before=some (pairStoreResult before base E m error charge) := by
  simp [pairStoreCode,pairStoreResult,pairLoaded,loadSlot,loadSlotResult,linearExecute,
    Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,hzero,height,hnine,heleven,
    hE,hm,he,hc,Nat.add_assoc]

theorem pairStore_heap (before : State) (base E m : ℕ) (error charge : ℚ) :
    (pairStoreResult before base E m error charge).heap=
      Function.update (Function.update before.heap (E+(m*2+1)) (.rational error))
        (E+(m*2+1)+1) (.rational charge) := rfl

theorem pairStore_live (before : State) (base E m : ℕ) (error charge : ℚ) :
    (pairStoreResult before base E m error charge).live=
      insert (E+(m*2+1)+1) (insert (E+(m*2+1)) before.live) := rfl

theorem pairStore_pc (before : State) (base E m : ℕ) (error charge : ℚ) :
    (pairStoreResult before base E m error charge).pc=before.pc+20 := rfl

theorem pairStore_output (before : State) (base E m : ℕ) (error charge : ℚ) :
    (pairStoreResult before base E m error charge).output=before.output := rfl

theorem pairStore_fresh (before : State) (base E m : ℕ) (error charge : ℚ) :
    (pairStoreResult before base E m error charge).register .fresh=before.register .fresh := by
  simp [pairStoreResult,pairLoaded,loadSlotResult,State.set]

theorem pairStore_header (before : State) (base E m : ℕ) (error charge : ℚ)
    (values : ℕ → Cell) (header : Header before base values) (separated : base+48≤E) :
    Header (pairStoreResult before base E m error charge) base values := by
  apply Header.frame header
  · intro slot inside
    have hs : slot<48 := inside
    rw [pairStore_heap,Function.update_of_ne (by omega : base+slot≠E+(m*2+1)+1),
      Function.update_of_ne (by omega : base+slot≠E+(m*2+1))]
  · intro address member
    rw [pairStore_live]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem member)

theorem pairStore_cells (before : State) (base E m : ℕ) (error charge : ℚ) :
    E+1+2*m∈(pairStoreResult before base E m error charge).live ∧
    E+2+2*m∈(pairStoreResult before base E m error charge).live ∧
    (pairStoreResult before base E m error charge).heap (E+1+2*m)=.rational error ∧
    (pairStoreResult before base E m error charge).heap (E+2+2*m)=.rational charge := by
  have first : E+1+2*m=E+(m*2+1) := by omega
  have later : E+2+2*m=E+(m*2+1)+1 := by omega
  rw [first,later,pairStore_live,pairStore_heap]
  refine ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),Finset.mem_insert_self _ _,?_,?_⟩
  · rw [Function.update_of_ne (by omega : E+(m*2+1)≠E+(m*2+1)+1),Function.update_self]
  · exact Function.update_self _ _ _

theorem pairStore_actual (program : Program) (input : List Cell) (before : State)
    (base E m : ℕ) (error charge : ℚ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hE : values 0=.natural E) (hm : values 8=.natural m)
    (he : values 9=.rational error) (hc : values 11=.rational charge)
    (separated : base+48≤E) (hfetch : FetchesCode program before.pc pairStoreCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (pairStoreResult before base E m error charge) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤315 ∧ Header (pairStoreResult before base E m error charge) base values := by
  have zeroLive : base∈before.live := by simpa only [Nat.add_zero] using header.live 0 (by decide)
  have zeroValue : before.heap base=.natural E := by
    simpa only [Nat.add_zero] using (header.value 0 (by decide)).trans hE
  obtain ⟨trace,hh,hl,hchain,ht,_⟩ :=
    linearExecute_trace_time program input pairStoreCode pairStore_straight before
      (pairStoreResult before base E m error charge) hfetch
      (pairStore_execute input before base E m error charge hbase zeroLive (header.live 8 (by decide))
        (header.live 9 (by decide)) (header.live 11 (by decide)) zeroValue
        ((header.value 8 (by decide)).trans hm) ((header.value 9 (by decide)).trans he)
        ((header.value 11 (by decide)).trans hc))
  exact ⟨trace,hh,hl,hchain,ht,pairStore_header before base E m error charge values header separated⟩

end RootD27.Endpoint
