module

public import Paid.RootD27Endpoint_Code_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot loadSlotResult storeSlotResult)

def cacheHeaderResult (before : State) (base M E : ℕ) : State :=
  let loaded:=loadSlotResult before base 3 .total
  let counted:=(({loaded with pc:=loaded.pc+2}).set .value (.natural 1)).set .total (.natural (M+1))
  let saved:=storeSlotResult counted base 17 .total
  let addressed:=loadSlotResult saved base 0 .address
  {addressed with
    heap:=Function.update addressed.heap E (.natural (M+1))
    live:=insert E addressed.live
    pc:=addressed.pc+1}

theorem cacheHeader_straight : StraightCode cacheHeaderCode := by
  simp [StraightCode,cacheHeaderCode,loadSlot,storeSlot,StraightInstruction]

theorem cacheHeader_execute (input : List Cell) (before : State) (base M E : ℕ)
    (hbase : before.register .fresh=.natural base)
    (hzero : base∈before.live) (hthree : base+3∈before.live)
    (hM : before.heap (base+3)=.natural M) (hE : before.heap base=.natural E) :
    linearExecute input cacheHeaderCode before=some (cacheHeaderResult before base M E) := by
  simp [cacheHeaderCode,cacheHeaderResult,loadSlot,storeSlot,loadSlotResult,storeSlotResult,
    linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,hzero,hthree,hM,hE,
    Nat.add_assoc]

theorem cacheHeader_heap (before : State) (base M E : ℕ) :
    (cacheHeaderResult before base M E).heap=
      Function.update (Function.update before.heap (base+17) (.natural (M+1))) E (.natural (M+1)) := by
  simp [cacheHeaderResult,loadSlotResult,storeSlotResult,State.set]

theorem cacheHeader_live (before : State) (base M E : ℕ) :
    (cacheHeaderResult before base M E).live=insert E (insert (base+17) before.live) := rfl

theorem cacheHeader_pc (before : State) (base M E : ℕ) :
    (cacheHeaderResult before base M E).pc=before.pc+12 := by
  simp [cacheHeaderResult,loadSlotResult,storeSlotResult,State.set,Nat.add_assoc]

theorem cacheHeader_fresh (before : State) (base M E : ℕ) :
    (cacheHeaderResult before base M E).register .fresh=before.register .fresh := by
  simp [cacheHeaderResult,loadSlotResult,storeSlotResult,State.set]

theorem cacheHeader_output (before : State) (base M E : ℕ) :
    (cacheHeaderResult before base M E).output=before.output := rfl

theorem cacheHeader_header (before : State) (base M E : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (separated : base+48≤E) :
    Header (cacheHeaderResult before base M E) base (Function.update values 17 (.natural (M+1))) := by
  intro slot inside
  have bound : slot<48 := inside
  constructor
  · rw [cacheHeader_live]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (header.live slot inside))
  · rw [cacheHeader_heap,Function.update_of_ne (by omega : base+slot≠E)]
    by_cases same : slot=17
    · subst slot
      simp only [Function.update_self]
    · rw [Function.update_of_ne (by omega : base+slot≠base+17),Function.update_of_ne same]
      exact header.value slot inside

/-- The cache list header is a real heap store. This is the initial one-cell
prefix of the ORIGINAL encoded endpoint list, not a prefilled output. -/
theorem cacheHeader_cell (before : State) (base M E : ℕ) :
    E∈(cacheHeaderResult before base M E).live ∧
    (cacheHeaderResult before base M E).heap E=.natural (M+1) := by
  constructor
  · rw [cacheHeader_live]
    exact Finset.mem_insert_self _ _
  · rw [cacheHeader_heap,Function.update_self]

theorem cacheHeader_actual (program : Program) (input : List Cell) (before : State)
    (base M E : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hM : values 3=.natural M)
    (hE : values 0=.natural E) (separated : base+48≤E)
    (hfetch : FetchesCode program before.pc cacheHeaderCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (cacheHeaderResult before base M E) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤195 ∧
      Header (cacheHeaderResult before base M E) base (Function.update values 17 (.natural (M+1))) ∧
      E∈(cacheHeaderResult before base M E).live ∧
      (cacheHeaderResult before base M E).heap E=.natural (M+1) := by
  have hz : base∈before.live := by simpa only [Nat.add_zero] using header.live 0 (by decide)
  have hv : before.heap base=.natural E := by
    simpa only [Nat.add_zero] using (header.value 0 (by decide)).trans hE
  obtain ⟨trace,hh,hl,hc,ht,_⟩ :=
    linearExecute_trace_time program input cacheHeaderCode cacheHeader_straight before
      (cacheHeaderResult before base M E) hfetch
      (cacheHeader_execute input before base M E hbase hz (header.live 3 (by decide))
        ((header.value 3 (by decide)).trans hM) hv)
  exact ⟨trace,hh,hl,hc,ht,cacheHeader_header before base M E values header separated,
    (cacheHeader_cell before base M E).1,(cacheHeader_cell before base M E).2⟩

end RootD27.Endpoint
