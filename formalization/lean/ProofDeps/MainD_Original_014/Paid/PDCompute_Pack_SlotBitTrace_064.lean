module
public import Paid.RootD27Bits_SlotPrefix_004
public import Paid.PDCompute_Pack_TraceInvariant_055

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame RootD27.Bits
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot storeSlotResult)

/-- One actual fetched three-op load: exact end state, real time,
physical frame and original all-register/heap/output/pc bits on SAME trace. -/
theorem loadSlot_trace_safe (program : Program) (input : List Cell) (before : State)
    (base slot budget : ℕ) (target : Register) (values : ℕ → Cell)
    (header : Header before base values) (inside : slot<headerWords) (hbase : before.register .fresh=.natural base)
    (safe : SafeBits before budget) (addressBits : 1+natBits (base+slot) ≤ budget)
    (pcBits : natBits (before.pc+3) ≤ budget) (fetched : FetchesCode program before.pc (loadSlot slot target)) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (loadSlotResult before base slot target) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 60 ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have run:=(header.loadSlot_execute input slot target inside hbase).1
  obtain ⟨trace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input (loadSlot slot target)
    (loadSlot_straight slot target) before _ fetched run (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state executed
      have countBound : count ≤ 3:=by simpa only [loadSlot,List.length_cons,List.length_nil] using bound
      have memory:=loadSlot_prefix_memory input before state base slot target hbase (header.live slot inside) count countBound executed
      exact ⟨HeaderMemory.of_unchanged base memory.1 memory.2.1 memory.2.2,
        loadSlot_prefix_safe input before state base slot budget count target safe hbase (header.live slot inside) addressBits pcBits countBound executed⟩)
  refine ⟨trace,hh,hl,hchain,?_,fun state member=>(invariant state member).1,fun state member=>(invariant state member).2⟩
  simpa only [loadSlot,List.length_cons,List.length_nil] using ht

theorem storeSlot_trace_safe (program : Program) (input : List Cell) (before : State)
    (base slot budget : ℕ) (source : Register) (values : ℕ → Cell)
    (header : Header before base values) (inside : slot<headerWords) (hbase : before.register .fresh=.natural base)
    (different : source≠.address) (safe : SafeBits before budget) (addressBits : 1+natBits (base+slot) ≤ budget)
    (pcBits : natBits (before.pc+3) ≤ budget) (fetched : FetchesCode program before.pc (storeSlot slot source)) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (storeSlotResult before base slot source) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 60 ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have straight : StraightCode (storeSlot slot source) := by
    intro instruction member
    simp only [storeSlot,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h <;> subst instruction <;> trivial
  have run:=PDLower.CalibrationCompute.storeSlot_execute input before base slot source hbase different
  obtain ⟨trace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input (storeSlot slot source)
    straight before _ fetched run (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state executed
      have countBound : count ≤ 3:=by simpa only [storeSlot,List.length_cons,List.length_nil] using bound
      exact ⟨storeSlot_prefix_memory input before state base slot source values header inside hbase different count countBound executed,
        storeSlot_prefix_safe input before state base slot budget count source safe hbase different addressBits pcBits countBound executed⟩)
  refine ⟨trace,hh,hl,hchain,?_,fun state member=>(invariant state member).1,fun state member=>(invariant state member).2⟩
  simpa only [storeSlot,List.length_cons,List.length_nil] using ht

end PDCompute.Pack
