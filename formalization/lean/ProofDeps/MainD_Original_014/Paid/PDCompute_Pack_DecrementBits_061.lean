module
public import Paid.PDCompute_Pack_SmallBits_060
public import Paid.PDCompute_Pack_Decrement_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot)

def decrementComputed (before : State) (base slot value : ℕ) : State:=
  let loaded:=loadSlotResult before base slot .index
  ({constantNatFirst loaded .flag 1 with pc:=loaded.pc+2}).set .index (.natural (value-1))

theorem decrement_prefix_safe (input : List Cell) (before after : State) (base slot value budget count : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : slot<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values slot=.natural value)
    (safe : SafeBits before budget) (addressBits : 1+natBits (base+slot) ≤ budget)
    (oneBits : 1+natBits 1 ≤ budget) (pcBits : natBits (before.pc+8) ≤ budget) (bound : count ≤ 8)
    (execute : linearExecute input ((decrementSlot slot).take count) before=some after) : SafeBits after budget := by
  let loaded:=loadSlotResult before base slot .index
  let computed:=decrementComputed before base slot value
  let pair:=constantNatPair .flag 1 .subtract .index .index .flag
  have loadPC : natBits (before.pc+3) ≤ budget:=(natBits_mono (by omega : before.pc+3 ≤ before.pc+8)).trans pcBits
  have loadedSafe : SafeBits loaded budget:=loadSlotResult_safe before base slot budget .index safe (header.live slot inside) addressBits loadPC
  have loadedIndex : loaded.register .index=.natural value:=(header.loadSlot_execute input slot .index inside hbase).2.trans hvalue
  have pairPC : natBits (loaded.pc+2) ≤ budget := by
    change natBits (before.pc+3+2) ≤ budget
    exact (natBits_mono (by omega : before.pc+3+2 ≤ before.pc+8)).trans pcBits
  have resultBits : 1+natBits (value-1) ≤ budget := by
    have previous:=loadedSafe.register .index
    rw [loadedIndex] at previous
    have mono:=natBits_mono (Nat.sub_le value 1)
    change 1+natBits value ≤ budget at previous
    omega
  have firstValue : (constantNatFirst loaded .flag 1).register .index=.natural value:=by simp [constantNatFirst,State.set,loadedIndex]
  have secondValue : (constantNatFirst loaded .flag 1).register .flag=.natural 1:=by simp [constantNatFirst,State.set]
  have pairRun : linearExecute input pair loaded=some computed := by
    simp [pair,constantNatPair,computed,decrementComputed,constantNatFirst,linearExecute,Instruction.execute,
      State.set,NatOp.eval,Cell.nat?,loadedIndex,Nat.add_assoc]
    simp [loaded]
  have computedSafe : SafeBits computed budget:=constantNatPair_prefix_safe input loaded computed .flag 1 .subtract .index .index .flag
    value 1 (value-1) budget 2 loadedSafe oneBits firstValue secondValue rfl resultBits pairPC (le_refl _) pairRun
  have computedBase : computed.register .fresh=.natural base:=by
    simp [computed,decrementComputed,constantNatFirst,State.set,loadSlotResult,hbase]
  have storePC : natBits (computed.pc+3) ≤ budget:=by
    change natBits (before.pc+3+2+3) ≤ budget
    simpa only [Nat.add_assoc] using pcBits
  have firstRun:=(header.loadSlot_execute input slot .index inside hbase).1
  have firstPrefixes : ∀ take ≤ (loadSlot slot .index).length,∀ state,
      linearExecute input ((loadSlot slot .index).take take) before=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact loadSlot_prefix_safe input before state base slot budget take .index safe hbase (header.live slot inside) addressBits loadPC takeBound run
  have pairPrefixes : ∀ take ≤ pair.length,∀ state,linearExecute input (pair.take take) loaded=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact constantNatPair_prefix_safe input loaded state .flag 1 .subtract .index .index .flag value 1 (value-1) budget take
      loadedSafe oneBits firstValue secondValue rfl resultBits pairPC takeBound run
  have storePrefixes : ∀ take ≤ (storeSlot slot .index).length,∀ state,
      linearExecute input ((storeSlot slot .index).take take) computed=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact storeSlot_prefix_safe input computed state base slot budget take .index computedSafe computedBase (by decide) addressBits storePC takeBound run
  have tail:=invariant_prefix_append input pair (storeSlot slot .index) loaded computed pairRun (fun state=>SafeBits state budget) pairPrefixes storePrefixes
  have combined:=invariant_prefix_append input (loadSlot slot .index) (pair++storeSlot slot .index) before loaded firstRun
    (fun state=>SafeBits state budget) firstPrefixes tail
  have allPrefixes : ∀ take ≤ (decrementSlot slot).length,∀ state,
      linearExecute input ((decrementSlot slot).take take) before=some state → SafeBits state budget:=by
    simpa only [decrementSlot,pair,constantNatPair,List.append_assoc] using combined
  exact allPrefixes count bound after execute

/-- Existing actual decrement semantics and memory proof, strengthened
on the SAME fetched trace to all-prefix original operand-bit safety. -/
theorem decrement_trace_safe (program : Program) (input : List Cell) (before : State) (base slot value budget : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : slot<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values slot=.natural value)
    (safe : SafeBits before budget) (addressBits : 1+natBits (base+slot) ≤ budget)
    (oneBits : 1+natBits 1 ≤ budget) (pcBits : natBits (before.pc+8) ≤ budget)
    (fetched : FetchesCode program before.pc (decrementSlot slot)) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (decrementResult before base slot value) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 135 ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have run:=decrement_execute input before base slot value hbase (header.live slot inside) ((header.value slot inside).trans hvalue)
  obtain ⟨trace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input (decrementSlot slot) (decrementSlot_straight slot)
    before _ fetched run (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state executed
      have countBound : count ≤ 8:=by simpa only [decrementSlot_length] using bound
      exact ⟨decrement_prefix_memory input before state base slot value values header inside hbase hvalue count countBound executed,
        decrement_prefix_safe input before state base slot value budget count values header inside hbase hvalue safe addressBits oneBits pcBits countBound executed⟩)
  refine ⟨trace,hh,hl,hchain,?_,fun state member=>(invariant state member).1,fun state member=>(invariant state member).2⟩
  simpa only [decrementSlot_length] using ht

end PDCompute.Pack
