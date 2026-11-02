module
public import Paid.PDCompute_Pack_IncrementBits_062
public import Paid.PDCompute_Pack_CounterTrace_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

theorem copyPlusOne_prefix_safe (input : List Cell) (before after : State)
    (base source target value budget count : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (sourceInside : source<headerWords) (targetInside : target<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values source=.natural value)
    (safe : SafeBits before budget) (sourceBits : 1+natBits (base+source) ≤ budget)
    (targetBits : 1+natBits (base+target) ≤ budget) (oneBits : 1+natBits 1 ≤ budget)
    (resultBits : 1+natBits (value+1) ≤ budget) (pcBits : natBits (before.pc+14) ≤ budget) (bound : count ≤ 14)
    (execute : linearExecute input ((copyPlusOneCode source target).take count) before=some after) : SafeBits after budget := by
  let copied:=copySlotResult before base source target
  have firstRun:=copySlot_execute input before base source target hbase (header.live source sourceInside)
  have firstPC : natBits (before.pc+6) ≤ budget:=(natBits_mono (by omega : before.pc+6 ≤ before.pc+14)).trans pcBits
  have copiedSafe : SafeBits copied budget:=copy_prefix_safe input before copied base source target budget 6 safe hbase
    (header.live source sourceInside) sourceBits targetBits firstPC (le_refl _) firstRun
  have copiedHeader:=header.copySlot source target sourceInside
  have copiedValue : (Function.update values target (values source)) target=.natural value:=by rw [Function.update_self,hvalue]
  have copiedBase : copied.register .fresh=.natural base:=(copySlotResult_fields before base source target).2.2.1.trans hbase
  have copiedCounter : natBits (copied.pc+8) ≤ budget:=by
    rw [(copySlotResult_fields before base source target).2.2.2.1]
    simpa only [Nat.add_assoc] using pcBits
  have firstPrefixes : ∀ take ≤ (copySlot source target).length,∀ state,
      linearExecute input ((copySlot source target).take take) before=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact copy_prefix_safe input before state base source target budget take safe hbase (header.live source sourceInside)
      sourceBits targetBits firstPC takeBound run
  have lastPrefixes : ∀ take ≤ (addNatSlot target 1).length,∀ state,
      linearExecute input ((addNatSlot target 1).take take) copied=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact increment_prefix_safe input copied state base target value 1 budget take _ copiedHeader targetInside copiedBase copiedValue
      copiedSafe targetBits oneBits resultBits copiedCounter takeBound run
  have combined:=invariant_prefix_append input (copySlot source target) (addNatSlot target 1) before copied firstRun
    (fun state=>SafeBits state budget) firstPrefixes lastPrefixes
  exact combined count bound after execute

theorem copyPlusOne_trace_safe (program : Program) (input : List Cell) (before : State)
    (base source target value budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (sourceInside : source<headerWords) (targetInside : target<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values source=.natural value)
    (safe : SafeBits before budget) (sourceBits : 1+natBits (base+source) ≤ budget)
    (targetBits : 1+natBits (base+target) ≤ budget) (oneBits : 1+natBits 1 ≤ budget)
    (resultBits : 1+natBits (value+1) ≤ budget) (pcBits : natBits (before.pc+14) ≤ budget)
    (fetched : FetchesCode program before.pc (copyPlusOneCode source target)) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (copyPlusOneResult before base source target value) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 225 ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have run:=copyPlusOne_execute input before base source target value values header sourceInside hbase hvalue
  obtain ⟨trace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input (copyPlusOneCode source target)
    (copyPlusOne_straight source target) before _ fetched run (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state executed
      have countBound : count ≤ 14:=by simpa only [copyPlusOneCode_length] using bound
      exact ⟨copyPlusOne_prefix_memory input before state base source target value values header sourceInside targetInside hbase hvalue count countBound executed,
        copyPlusOne_prefix_safe input before state base source target value budget count values header sourceInside targetInside hbase hvalue
          safe sourceBits targetBits oneBits resultBits pcBits countBound executed⟩)
  refine ⟨trace,hh,hl,hchain,?_,fun state member=>(invariant state member).1,fun state member=>(invariant state member).2⟩
  simpa only [copyPlusOneCode_length] using ht

end PDCompute.Pack
