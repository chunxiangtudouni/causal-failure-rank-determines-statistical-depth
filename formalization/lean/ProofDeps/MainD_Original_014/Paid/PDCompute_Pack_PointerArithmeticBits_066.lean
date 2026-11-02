module
public import Paid.PDCompute_Pack_PointerTailBits_065
public import Paid.PDCompute_Pack_ArithmeticMemory_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)

theorem pointerArithmetic_split : pointerArithmeticCode=
    loadSlot rowRemaining .index++loadSlot columnsPerRow .value++pointerTailCode := rfl

theorem pointerArithmetic_prefix_safe (input : List Cell) (before after : State) (base n k budget count : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (rows : values rowRemaining=.natural (n+1)) (columns : values columnsPerRow=.natural (k+1))
    (safe : SafeBits before budget) (naturalBound : ∀ value ≤ naturalCap base n k,1+natBits value ≤ budget)
    (counter : natBits (before.pc+12) ≤ budget) (bound : count ≤ 12)
    (execute : linearExecute input (pointerArithmeticCode.take count) before=some after) : SafeBits after budget := by
  let first:=loadSlotResult before base rowRemaining .index
  let second:=loadSlotResult first base columnsPerRow .value
  have address1 : 1+natBits (base+rowRemaining) ≤ budget:=naturalBound _ (naturalCap_header_address base n k rowRemaining (by decide))
  have address2 : 1+natBits (base+columnsPerRow) ≤ budget:=naturalBound _ (naturalCap_header_address base n k columnsPerRow (by decide))
  have pc1 : natBits (before.pc+3) ≤ budget:=(natBits_mono (by omega : before.pc+3 ≤ before.pc+12)).trans counter
  have pc2 : natBits (first.pc+3) ≤ budget:=by
    change natBits (before.pc+3+3) ≤ budget
    exact (natBits_mono (by omega : before.pc+3+3 ≤ before.pc+12)).trans counter
  have pc3 : natBits (second.pc+6) ≤ budget:=by
    change natBits (before.pc+3+3+6) ≤ budget
    simpa only [Nat.add_assoc] using counter
  have firstHeader : Header first base values:=header
  have firstFresh : first.register .fresh=.natural base:=(loadSlotResult_fresh before base rowRemaining .index (by decide)).trans fresh
  have firstRows : first.register .index=.natural (n+1):=(header.loadSlot_execute input rowRemaining .index (by decide) fresh).2.trans rows
  have secondFresh : second.register .fresh=.natural base:=(loadSlotResult_fresh first base columnsPerRow .value (by decide)).trans firstFresh
  have secondRows : second.register .index=.natural (n+1):=by
    simpa only [second,loadSlotResult,Function.update_of_ne (by decide : (.index : Register)≠.value),
      Function.update_of_ne (by decide : (.index : Register)≠.address)] using firstRows
  have secondColumns : second.register .value=.natural (k+1):=(firstHeader.loadSlot_execute input columnsPerRow .value (by decide) firstFresh).2.trans columns
  have firstSafe : SafeBits first budget:=loadSlotResult_safe before base rowRemaining budget .index safe (header.live rowRemaining (by decide)) address1 pc1
  have secondSafe : SafeBits second budget:=loadSlotResult_safe first base columnsPerRow budget .value firstSafe
    (firstHeader.live columnsPerRow (by decide)) address2 pc2
  have run1:=(header.loadSlot_execute input rowRemaining .index (by decide) fresh).1
  have run2:=(firstHeader.loadSlot_execute input columnsPerRow .value (by decide) firstFresh).1
  have prefix1 : ∀ take ≤ (loadSlot rowRemaining .index).length,∀ state,
      linearExecute input ((loadSlot rowRemaining .index).take take) before=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact loadSlot_prefix_safe input before state base rowRemaining budget take .index safe fresh
      (header.live rowRemaining (by decide)) address1 pc1 takeBound run
  have prefix2 : ∀ take ≤ (loadSlot columnsPerRow .value).length,∀ state,
      linearExecute input ((loadSlot columnsPerRow .value).take take) first=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact loadSlot_prefix_safe input first state base columnsPerRow budget take .value firstSafe firstFresh
      (firstHeader.live columnsPerRow (by decide)) address2 pc2 takeBound run
  have prefix3 : ∀ take ≤ pointerTailCode.length,∀ state,
      linearExecute input (pointerTailCode.take take) second=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact pointerTail_prefix_safe input second state base n k budget take secondFresh secondRows secondColumns secondSafe naturalBound pc3 takeBound run
  have tail:=invariant_prefix_append input (loadSlot columnsPerRow .value) pointerTailCode first second run2
    (fun state=>SafeBits state budget) prefix2 prefix3
  have combined:=invariant_prefix_append input (loadSlot rowRemaining .index) (loadSlot columnsPerRow .value++pointerTailCode)
    before first run1 (fun state=>SafeBits state budget) prefix1 tail
  have allPrefixes : ∀ take ≤ pointerArithmeticCode.length,∀ state,
      linearExecute input (pointerArithmeticCode.take take) before=some state → SafeBits state budget:=by
    simpa only [pointerArithmetic_split,List.append_assoc] using combined
  exact allPrefixes count bound after execute

theorem pointerArithmetic_trace_safe (program : Program) (input : List Cell) (before : State) (base n k budget : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (rows : values rowRemaining=.natural (n+1)) (columns : values columnsPerRow=.natural (k+1))
    (safe : SafeBits before budget) (naturalBound : ∀ value ≤ naturalCap base n k,1+natBits value ≤ budget)
    (counter : natBits (before.pc+12) ≤ budget) (fetched : FetchesCode program before.pc pointerArithmeticCode) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (pointerArithmeticResult before base n k) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 195 ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have run:=pointerArithmetic_execute input before base n k values header fresh rows columns
  have straight : StraightCode pointerArithmeticCode:=by
    rw [pointerArithmetic_split]
    intro instruction member
    simp only [List.mem_append] at member
    rcases member with (left|right)|tail
    · exact loadSlot_straight rowRemaining .index instruction left
    · exact loadSlot_straight columnsPerRow .value instruction right
    · simp only [pointerTailCode,List.mem_cons,List.not_mem_nil,or_false] at tail
      rcases tail with h|h|h|h|h|h <;> subst instruction <;> trivial
  obtain ⟨trace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input pointerArithmeticCode straight before _ fetched run
    (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state executed
      have countBound : count ≤ 12:=by simpa only [pointerArithmeticCode_length] using bound
      exact ⟨pointerArithmetic_prefix_memory input before state base count executed,
        pointerArithmetic_prefix_safe input before state base n k budget count values header fresh rows columns safe naturalBound counter countBound executed⟩)
  refine ⟨trace,hh,hl,hchain,?_,fun state member=>(invariant state member).1,fun state member=>(invariant state member).2⟩
  simpa only [pointerArithmeticCode_length] using ht

end PDCompute.Pack
