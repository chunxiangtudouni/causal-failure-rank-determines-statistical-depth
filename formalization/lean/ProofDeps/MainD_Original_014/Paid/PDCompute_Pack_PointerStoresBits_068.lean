module
public import Paid.PDCompute_Pack_NaturalCap_054
public import Paid.PDCompute_Pack_SmallBits_060
public import Paid.PDCompute_Pack_PointerTrace_021

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute storeSlot storeSlotResult)

theorem pointerStores_prefix_safe (input : List Cell) (before after : State) (base n k budget count : ℕ)
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before budget)
    (naturalBound : ∀ value ≤ naturalCap base n k,1+natBits value ≤ budget)
    (counter : natBits (before.pc+11) ≤ budget) (bound : count ≤ 11)
    (execute : linearExecute input (pointerStoresCode.take count) before=some after) : SafeBits after budget := by
  let first:=storeSlotResult before base outputStart .total
  let second:=storeSlotResult first base outputCursor .total
  let arithmetic:=sourcePointerResult second base
  have base1 : first.register .fresh=.natural base:=by simp [first,storeSlotResult,fresh]
  have base2 : second.register .fresh=.natural base:=by simp [second,storeSlotResult,base1]
  have base3 : arithmetic.register .fresh=.natural base:=by simp [arithmetic,sourcePointerResult,State.set,base2]
  have address1:=naturalBound _ (naturalCap_header_address base n k outputStart (by decide))
  have address2:=naturalBound _ (naturalCap_header_address base n k outputCursor (by decide))
  have address3:=naturalBound _ (naturalCap_header_address base n k sourceCursor (by decide))
  have sourceBound : base+48 ≤ naturalCap base n k:=by unfold naturalCap workspaceSize headerWords;omega
  have sourceBits:=naturalBound _ sourceBound
  have pc1 : natBits (before.pc+3) ≤ budget:=(natBits_mono (by omega : before.pc+3 ≤ before.pc+11)).trans counter
  have pc2 : natBits (first.pc+3) ≤ budget:=by
    change natBits (before.pc+3+3) ≤ budget
    exact (natBits_mono (by omega : before.pc+3+3 ≤ before.pc+11)).trans counter
  have pc3 : natBits (second.pc+2) ≤ budget:=by
    change natBits (before.pc+3+3+2) ≤ budget
    exact (natBits_mono (by omega : before.pc+3+3+2 ≤ before.pc+11)).trans counter
  have pc4 : natBits (arithmetic.pc+3) ≤ budget:=by
    change natBits (before.pc+3+3+2+3) ≤ budget
    simpa only [Nat.add_assoc] using counter
  have safe1 : SafeBits first budget:=storeSlotResult_safe before base outputStart budget .total safe address1 pc1
  have safe2 : SafeBits second budget:=storeSlotResult_safe first base outputCursor budget .total safe1 address2 pc2
  have run1:=PDLower.CalibrationCompute.storeSlot_execute input before base outputStart .total fresh (by decide)
  have run2:=PDLower.CalibrationCompute.storeSlot_execute input first base outputCursor .total base1 (by decide)
  have run3:=sourcePointer_execute input second base base2
  have safe3 : SafeBits arithmetic budget:=sourcePointer_prefix_safe input second arithmetic base budget 2 safe2 base2
    sourceBits pc3 (le_refl _) run3
  have prefixes1 : ∀ take ≤ (storeSlot outputStart .total).length,∀ state,
      linearExecute input ((storeSlot outputStart .total).take take) before=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact storeSlot_prefix_safe input before state base outputStart budget take .total safe fresh (by decide) address1 pc1 takeBound run
  have prefixes2 : ∀ take ≤ (storeSlot outputCursor .total).length,∀ state,
      linearExecute input ((storeSlot outputCursor .total).take take) first=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact storeSlot_prefix_safe input first state base outputCursor budget take .total safe1 base1 (by decide) address2 pc2 takeBound run
  have prefixes3 : ∀ take ≤ sourcePointerCode.length,∀ state,
      linearExecute input (sourcePointerCode.take take) second=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact sourcePointer_prefix_safe input second state base budget take safe2 base2 sourceBits pc3 takeBound run
  have prefixes4 : ∀ take ≤ (storeSlot sourceCursor .total).length,∀ state,
      linearExecute input ((storeSlot sourceCursor .total).take take) arithmetic=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact storeSlot_prefix_safe input arithmetic state base sourceCursor budget take .total safe3 base3 (by decide) address3 pc4 takeBound run
  have tail:=invariant_prefix_append input sourcePointerCode (storeSlot sourceCursor .total) second arithmetic run3
    (fun state=>SafeBits state budget) prefixes3 prefixes4
  have middle:=invariant_prefix_append input (storeSlot outputCursor .total) (sourcePointerCode++storeSlot sourceCursor .total)
    first second run2 (fun state=>SafeBits state budget) prefixes2 tail
  have combined:=invariant_prefix_append input (storeSlot outputStart .total)
    (storeSlot outputCursor .total++(sourcePointerCode++storeSlot sourceCursor .total)) before first run1
    (fun state=>SafeBits state budget) prefixes1 middle
  have allPrefixes : ∀ take ≤ pointerStoresCode.length,∀ state,
      linearExecute input (pointerStoresCode.take take) before=some state → SafeBits state budget:=by
    simpa only [pointerStoresCode,List.append_assoc] using combined
  exact allPrefixes count bound after execute

theorem pointerStores_trace_safe (program : Program) (input : List Cell) (before : State) (base n k budget : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (safe : SafeBits before budget) (naturalBound : ∀ value ≤ naturalCap base n k,1+natBits value ≤ budget)
    (counter : natBits (before.pc+11) ≤ budget) (fetched : FetchesCode program before.pc pointerStoresCode) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (pointerStoresResult before base) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 180 ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have run:=pointerStores_execute input before base fresh
  obtain ⟨trace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input pointerStoresCode
    pointerStores_straight before _ fetched run (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state executed
      have countBound : count ≤ 11:=by simpa only [pointerStoresCode_length] using bound
      exact ⟨pointerStores_prefix_memory input before state base values header fresh count bound executed,
        pointerStores_prefix_safe input before state base n k budget count fresh safe naturalBound counter countBound executed⟩)
  refine ⟨trace,hh,hl,hchain,?_,fun state member=>(invariant state member).1,fun state member=>(invariant state member).2⟩
  simpa only [pointerStoresCode_length] using ht

end PDCompute.Pack
