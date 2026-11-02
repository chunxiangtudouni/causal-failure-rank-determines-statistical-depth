module
public import Paid.PDCompute_Pack_SmallBits_060
public import Paid.PDCompute_SolverDenseReadTrace_057

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute storeSlot storeSlotResult)

theorem oldIncrement_prefix_safe (input : List Cell) (before after : State) (pointer budget count : ℕ)
    (safe : SafeBits before budget) (pointerValue : before.register .old=.natural pointer)
    (resultBits : 1+natBits (pointer+1) ≤ budget) (pcBits : natBits (before.pc+2) ≤ budget) (bound : count ≤ 2)
    (execute : linearExecute input ((constantNatPair .flag 1 .add .old .old .flag).take count) before=some after) : SafeBits after budget := by
  have oneBits : 1+natBits 1 ≤ budget:=by
    have mono:=natBits_mono (by omega : 1 ≤ pointer+1)
    omega
  exact constantNatPair_prefix_safe input before after .flag 1 .add .old .old .flag pointer 1 (pointer+1) budget count safe oneBits
    (by simp [constantNatFirst,State.set,pointerValue]) (by simp [constantNatFirst,State.set]) rfl resultBits pcBits bound execute

/-- Dense data are copied using their live-heap bit certificate; arbitrary
natural action levels are not required to be below the pointer cap. -/
theorem denseReadCell_prefix_safe (input : List Cell) (before after : State) (base target pointer budget count : ℕ)
    (fresh : before.register .fresh=.natural base) (pointerValue : before.register .old=.natural pointer)
    (live : pointer∈before.live) (safe : SafeBits before budget)
    (addressBits : 1+natBits (base+target) ≤ budget) (resultBits : 1+natBits (pointer+1) ≤ budget)
    (counter : natBits (before.pc+6) ≤ budget) (bound : count ≤ 6)
    (execute : linearExecute input ((denseReadCellCode target).take count) before=some after) : SafeBits after budget := by
  let loaded:=({before with pc:=before.pc+1}).set .total (before.heap pointer)
  let stored:=storeSlotResult loaded base target .total
  have pc1 : natBits (before.pc+1) ≤ budget:=(natBits_mono (by omega : before.pc+1 ≤ before.pc+6)).trans counter
  have pc2 : natBits (loaded.pc+3) ≤ budget:=by
    change natBits (before.pc+1+3) ≤ budget
    exact (natBits_mono (by omega : before.pc+1+3 ≤ before.pc+6)).trans counter
  have pc3 : natBits (stored.pc+2) ≤ budget:=by
    change natBits (before.pc+1+3+2) ≤ budget
    simpa only [Nat.add_assoc] using counter
  have loadedSafe : SafeBits loaded budget:=(safe.withPC (before.pc+1) pc1).set .total (before.heap pointer) (safe.heap pointer live)
  have storedSafe : SafeBits stored budget:=storeSlotResult_safe loaded base target budget .total loadedSafe addressBits pc2
  have loadedBase : loaded.register .fresh=.natural base:=by simp [loaded,State.set,fresh]
  have storedPointer : stored.register .old=.natural pointer:=by simp [stored,storeSlotResult,loaded,State.set,pointerValue]
  have run1 : linearExecute input [.load .total .old] before=some loaded:=by
    simp [linearExecute,Instruction.execute,pointerValue,Cell.nat?,live,loaded]
  have run2:=PDLower.CalibrationCompute.storeSlot_execute input loaded base target .total loadedBase (by decide)
  have prefix1:=instruction_prefix_invariant input (.load .total .old) before (fun state=>SafeBits state budget) safe
    (fun state run=>load_execute_safe input before state .total .old pointer budget safe pointerValue live pc1 run)
  have prefix2 : ∀ take ≤ (storeSlot target .total).length,∀ state,
      linearExecute input ((storeSlot target .total).take take) loaded=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact storeSlot_prefix_safe input loaded state base target budget take .total loadedSafe loadedBase (by decide) addressBits pc2 takeBound run
  have prefix3 : ∀ take ≤ (constantNatPair .flag 1 .add .old .old .flag).length,∀ state,
      linearExecute input ((constantNatPair .flag 1 .add .old .old .flag).take take) stored=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact oldIncrement_prefix_safe input stored state pointer budget take storedSafe storedPointer resultBits pc3 takeBound run
  have tail:=invariant_prefix_append input (storeSlot target .total) (constantNatPair .flag 1 .add .old .old .flag)
    loaded stored run2 (fun state=>SafeBits state budget) prefix2 prefix3
  have combined:=invariant_prefix_append input [.load .total .old]
    (storeSlot target .total++constantNatPair .flag 1 .add .old .old .flag) before loaded run1 (fun state=>SafeBits state budget) prefix1 tail
  have allPrefixes : ∀ take ≤ (denseReadCellCode target).length,∀ state,
      linearExecute input ((denseReadCellCode target).take take) before=some state → SafeBits state budget:=by
    simpa only [denseReadCellCode,constantNatPair,List.append_assoc] using combined
  exact allPrefixes count bound after execute

theorem denseReadCell_trace_safe (program : Program) (input : List Cell) (before : State) (base target pointer budget : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : target<headerWords)
    (fresh : before.register .fresh=.natural base) (pointerValue : before.register .old=.natural pointer)
    (live : pointer∈before.live) (safe : SafeBits before budget)
    (addressBits : 1+natBits (base+target) ≤ budget) (resultBits : 1+natBits (pointer+1) ≤ budget)
    (counter : natBits (before.pc+6) ≤ budget) (fetched : FetchesCode program before.pc (denseReadCellCode target)) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (denseReadCellResult before base target pointer) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 105 ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have run:=denseReadCellCode_execute input before base target pointer fresh pointerValue live
  obtain ⟨trace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input (denseReadCellCode target)
    (denseReadCellCode_straight target) before _ fetched run (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state executed
      have countBound : count ≤ 6:=by simpa only [denseReadCellCode_length] using bound
      exact ⟨denseReadCellCode_prefix_memory input before state base target pointer values header inside fresh pointerValue live count countBound executed,
        denseReadCell_prefix_safe input before state base target pointer budget count fresh pointerValue live safe addressBits resultBits counter countBound executed⟩)
  refine ⟨trace,hh,hl,hchain,?_,fun state member=>(invariant state member).1,fun state member=>(invariant state member).2⟩
  simpa only [denseReadCellCode_length] using ht

end PDCompute.Pack
