module
public import Paid.PDCompute_Pack_DenseReadCellBits_070
public import Paid.PDCompute_SolverDenseWrite_075

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)

theorem denseWriteCell_prefix_safe (input : List Cell) (before after : State) (base source pointer budget count : ℕ)
    (fresh : before.register .fresh=.natural base) (pointerValue : before.register .old=.natural pointer)
    (live : base+source∈before.live) (safe : SafeBits before budget)
    (addressBits : 1+natBits (base+source) ≤ budget) (resultBits : 1+natBits (pointer+1) ≤ budget)
    (counter : natBits (before.pc+6) ≤ budget) (bound : count ≤ 6)
    (execute : linearExecute input ((denseWriteCellCode source).take count) before=some after) : SafeBits after budget := by
  let loaded:=loadSlotResult before base source .total
  let stored : State :=
    {loaded with
      heap:=Function.update loaded.heap pointer (loaded.register .total)
      live:=insert pointer loaded.live
      pc:=loaded.pc+1}
  have pc1 : natBits (before.pc+3) ≤ budget:=(natBits_mono (by omega : before.pc+3 ≤ before.pc+6)).trans counter
  have pc2 : natBits (loaded.pc+1) ≤ budget:=by
    change natBits (before.pc+3+1) ≤ budget
    exact (natBits_mono (by omega : before.pc+3+1 ≤ before.pc+6)).trans counter
  have pc3 : natBits (stored.pc+2) ≤ budget:=by
    change natBits (before.pc+3+1+2) ≤ budget
    simpa only [Nat.add_assoc] using counter
  have loadedSafe : SafeBits loaded budget:=loadSlotResult_safe before base source budget .total safe live addressBits pc1
  have loadedPointer : loaded.register .old=.natural pointer:=by simp [loaded,loadSlotResult,pointerValue]
  have pointerBits : natBits pointer ≤ budget:=by
    have represented:=safe.register .old
    rw [pointerValue] at represented
    change 1+natBits pointer ≤ budget at represented
    omega
  have storedSafe : SafeBits stored budget:=(loadedSafe.store pointer (loaded.register .total) pointerBits (loadedSafe.register .total)).withPC (loaded.pc+1) pc2
  have storedPointer : stored.register .old=.natural pointer:=loadedPointer
  have run1:=PDLower.CalibrationCompute.loadSlot_execute input before base source .total fresh live
  have run2 : linearExecute input [.store .old .total] loaded=some stored:=by
    simp [linearExecute,Instruction.execute,loadedPointer,Cell.nat?,stored]
  have prefix1 : ∀ take ≤ (loadSlot source .total).length,∀ state,
      linearExecute input ((loadSlot source .total).take take) before=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact loadSlot_prefix_safe input before state base source budget take .total safe fresh live addressBits pc1 takeBound run
  have prefix2:=instruction_prefix_invariant input (.store .old .total) loaded (fun state=>SafeBits state budget) loadedSafe
    (fun state run=>store_execute_safe input loaded state .old .total pointer budget loadedSafe loadedPointer pc2 run)
  have prefix3 : ∀ take ≤ (constantNatPair .flag 1 .add .old .old .flag).length,∀ state,
      linearExecute input ((constantNatPair .flag 1 .add .old .old .flag).take take) stored=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact oldIncrement_prefix_safe input stored state pointer budget take storedSafe storedPointer resultBits pc3 takeBound run
  have tail:=invariant_prefix_append input [.store .old .total] (constantNatPair .flag 1 .add .old .old .flag)
    loaded stored run2 (fun state=>SafeBits state budget) prefix2 prefix3
  have combined:=invariant_prefix_append input (loadSlot source .total)
    ([.store .old .total]++constantNatPair .flag 1 .add .old .old .flag) before loaded run1 (fun state=>SafeBits state budget) prefix1 tail
  have allPrefixes : ∀ take ≤ (denseWriteCellCode source).length,∀ state,
      linearExecute input ((denseWriteCellCode source).take take) before=some state → SafeBits state budget:=by
    simpa only [denseWriteCellCode,constantNatPair,List.cons_append,List.nil_append] using combined
  exact allPrefixes count bound after execute

theorem denseWriteCell_trace_safe (program : Program) (input : List Cell) (before : State) (base source pointer budget : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : source<headerWords)
    (fresh : before.register .fresh=.natural base) (pointerValue : before.register .old=.natural pointer)
    (safe : SafeBits before budget) (addressBits : 1+natBits (base+source) ≤ budget) (resultBits : 1+natBits (pointer+1) ≤ budget)
    (counter : natBits (before.pc+6) ≤ budget) (fetched : FetchesCode program before.pc (denseWriteCellCode source)) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (denseWriteCellResult before base source pointer) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 105 ∧
      (∀ state∈trace,CellWriteMemory before state pointer) ∧ (∀ state∈trace,SafeBits state budget) := by
  have live:=header.live source inside
  have run:=denseWriteCellCode_execute input before base source pointer fresh pointerValue live
  obtain ⟨trace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input (denseWriteCellCode source)
    (denseWriteCellCode_straight source) before _ fetched run (fun state=>CellWriteMemory before state pointer ∧ SafeBits state budget) (by
      intro count bound state executed
      have countBound : count ≤ 6:=by simpa only [denseWriteCellCode_length] using bound
      exact ⟨denseWriteCellCode_prefix_memory input before state base source pointer fresh pointerValue live count countBound executed,
        denseWriteCell_prefix_safe input before state base source pointer budget count fresh pointerValue live safe addressBits resultBits counter countBound executed⟩)
  refine ⟨trace,hh,hl,hchain,?_,fun state member=>(invariant state member).1,fun state member=>(invariant state member).2⟩
  simpa only [denseWriteCellCode_length] using ht

end PDCompute.Pack
