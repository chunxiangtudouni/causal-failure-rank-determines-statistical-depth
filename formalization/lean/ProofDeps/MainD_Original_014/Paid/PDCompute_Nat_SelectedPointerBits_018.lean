module
public import Paid.PDCompute_Nat_SlotBits_001
public import Paid.PDCompute_Pack_PairBits_059
public import Paid.PDCompute_SolverSelectedPointer_079
public import Paid.PDCompute_SolverHeaderFrame_099

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot)
open PDROC.CalibrationRow.Operand

/-- The actual selected-cache address may exceed the workspace endpoint.
Only the real source+(1+2*level) and header address need new bits. -/
theorem selectedPointer_prefix_safe (input : List Cell) (before : State) (base source level budget : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : values 0=.natural source) (hlevel : values 23=.natural level)
    (safe : RootD27.Bits.SafeBits before budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (targetBits : (.natural (source+(1+2*level)) : Cell).bits≤budget) (pcBits : natBits (before.pc+14)≤budget) :
    PrefixSafe input selectedPointerCode before budget := by
  let loaded:=loadSlotResult before base 23 .index
  let doubled:=({PDCompute.Pack.constantNatFirst loaded .flag 2 with pc:=loaded.pc+2}).set .index (.natural (2*level))
  let shifted:=({PDCompute.Pack.constantNatFirst doubled .flag 1 with pc:=doubled.pc+2}).set .index (.natural (1+2*level))
  let sourceLoaded:=loadSlotResult shifted base 0 .value
  let computed:=({sourceLoaded with pc:=sourceLoaded.pc+1}).set .index (.natural (source+(1+2*level)))
  have slotBits (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : base+slot≤base+headerWords)) 1).trans addressBits
  have literal2 : 1+natBits 2≤budget:=
    (Nat.add_le_add_left (natBits_mono (by change 2≤base+48;omega)) 1).trans addressBits
  have literal1 : 1+natBits 1≤budget:=(Nat.add_le_add_left (natBits_mono (by decide : 1≤2)) 1).trans literal2
  have doubledBits : 1+natBits (2*level)≤budget:=
    (Nat.add_le_add_left (natBits_mono (by omega : 2*level≤source+(1+2*level))) 1).trans targetBits
  have shiftedBits : 1+natBits (1+2*level)≤budget:=
    (Nat.add_le_add_left (natBits_mono (by omega : 1+2*level≤source+(1+2*level))) 1).trans targetBits
  have pcSmall (counter : ℕ) (bound : counter≤before.pc+14) : natBits counter≤budget:=(natBits_mono bound).trans pcBits
  have loadRun:=(header.loadSlot_execute input 23 .index (by decide) fresh).1
  have loadSafe:=PrefixSafe.loadSlot input before base 23 budget .index safe fresh (header.live 23 (by decide)) (slotBits 23 (by decide)) (pcSmall _ (by omega))
  have loadedLevel : loaded.register .index=.natural level:=(header.loadSlot_execute input 23 .index (by decide) fresh).2.trans hlevel
  have loadedFresh : loaded.register .fresh=.natural base:=(loadSlotResult_fresh before base 23 .index (by decide)).trans fresh
  have loadedHeader : Header loaded base values:=header
  have multiplyLeft : (PDCompute.Pack.constantNatFirst loaded .flag 2).register .flag=.natural 2:=by simp [PDCompute.Pack.constantNatFirst,State.set]
  have multiplyRight : (PDCompute.Pack.constantNatFirst loaded .flag 2).register .index=.natural level:=by
    simpa only [PDCompute.Pack.constantNatFirst,State.set,Function.update_of_ne (by decide : (.index : Register)≠.flag)] using loadedLevel
  have multiplySafe : PrefixSafe input (PDCompute.Pack.constantNatPair .flag 2 .multiply .index .flag .index) loaded budget:=by
    apply PrefixSafe.of_bounded
    intro count bound state run
    exact PDCompute.Pack.constantNatPair_prefix_safe input loaded state .flag 2 .multiply .index .flag .index 2 level (2*level) budget count
      (loadSafe.final loadRun) literal2 multiplyLeft multiplyRight rfl doubledBits (pcSmall _ (by change before.pc+3+2≤before.pc+14;omega)) bound run
  have multiplyRun : linearExecute input (PDCompute.Pack.constantNatPair .flag 2 .multiply .index .flag .index) loaded=some doubled:=by
    simp [PDCompute.Pack.constantNatPair,PDCompute.Pack.constantNatFirst,linearExecute,Instruction.execute,State.set,loadedLevel,Cell.nat?,NatOp.eval,doubled,Nat.add_assoc]
  have doubledLevel : doubled.register .index=.natural (2*level):=by simp [doubled,State.set]
  have doubledFresh : doubled.register .fresh=.natural base:=by
    simpa only [doubled,PDCompute.Pack.constantNatFirst,State.set,Function.update_of_ne (by decide : (.fresh : Register)≠.index),
      Function.update_of_ne (by decide : (.fresh : Register)≠.flag)] using loadedFresh
  have doubledHeader : Header doubled base values:=loadedHeader
  have plusLeft : (PDCompute.Pack.constantNatFirst doubled .flag 1).register .flag=.natural 1:=by simp [PDCompute.Pack.constantNatFirst,State.set]
  have plusRight : (PDCompute.Pack.constantNatFirst doubled .flag 1).register .index=.natural (2*level):=by
    simpa only [PDCompute.Pack.constantNatFirst,State.set,Function.update_of_ne (by decide : (.index : Register)≠.flag)] using doubledLevel
  have shiftSafe : PrefixSafe input (PDCompute.Pack.constantNatPair .flag 1 .add .index .flag .index) doubled budget:=by
    apply PrefixSafe.of_bounded
    intro count bound state run
    exact PDCompute.Pack.constantNatPair_prefix_safe input doubled state .flag 1 .add .index .flag .index 1 (2*level) (1+2*level) budget count
      (multiplySafe.final multiplyRun) literal1 plusLeft plusRight rfl shiftedBits (pcSmall _ (by change before.pc+3+2+2≤before.pc+14;omega)) bound run
  have shiftRun : linearExecute input (PDCompute.Pack.constantNatPair .flag 1 .add .index .flag .index) doubled=some shifted:=by
    simp [PDCompute.Pack.constantNatPair,PDCompute.Pack.constantNatFirst,linearExecute,Instruction.execute,State.set,doubledLevel,Cell.nat?,NatOp.eval,shifted,Nat.add_assoc]
  have shiftedFresh : shifted.register .fresh=.natural base:=by
    simpa only [shifted,PDCompute.Pack.constantNatFirst,State.set,Function.update_of_ne (by decide : (.fresh : Register)≠.index),
      Function.update_of_ne (by decide : (.fresh : Register)≠.flag)] using doubledFresh
  have shiftedHeader : Header shifted base values:=doubledHeader
  have sourceRun:=(shiftedHeader.loadSlot_execute input 0 .value (by decide) shiftedFresh).1
  have sourceSafe:=PrefixSafe.loadSlot input shifted base 0 budget .value (shiftSafe.final shiftRun) shiftedFresh (shiftedHeader.live 0 (by decide))
    (slotBits 0 (by decide)) (pcSmall _ (by change before.pc+3+2+2+3≤before.pc+14;omega))
  have sourceValue : sourceLoaded.register .value=.natural source:=(shiftedHeader.loadSlot_execute input 0 .value (by decide) shiftedFresh).2.trans hsource
  have indexValue : sourceLoaded.register .index=.natural (1+2*level):=by
    simp [sourceLoaded,loadSlotResult,shifted,State.set]
  have sumSafe:=PrefixSafe.natOp input sourceLoaded budget .add .index .value .index source (1+2*level) (source+(1+2*level))
    (sourceSafe.final sourceRun) sourceValue indexValue rfl targetBits (pcSmall _ (by change before.pc+3+2+2+3+1≤before.pc+14;omega))
  have sumRun : linearExecute input [.natOp .add .index .value .index] sourceLoaded=some computed:=by
    simp [linearExecute,Instruction.execute,sourceValue,indexValue,Cell.nat?,NatOp.eval,computed]
  have computedFresh : computed.register .fresh=.natural base:=by
    simpa only [computed,State.set,Function.update_of_ne (by decide : (.fresh : Register)≠.index)] using
      (loadSlotResult_fresh shifted base 0 .value (by decide)).trans shiftedFresh
  have storeSafe:=PrefixSafe.storeSlot input computed base 39 budget .index (sumSafe.final sumRun) computedFresh (by decide) (slotBits 39 (by decide))
    (pcSmall _ (by change before.pc+3+2+2+3+1+3≤before.pc+14;omega))
  have firstSafe:=PrefixSafe.append input _ _ before loaded budget loadRun loadSafe multiplySafe
  have firstRun : linearExecute input (loadSlot 23 .index++PDCompute.Pack.constantNatPair .flag 2 .multiply .index .flag .index) before=some doubled:=by
    rw [PDLower.CalibrationCompute.linearExecute_append,loadRun,Option.bind_some];exact multiplyRun
  have secondSafe:=PrefixSafe.append input _ _ before doubled budget firstRun firstSafe shiftSafe
  have secondRun : linearExecute input ((loadSlot 23 .index++PDCompute.Pack.constantNatPair .flag 2 .multiply .index .flag .index)++PDCompute.Pack.constantNatPair .flag 1 .add .index .flag .index) before=some shifted:=by
    rw [PDLower.CalibrationCompute.linearExecute_append,firstRun,Option.bind_some];exact shiftRun
  have thirdSafe:=PrefixSafe.append input _ _ before shifted budget secondRun secondSafe sourceSafe
  have thirdRun : linearExecute input (((loadSlot 23 .index++PDCompute.Pack.constantNatPair .flag 2 .multiply .index .flag .index)++PDCompute.Pack.constantNatPair .flag 1 .add .index .flag .index)++loadSlot 0 .value) before=some sourceLoaded:=by
    rw [PDLower.CalibrationCompute.linearExecute_append,secondRun,Option.bind_some];exact sourceRun
  have fourthSafe:=PrefixSafe.append input _ _ before sourceLoaded budget thirdRun thirdSafe sumSafe
  have fourthRun : linearExecute input ((((loadSlot 23 .index++PDCompute.Pack.constantNatPair .flag 2 .multiply .index .flag .index)++PDCompute.Pack.constantNatPair .flag 1 .add .index .flag .index)++loadSlot 0 .value)++[.natOp .add .index .value .index]) before=some computed:=by
    rw [PDLower.CalibrationCompute.linearExecute_append,thirdRun,Option.bind_some];exact sumRun
  have complete:=PrefixSafe.append input _ _ before computed budget fourthRun fourthSafe storeSafe
  simpa only [selectedPointerCode,PDCompute.Pack.constantNatPair,List.append_assoc,List.cons_append,List.nil_append] using complete

/-- Exact fourteen-op selected-pointer trace, including final physical
write, original Header/Frame and full arbitrary-live SAME-B certificate. -/
theorem selectedPointer_trace_resources (program : Program) (input : List Cell) (before : State) (base source level n k budget : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : values 0=.natural source) (hlevel : values 23=.natural level)
    (safe : RootD27.Bits.SafeBits before budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (targetBits : (.natural (source+(1+2*level)) : Cell).bits≤budget) (pcBits : natBits (before.pc+14)≤budget)
    (fetch : FetchesCode program before.pc selectedPointerCode) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (selectedPointerResult before base source level) ∧
      trace.IsChain (fun a b=>step program input a=some b) ∧ time program trace≤225 ∧
      Header (selectedPointerResult before base source level) base (Function.update values 39 (.natural (source+(1+2*level)))) ∧
      Frame before (selectedPointerResult before base source level) base n k ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have run:=selectedPointerCode_execute input before base source level values header fresh hsource hlevel
  have safePrefixes:=selectedPointer_prefix_safe input before base source level budget values header fresh hsource hlevel safe addressBits targetBits pcBits
  obtain ⟨trace,head,last,chain,cost,invariant⟩:=PDCompute.Pack.linearExecute_trace_invariant program input selectedPointerCode selectedPointerCode_straight before _ fetch run
    (fun state=>HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bound state executed
      exact ⟨selectedPointerCode_prefix_memory input before state base source level values header fresh hsource hlevel count bound executed,safePrefixes count state executed⟩)
  exact ⟨trace,head,last,chain,cost,selectedPointerResult_header before base source level values header,selectedPointerResult_frame before base source level n k,invariant⟩

end PDCompute.NatControl
