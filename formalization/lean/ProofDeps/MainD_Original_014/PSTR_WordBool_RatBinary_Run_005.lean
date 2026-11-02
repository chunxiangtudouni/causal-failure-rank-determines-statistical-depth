module

public import PSTR_WordBool_RatBinary_Resources_004

/-! Same-path instruction assembly. The Raw contract is an internal
assembler parameter; the next leaf discharges it with each of the four
already-frozen concrete callees, before all operand quantifiers. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatBinary

open Turing PSTRWordVM RationalControllerComputation

universe u
variable {C : Type u} {states : Nat}

structure Facts (machine : Machine states) (coefficient : Nat) (operation : Rat→Rat→Rat)
    (background : RatInput.Stack→List Bool) (context : C) (oldX oldY : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (nativeMemory : BoolOnStacks.Store states)
    (readerMemory : RatOutput.Store) (x y : Rat) (tail scratch : List Bool)
    (trace : List (State C states)) (final : State C states) : Prop where
  first : trace.head?=some (entry background context oldX oldY memory formatter nativeMemory readerMemory x y tail scratch)
  chain : trace.IsChain (fun a b=>TM2.step (program machine .halt) a=some b)
  last : trace.getLast?=some final
  active : final.l=some .done
  context_eq : final.var.1.1.1.1.1=context
  contents : final.stk=RatPair.Link.finalContents background (RatPair.packet (operation x y) tail) scratch []
  count : trace.length≤time coefficient background x y tail scratch
  boundaries : ∀ current∈trace,
    RatInput.occupied current.stk≤space coefficient background x y tail scratch ∧
    (∀ slot,(current.stk slot).length≤space coefficient background x y tail scratch) ∧
    ∀ slot,¬RatPair.Link.Work slot→current.stk slot=background slot
  internal : ∀ current∈trace,∀ point,current.l=some point→
    (∀ node∈AuxWorkspace.nodes (program machine .halt point) current.var current.stk,
      (∀ slot,(node.2 slot).length≤space coefficient background x y tail scratch+32) ∧
      ∀ slot,¬RatPair.Link.Work slot→node.2 slot=background slot) ∧
    ScannerStatement.clock (program machine .halt point) current.var current.stk≤
      64*(space coefficient background x y tail scratch+33)
  proper : ∀ current∈trace.dropLast,current.l≠some .done

theorem actual_binary (machine : Machine states) (coefficient : Nat) (operation : Rat→Rat→Rat)
    (realCall : RatMulDiv.CalleeClaims.{u} machine coefficient 4 operation)
    (background : RatInput.Stack→List Bool) (context : C) (oldX oldY : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (nativeMemory : BoolOnStacks.Store states)
    (readerMemory : RatOutput.Store) (x y : Rat) (tail scratch : List Bool) :
    ∃ (trace : List (State C states)) (final : State C states),
      Facts machine coefficient operation background context oldX oldY memory formatter nativeMemory readerMemory x y tail scratch trace final := by
  let P:=RatPair.space background x y tail scratch
  let W:=space coefficient background x y tail scratch
  have wValue : W=16*P+rawBound coefficient background x y tail scratch+8:=rfl
  obtain ⟨pPath,pFinal,pFacts⟩:=RatPair.actual_pair .halt background ((context,nativeMemory),readerMemory)
    oldX oldY memory formatter x y tail scratch
  rcases RatPair.final_stacks pFacts with ⟨pRight,pLeft,pScratch,pSource,p3,_p4,_p5,_p6,_p8,_p9,_p12⟩
  let rawContext:RatPair.Store C:=(pairStoreMap C states pFinal.var).1.1
  let rawNative:BoolOnStacks.Store states:=(pairStoreMap C states pFinal.var).1.2
  let rawReader:RatOutput.Store:=(pairStoreMap C states pFinal.var).2
  let rawInput:=encode [.rational x,.rational y]
  let rawBudget:=coefficient*(rawInput.length+1)^4
  obtain ⟨nPath,nFinal,nFacts,_nNodes,_nSyntax⟩:=
    realCall (RatPair.Store C) .halt rawContext rawReader rawNative pFinal.stk x y
  have shared1:=pair_to_arith pFinal rawInput pFacts.active pRight pLeft
  have nativeSource : nFinal.stk 15=RatDrop.source (operation x y) x y tail := by
    rw [nFacts.output,pSource]
    exact output_source (operation x y) x y tail
  have nativeEmpty : nFinal.stk 3=[]:=
    (nFacts.frame 3 (by decide) (by decide) (by decide)).trans p3
  obtain ⟨dPath,dFirst,dChain,dLast,dTime,dBounds,_dNodes,_dProper⟩:=
    RatDrop.actual_drop nFinal.stk nFinal.var.1 nFinal.var.2 (operation x y) x y tail
  let dFinal:=RatDrop.state nFinal.stk 10 nFinal.var.1 (false,false) (RatInput.Encoder.packet (operation x y) tail) []
  have shared2:=arith_to_drop nFinal (operation x y) x y tail nFacts.active nativeSource nativeEmpty
  have pairLift:=pair_path machine (.halt:Statement C states) pPath _ _ pFacts.first pFacts.chain pFacts.last pFacts.active
  have arithLift:=arith_path machine (.halt:Statement C states) nPath _ _ nFacts.first nFacts.chain nFacts.last nFacts.active
  have dropLift:=drop_path machine (.halt:Statement C states) dPath _ dFinal dFirst dChain dLast rfl
  let front:=pPath.map pairConfiguration
  let middle:=nPath.map arithConfiguration
  let back:=dPath.map dropConfiguration
  let port1:=pairConfiguration pFinal
  let port2:=arithConfiguration nFinal
  let final:=dropConfiguration dFinal
  have frontLast : front.getLast?=some port1:=pairLift.2.2
  have middleFirst : middle.head?=some port1:=arithLift.1.trans (congrArg some shared1)
  have middleLast : middle.getLast?=some port2:=arithLift.2.2
  have backFirst : back.head?=some port2:=dropLift.1.trans (congrArg some shared2)
  have shapeMiddle : port1::middle.tail=middle:=by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp middleFirst
    rw [same];rfl
  have shapeBack : port2::back.tail=back:=by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp backFirst
    rw [same];rfl
  have firstHalfLast : (front++middle.tail).getLast?=some port2:=
    (NativeTrace.join_last _ _ _ frontLast).trans (shapeMiddle.symm ▸ middleLast)
  have firstHalfChain : (front++middle.tail).IsChain (fun a b=>TM2.step (program machine .halt) a=some b):=
    NativeTrace.join_chain _ _ _ frontLast pairLift.2.1 (shapeMiddle.symm ▸ arithLift.2.1)
  have last : (front++middle.tail++back.tail).getLast?=some final:=
    (NativeTrace.join_last _ _ _ firstHalfLast).trans (shapeBack.symm ▸ dropLift.2.2)
  have chain : (front++middle.tail++back.tail).IsChain (fun a b=>TM2.step (program machine .halt) a=some b):=
    NativeTrace.join_chain _ _ _ firstHalfLast firstHalfChain (shapeBack.symm ▸ dropLift.2.1)
  have active : final.l=some .done:=rfl
  have rawCap : rawBudget≤rawBound coefficient background x y tail scratch:=
    raw_input_bound coefficient background pFinal.stk x y tail scratch pRight
      (pFacts.boundaries pFinal (List.mem_of_getLast? pFacts.last)).2.1
  have nativeBudget : RatMulDiv.budget pFinal.stk rawBudget+8≤W := by
    have outside:=outside_native_le pFinal.stk
    have mass:=(pFacts.boundaries pFinal (List.mem_of_getLast? pFacts.last)).2.1
    change IsolatedRat.outside pFinal.stk+rawBudget+8≤W
    change RatInput.occupied pFinal.stk≤16*P at mass
    omega
  have nativeMass : RatInput.occupied nFinal.stk≤W:=
    ((nFacts.boundaries nFinal (List.mem_of_getLast? nFacts.last)).2.2).trans nativeBudget
  have dropBudget : RatDrop.budget nFinal.stk (operation x y) x y tail≤W:=
    (drop_mass nFinal.stk (operation x y) x y tail nativeSource nativeEmpty).trans_le nativeMass
  have resultSize : RatInput.Encoder.fieldSize (operation x y)≤W:=
    (result_field_bound nFinal.stk (operation x y) (pFinal.stk 15) nFacts.output).trans nativeMass
  have finalOutput : final.stk=RatPair.Link.finalContents background (RatPair.packet (operation x y) tail) scratch [] :=
    final_contents background pFinal.stk nFinal.stk (RatPair.input x y tail) scratch rawInput
      (RatPair.packet (operation x y) tail) pFacts.contents nFacts.right nFacts.left nFacts.frame
  have pairContext : rawContext.1.1.1=context:=
    congrArg (fun value : ((C×BoolOnStacks.Store states)×RatOutput.Store)×Bool×Bool=>value.1.1.1) pFacts.context_eq
  have finalContext : final.var.1.1.1.1.1=context:=
    (congrArg (fun value : RatPair.Store C=>value.1.1.1) nFacts.context_eq).trans pairContext
  have allBounds : ∀ current∈front++middle.tail++back.tail,
      RatInput.occupied current.stk≤W ∧ (∀ slot,(current.stk slot).length≤W) ∧
      ∀ slot,¬RatPair.Link.Work slot→current.stk slot=background slot := by
    intro current member
    rcases List.mem_append.mp member with early|late
    · rcases List.mem_append.mp early with firstPart|secondPart
      · obtain ⟨old,oldMember,rfl⟩:=List.mem_map.mp firstPart
        have bounds:=pFacts.boundaries old oldMember
        have mass : RatInput.occupied old.stk≤W:=bounds.2.1.trans (by change 16*P≤W;omega)
        exact ⟨mass,fun slot=>(RatInput.Encoder.point_mass old.stk slot).trans mass,bounds.2.2⟩
      · obtain ⟨old,oldMember,rfl⟩:=List.mem_map.mp (List.mem_of_mem_tail secondPart)
        have bounds:=nFacts.boundaries old oldMember
        have mass : RatInput.occupied old.stk≤W:=bounds.2.2.trans nativeBudget
        refine ⟨mass,fun slot=>(RatInput.Encoder.point_mass old.stk slot).trans mass,?_⟩
        intro slot untouched
        have noWork:=nonwork slot untouched
        exact (bounds.2.1 slot noWork.1 noWork.2.1 noWork.2.2.1 noWork.2.2.2.1).trans
          (RatPair.final_frame pFacts slot untouched)
    · obtain ⟨old,oldMember,rfl⟩:=List.mem_map.mp (List.mem_of_mem_tail late)
      have bounds:=dBounds old oldMember
      have mass : RatInput.occupied old.stk≤W:=bounds.1.2.2.trans dropBudget
      refine ⟨mass,fun slot=>(RatInput.Encoder.point_mass old.stk slot).trans mass,?_⟩
      intro slot untouched
      have noWork:=nonwork slot untouched
      exact ((bounds.1.2.1 slot noWork.2.2.2.1 noWork.2.2.2.2).trans
        (nFacts.frame slot noWork.1 noWork.2.1 noWork.2.2.2.1)).trans (RatPair.final_frame pFacts slot untouched)
  have count : (front++middle.tail++back.tail).length≤time coefficient background x y tail scratch := by
    have pTime:=pFacts.time
    have nTime:=nFacts.time
    have sizes:=fieldSize_eq x y
    have pairLen : front.length≤8*RatPair.fieldSize x y+80 := by
      simpa only [front,List.length_map] using pTime
    have lenFront : front.length=pPath.length:=List.length_map _
    have lenMiddle : middle.length=nPath.length:=List.length_map _
    have lenBack : back.length=dPath.length:=List.length_map _
    have arithBudget : RatMulDiv.budget pFinal.stk rawBudget≤16*P+rawBound coefficient background x y tail scratch := by
      have mass := (pFacts.boundaries pFinal (List.mem_of_getLast? pFacts.last)).2.1
      have outside := outside_native_le pFinal.stk
      dsimp only [RatMulDiv.budget,rawBudget]
      dsimp only [P]
      omega
    have arithTime : nPath.length≤4*(16*P+rawBound coefficient background x y tail scratch)+20 := by
      have t:=nFacts.time
      change nPath.length≤4*RatMulDiv.budget pFinal.stk rawBudget+20 at t
      omega
    have arithLen : middle.tail.length≤4*(16*P+rawBound coefficient background x y tail scratch)+20 := by
      have tailLen := congrArg List.length shapeMiddle
      simp only [List.length_cons] at tailLen
      omega
    have dropLen : back.tail.length≤3*RatInput.Encoder.fieldSize (operation x y)+
        RatInput.Encoder.fieldSize x+RatInput.Encoder.fieldSize y+17 := by
      have tailLen := congrArg List.length shapeBack
      simp only [List.length_cons] at tailLen
      change dPath.length≤3*RatInput.Encoder.fieldSize (operation x y)+
        RatInput.Encoder.fieldSize x+RatInput.Encoder.fieldSize y+17 at dTime
      omega
    dsimp only [time]
    change (front++middle.tail++back.tail).length≤9*RatPair.fieldSize x y+7*W+128
    simp only [List.length_append]
    have resultSmall : RatInput.Encoder.fieldSize (operation x y)≤W:=resultSize
    omega
  refine ⟨front++middle.tail++back.tail,final,{
    first:=by rw [List.head?_append,List.head?_append,pairLift.1];rfl
    chain:=chain,last:=last,active:=active,context_eq:=finalContext,contents:=finalOutput,count:=count
    boundaries:=allBounds
    internal:=by
      intro current member point selected
      exact internal_bound machine background current W (allBounds current member).1 (allBounds current member).2.2 point
    proper:=NativeMulLink.no_early_halt_port (program machine .halt) .done rfl _ _ chain last active }⟩

end PaperProofs.Common.Native.PSTRWordBool.RatBinary
