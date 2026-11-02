module

public import PSTR_WordBool_RatCmp_Link_001

/-! ALL signed x,y: actual frozen subtraction, then real packet reading
and a real physical push on3. All witnesses belong to one joined trace. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatCmp.Link

open Turing PSTRWordVM RationalControllerComputation PA17TMRatArithmeticParse002

variable {C : Type*}

theorem actual_path (caller : Statement C) (context : C) (flags : Reader.Store)
    (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store states)
    (background : Stack → List Bool) (x y : Rat) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry context flags readerMemory nativeMemory background x y) ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some done ∧ final.var.1.1.1=context ∧
      final.stk 13=[] ∧ final.stk 14=[] ∧ final.stk 7=background 7 ∧ final.stk 15=background 15 ∧
      final.stk 3=decide (x≤y)::background 3 ∧
      (∀ slot,slot≠3→slot≠13→slot≠14→slot≠15→final.stk slot=background slot) ∧
      trace.length≤6*baseBudget background x y+64 ∧
      (∀ current∈trace,current.var.1.1.1=context) ∧
      RatOutput.occupied (entry context flags readerMemory nativeMemory background x y).stk≤baseBudget background x y+8 := by
  obtain ⟨subTrace,subFinal,facts,_oldInternal,_oldSyntax⟩:=
    RatAddSub.actual_sub (.halt : RatOutput.Link.Statement (C × Reader.Store) states)
      (context,flags) readerMemory nativeMemory background x y
  have old3 : subFinal.stk 3=background 3:=facts.frame 3 (by decide) (by decide) (by decide)
  let base:=((exchange C).symm subFinal.var).1
  let initialFlags:=((exchange C).symm subFinal.var).2
  let readBefore:=Reader.state subFinal.stk 0 base initialFlags
    (PSTRSymbolicRatExport.packet (sign (x-y)) (numeratorDigits (x-y)) (denominatorDigits (x-y)) (background 15))
    (background 3)
  let readFinal:=Reader.state subFinal.stk 4 base (sign (x-y),Reader.anyTrue (numeratorDigits (x-y)),false)
    (background 15) ((sign (x-y) || !Reader.anyTrue (numeratorDigits (x-y)))::background 3)
  obtain ⟨reader,rFirst,rChain,rLast,rCount,rContexts⟩:=Reader.actual_packet .halt subFinal.stk base initialFlags
    (sign (x-y)) (numeratorDigits (x-y)) (denominatorDigits (x-y)) (background 15) (background 3)
  have rPath:=read_path caller reader readBefore readFinal rFirst rChain rLast rfl
  have sPath:=sub_path caller subTrace _ subFinal facts.first facts.chain facts.last facts.active
  have shared : readConfiguration readBefore=subConfiguration subFinal := by
    dsimp only [readBefore]
    rw [←facts.output,←old3]
    exact shared_configuration subFinal facts.active
  have shape : subConfiguration subFinal::(reader.map readConfiguration).tail=reader.map readConfiguration := by
    have head : (reader.map readConfiguration).head?=some (subConfiguration subFinal):=
      rPath.1.trans (congrArg some shared)
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp head
    rw [same];rfl
  let trace:=subTrace.map subConfiguration++(reader.map readConfiguration).tail
  let final:=readConfiguration readFinal
  have joined : trace.IsChain (fun a b=>TM2.step (program caller) a=some b):=
    NativeTrace.join_chain _ _ _ sPath.2.2 sPath.2.1 (shape.symm ▸ rPath.2.1)
  have last : trace.getLast?=some final:=
    (NativeTrace.join_last _ _ _ sPath.2.2).trans (shape.symm ▸ rPath.2.2)
  have finalContext : final.var.1.1.1=context := by
    change subFinal.var.1.1.1=context
    exact congrArg Prod.fst facts.context_eq
  have packetSize :
      (PSTRSymbolicRatExport.packet (sign (x-y)) (numeratorDigits (x-y)) (denominatorDigits (x-y)) (background 15)).length=
        2*((numeratorDigits (x-y)).length+(denominatorDigits (x-y)).length)+6+(background 15).length := by
    simp only [PSTRSymbolicRatExport.packet,List.length_cons,List.length_append,RatOutput.flagged_length]
    omega
  have packetMass:=RatOutput.Link.point_mass subFinal.stk 15
  rw [facts.output,packetSize] at packetMass
  have lastMass:=(facts.boundaries subFinal (List.mem_of_getLast? facts.last)).2.2
  change RatOutput.occupied subFinal.stk≤baseBudget background x y+8 at lastMass
  have oldTime:=facts.time
  change subTrace.length≤4*baseBudget background x y+20 at oldTime
  have time : trace.length≤6*baseBudget background x y+64 := by
    have tailLength : (reader.map readConfiguration).tail.length≤reader.length := by
      simp only [List.length_tail,List.length_map]
      omega
    dsimp only [trace]
    simp only [List.length_append,List.length_map]
    omega
  refine ⟨trace,final,?_,joined,last,rfl,finalContext,?_,?_,?_,rfl,?_,?_,time,?_,?_⟩
  · rw [List.head?_append,sPath.1]
    rfl
  · change subFinal.stk 13=[]
    exact facts.right
  · change subFinal.stk 14=[]
    exact facts.left
  · change subFinal.stk 7=background 7
    exact facts.counter
  · change (sign (x-y) || !Reader.anyTrue (numeratorDigits (x-y)))::background 3=decide (x≤y)::background 3
    simpa only [Reader.decision] using congrArg (fun bit=>bit::background 3) (Reader.decision_le x y)
  · intro slot not3 not13 not14 not15
    change Reader.cells subFinal.stk (background 15) _ slot=background slot
    simp only [Reader.cells,not3,not15,ite_false]
    exact facts.frame slot not13 not14 not15
  · intro current member
    rcases List.mem_append.mp member with early|later
    · obtain ⟨small,smallMember,rfl⟩:=List.mem_map.mp early
      exact congrArg Prod.fst (facts.boundaries small smallMember).1
    · obtain ⟨small,smallMember,rfl⟩:=List.mem_map.mp (List.mem_of_mem_tail later)
      have contextSame:=rContexts small smallMember
      change (exchange C (small.var)).1.1.1=context
      change small.var.1.1.1=context
      exact (congrArg (fun memory : Base C=>memory.1.1) contextSame).trans
        (congrArg Prod.fst facts.context_eq)
  · obtain ⟨rest,sourceShape⟩:=List.head?_eq_some_iff.mp facts.first
    let initialState:=RatOutput.Link.nativeConfiguration
      (IsolatedRat.entry ((context,flags),readerMemory) nativeMemory background (encode [.rational x,.rational y]))
    have member : initialState∈subTrace := by rw [sourceShape];exact List.mem_cons_self
    exact (facts.boundaries initialState member).2.2

end PaperProofs.Common.Native.PSTRWordBool.RatCmp.Link
