module

public import RootB234_PrepEntry_NatRun_001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.Alpha

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMWordFrontCode213 PSTRTMWordPreparationFront214
open B23_4_RatWordPrep

abbrev NativeMemory := BoolOnStacks.Store 19
abbrev Store (C : Type*) := C × NativeMemory
abbrev Statement (C : Type*) := VirtualReturn.Statement C NativeMemory
abbrev State (C : Type*) := VirtualReturn.State C NativeMemory

def source : Unit → VirtualReturn.SmallStatement NativeMemory := VirtualBool.source alphaMachine

def program {C : Type*} (caller : Statement C) : Fin 2 → Statement C := VirtualReturn.program source caller

variable {C : Type*}

def nextLeft (left : List Bool) (number : Nat) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::left)

private theorem transported (context : C) (memory : NativeMemory) (bank : RatInput.Stack → List Bool)
    (oldStart oldFinal : MachineState 19) (oldTrace : List (MachineState 19))
    (represented : BoolOnStacks.representedState
      (⟨some (),memory,fun slot => bank (VirtualReturn.role slot)⟩ : BoolOnStacks.State 19)=oldStart)
    (first : oldTrace.head?=some oldStart)
    (chain : oldTrace.IsChain (fun a b => TM0.step alphaMachine a=some b))
    (last : oldTrace.getLast?=some oldFinal) (halt : TM0.step alphaMachine oldFinal=none) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (⟨some 0,(context,memory),bank⟩ : State C) ∧
      trace.IsChain (fun a b => TM2.step (program .halt) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some 1 ∧
      VirtualBool.representedState final=oldFinal ∧
      trace.length=oldTrace.length+1 ∧ final.var.1=context ∧
      ∀ current∈trace,current.var.1=context ∧
        ∀ slot,slot≠0→slot≠1→current.stk slot=bank slot := by
  obtain ⟨rest,shape⟩:=List.head?_eq_some_iff.mp first
  rw [shape] at chain last
  let start : BoolOnStacks.State 19:=⟨some (),memory,fun slot => bank (VirtualReturn.role slot)⟩
  obtain ⟨posts,beforeHalt,length,sourceChain,sourceLast,live,representation⟩:=
    BoolStackTrace.lift_path alphaMachine start oldStart oldFinal rest rfl represented chain last
  have actualHalt : TM0.step alphaMachine (BoolOnStacks.representedState beforeHalt)=none := by
    rw [representation]
    exact halt
  obtain ⟨smallFinal,haltEdge,done,unchanged⟩:=BoolStackTrace.terminate alphaMachine beforeHalt live actualHalt
  have pair : (beforeHalt::[smallFinal]).IsChain
      (fun a b => TM2.step (BoolOnStacks.program alphaMachine) a=some b) :=
    List.isChain_cons_cons.mpr ⟨haltEdge,List.isChain_singleton _⟩
  let smallRun:=(start::posts)++[smallFinal]
  have smallFirst : smallRun.head?=some start := rfl
  have smallChain:=NativeTrace.join_chain _ _ _ sourceLast sourceChain pair
  have smallLast : smallRun.getLast?=some smallFinal:=List.getLast?_append_cons _ _ []
  have smallCount : smallRun.length=oldTrace.length+1 := by
    simp only [smallRun,shape,List.length_append,List.length_cons,List.length_nil,length]
  have mapped:=VirtualReturn.path_configuration source .halt context bank smallRun start smallFinal
    smallFirst smallChain smallLast
  have rebuild : VirtualReturn.configuration context bank start=(⟨some 0,(context,memory),bank⟩ : State C) := by
    change (⟨some 0,(context,memory),_⟩ : State C)=⟨some 0,(context,memory),bank⟩
    congr 1
    funext slot
    fin_cases slot <;> rfl
  refine ⟨smallRun.map (VirtualReturn.configuration context bank),
    VirtualReturn.configuration context bank smallFinal,mapped.1.trans (congrArg some rebuild),
    mapped.2.1,mapped.2.2.1,VirtualReturn.returned context bank smallFinal done,?_,
    mapped.2.2.2.1.trans smallCount,rfl,mapped.2.2.2.2⟩
  exact (VirtualBool.represented_configuration context bank smallFinal).trans (unchanged.trans representation)

/-- Only the frozen natural-tag/17-state parser is reused. The initial
finite memory is the caller's real allocated block, never a host packet. -/
theorem actual {C : Type*} (context : C) (memory : NativeMemory) (bank : RatInput.Stack → List Bool)
    (left : List Bool) (number : Nat) (suffix : List Bool) (control : memory.1=0)
    (physical : Tape.mk' (ListBlank.mk (bank 1)) (ListBlank.mk (bank 0))=
      Tape.mk₂ left (false::(encodeNat number++suffix))) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (⟨some 0,(context,memory),bank⟩ : State C) ∧
      trace.IsChain (fun a b => TM2.step (program .halt) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some 1 ∧
      Tape.mk' (ListBlank.mk (final.stk 1)) (ListBlank.mk (final.stk 0))=
        Tape.mk₂ (nextLeft left number) suffix ∧
      trace.length=(PSTRTMNatValue017.rawPayload number).length^2+
        9*(PSTRTMNatValue017.rawPayload number).length+5 ∧
      final.var.1=context ∧
      ∀ current∈trace,current.var.1=context ∧
        ∀ slot,slot≠0→slot≠1→current.stk slot=bank slot := by
  have old:=alpha_runsFrom left number suffix
  have represented : BoolOnStacks.representedState
      (⟨some (),memory,fun slot => bank (VirtualReturn.role slot)⟩ : BoolOnStacks.State 19)=
      (⟨0,Tape.mk₂ left (false::(encodeNat number++suffix))⟩ : MachineState 19) := by
    change (⟨memory.1,Tape.mk' (ListBlank.mk (bank 1)) (ListBlank.mk (bank 0))⟩ : MachineState 19)=_
    rw [control,physical]
  obtain ⟨trace,final,first,chain,last,active,representedFinal,count,contextEq,frames⟩:=
    transported context memory bank _ _ _ represented old.1 old.2.1 old.2.2.1 old.2.2.2
  refine ⟨trace,final,first,chain,last,active,?_,?_,contextEq,frames⟩
  · exact congrArg TM0.Cfg.Tape representedFinal
  · rw [count]
    simp only [alphaTrace,tagTrace,List.length_append,List.length_map,List.length_cons,List.length_nil,
      PA17TMRatArithmeticParse002.streamTrace_length]
    omega

theorem count_marker_tail (left : List Bool) (count : Nat) : ∃ tail,headerLeft left count=false::true::tail := by
  cases shape : (PSTRTMNatValue017.rawPayload count).reverse with
  | nil =>
    have reversed:=congrArg List.reverse shape
    simp only [List.reverse_reverse,List.reverse_nil] at reversed
    exact False.elim (PSTRSymbolicLaneArchive.rawPayload_nonempty count reversed)
  | cons bit later =>
    refine ⟨bit::(PSTRTMRawNat010.leftBlocks later++left),?_⟩
    rw [headerLeft,shape]
    rfl

theorem finite_archive_tail (left : List Bool) (count number : Nat) (bank : RatInput.Stack → List Bool)
    (wholeLeft : ListBlank.mk (bank 1)=ListBlank.mk (fieldLeft left count number)) :
    ∃ tail,bank 1=false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::tail) := by
  obtain ⟨countTail,marker⟩:=count_marker_tail left count
  rw [fieldLeft,marker] at wholeLeft
  let marked:=false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++[false,false])
  obtain ⟨tail,shape⟩:=PSTRSymbolicNaturalExport.finite_marked_prefix marked countTail (bank 1)
    (by simpa only [marked,List.cons_append,List.append_assoc,List.nil_append] using wholeLeft)
  refine ⟨false::true::tail,?_⟩
  simpa only [marked,List.cons_append,List.append_assoc,List.nil_append] using shape

end RootB234.PrepEntry.Alpha
