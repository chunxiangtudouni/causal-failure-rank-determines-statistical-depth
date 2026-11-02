module

public import RootB234_PrepEntry_NatPacketCode_078

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.NatPacket

open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep PSTRTMRawNat010

variable {C : Type*}

theorem packet_append (number : Nat) (tail : List Bool) :
    NatField.packet number tail=NatField.packet number []++tail := by
  simp only [NatField.packet,List.append_assoc,List.cons_append,List.nil_append]

private theorem leftBlocks_length (bits : List Bool) : (leftBlocks bits).length=2*bits.length := by
  induction bits with
  | nil => rfl
  | cons bit later ih =>
    simp only [leftBlocks,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at ih ⊢
    omega

theorem packet_length (number : Nat) (tail : List Bool) :
    (NatField.packet number tail).length=2*(PSTRTMNatValue017.rawPayload number).length+2+tail.length := by
  simp only [NatField.packet,List.length_append,leftBlocks_length,List.length_cons]
  omega

structure Path (copy : Bool) (caller : Statement C) (before final : State C) (bound : Nat) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program copy caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length≤bound

def Path.append {copy : Bool} {caller : Statement C} {before middle final : State C} {a b : Nat}
    (front : Path copy caller before middle a) (back : Path copy caller middle final b) : Path copy caller before final (a+b) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.first
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.first]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have first:=front.count
    have second:=back.count
    simp only [List.length_append,List.length_tail]
    omega

private theorem reverse_points (copy : Bool) (background : RatInput.Stack → List Bool) (context : C)
    (word : List Bool) (memory : RatOutput.Store) (source target : List Bool) :
    ∀ current∈RootB234.RatPacketTransport.reverseTrace copy background context word memory source target,
      current.l=some 3 ∨ current.l=some 4 := by
  induction word generalizing memory source target with
  | nil =>
    intro current member
    rcases List.mem_cons.mp member with rfl|later
    · exact Or.inl rfl
    · have same:=List.mem_singleton.mp later
      subst current
      exact Or.inr rfl
  | cons bit later ih =>
    intro current member
    rw [RootB234.RatPacketTransport.reverseTrace,List.mem_cons] at member
    rcases member with rfl|member
    · exact Or.inl rfl
    · exact ih (true,bit) (if copy then bit::source else source) (bit::target) current member

/-- The original parser trace followed by the original arbitrary-word
reverse trace. The new source supplies neither a width nor a cursor/fuel,
and does not synthesize the result packet in a host register. -/
theorem actual (copy : Bool) (caller : Statement C) (background : RatInput.Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (number : Nat) (source target : List Bool) :
    ∃ _run : Path copy caller (entry background context memory number source target)
      (finalState copy background context number source target)
      (3*(PSTRTMNatValue017.rawPayload number).length+6), True := by
  let digits:=PSTRTMNatValue017.rawPayload number
  let old:=RootB234.RatPacketTransport.oldBackground background target
  let oldRun:=RatDrop.fieldTrace true old context 1 2 digits memory source []
  let parsed:=oldRun.map (StackIso.configuration RootB234.RatPacketTransport.roles)
  let word:=RatDrop.fieldCopied true digits []
  let pStart:=RootB234.RatPacketTransport.state background 1 context memory (NatField.packet number source) [] target
  let pFinal:=RootB234.RatPacketTransport.state background 2 context (true,false) source word target
  have pFirst : parsed.head?=some pStart := by
    simp only [parsed,oldRun,List.head?_map,RatDrop.field_head,Option.map_some,old,
      RootB234.RatPacketTransport.renamed_state]
    rfl
  have pLast : parsed.getLast?=some pFinal := by
    simp only [parsed,oldRun,List.getLast?_map,RatDrop.field_last,Option.map_some,old,
      RootB234.RatPacketTransport.renamed_state]
    rfl
  have pChain:=RootB234.RatPacketTransport.field_chain copy (.halt : RootB234.RatPacketTransport.Statement C)
    old context 1 2 (by decide) rfl digits memory source []
  have pMap:=LabelMap.actual_path_on fieldLabel (RootB234.RatPacketTransport.program copy .halt) (program copy caller)
    parsed pStart pFinal pFirst pChain pLast (by
      intro current member point selected
      change current∈(oldRun.map (StackIso.configuration RootB234.RatPacketTransport.roles)).dropLast at member
      rw [←List.map_dropLast] at member
      obtain ⟨original,present,rfl⟩:=List.mem_map.mp member
      have atField:=RootB234.RatPacketTransport.field_proper old context 1 2 digits memory source [] original present
      change original.l=some point at selected
      have same : point=1 := Option.some.inj (selected.symm.trans atField)
      subst point
      rfl)
  let front : Path copy caller (entry background context memory number source target) (fieldCfg pFinal) (digits.length+2):=
    ⟨parsed.map (LabelMap.configuration fieldLabel),pMap.1,pMap.2.1,pMap.2.2.1,by
      simp only [parsed,oldRun,List.length_map,RatDrop.field_length]
      rfl⟩
  have wordEq : word=(NatField.packet number []).reverse := by
    simp only [word,RatDrop.fieldCopied,ite_true,List.append_nil,NatField.packet,digits]
  let rStart:=RootB234.RatPacketTransport.state background 3 context (true,false) source word target
  let rFinal:=RootB234.RatPacketTransport.state background 4 context (false,false)
    (if copy then NatField.packet number source else source) [] (NatField.packet number target)
  let reversed:=RootB234.RatPacketTransport.reverseTrace copy background context word (true,false) source target
  have rFirst : reversed.head?=some rStart := RootB234.RatPacketTransport.reverse_head _ _ _ _ _ _ _
  have rLast : reversed.getLast?=some rFinal := by
    rw [RootB234.RatPacketTransport.reverse_last]
    simp only [wordEq,List.reverse_reverse,←packet_append]
    rfl
  have rChain:=RootB234.RatPacketTransport.reverse_chain copy (.halt : RootB234.RatPacketTransport.Statement C)
    background context word (true,false) source target
  have proper:=NativeMulLink.no_early_halt_port (RootB234.RatPacketTransport.program copy (C := C) .halt) 4 rfl
    reversed rFinal rChain rLast rfl
  have rMap:=LabelMap.actual_path_on reverseLabel (RootB234.RatPacketTransport.program copy .halt) (program copy caller)
    reversed rStart rFinal rFirst rChain rLast (by
      intro current member point selected
      rcases reverse_points copy background context word (true,false) source target current (List.mem_of_mem_dropLast member) with atThree|atFour
      · have same : point=3 := Option.some.inj (selected.symm.trans atThree)
        subst point
        rfl
      · exact False.elim (proper current member atFour))
  have join : reverseCfg rStart=fieldCfg pFinal := rfl
  let back : Path copy caller (fieldCfg pFinal) (finalState copy background context number source target)
      (2*digits.length+4):=
    ⟨reversed.map (LabelMap.configuration reverseLabel),rMap.1.trans (congrArg some join),rMap.2.1,rMap.2.2.1,by
      rw [List.length_map,RootB234.RatPacketTransport.reverse_length,wordEq,List.length_reverse,packet_length]
      simp only [List.length_nil]
      dsimp only [digits]
      omega⟩
  let whole:=front.append back
  let run : Path copy caller (entry background context memory number source target)
      (finalState copy background context number source target) (3*digits.length+6):=
    ⟨whole.trace,whole.first,whole.chain,whole.last,by have count:=whole.count;omega⟩
  exact ⟨run,trivial⟩

end RootB234.PrepEntry.NatPacket
