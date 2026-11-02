module

public import B23_4_RatWordPrep_SeqCmp_NatFieldCurrent_052
public import RootB234_RatPacketTransport_Public005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.NatPacketMove

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMRawNat010

abbrev Label := RootB234.RatPacketTransport.Label
abbrev Store (C : Type*) := RootB234.RatPacketTransport.Store C
abbrev Statement (C : Type*) := RootB234.RatPacketTransport.Statement C
abbrev State (C : Type*) := RootB234.RatPacketTransport.State C

variable {C : Type*}

def cells (digits tail : List Bool) : List Bool := leftBlocks digits++false::false::tail

theorem cells_append (digits tail : List Bool) : cells digits tail=cells digits []++tail := by
  simp [cells,List.append_assoc]

/-- Reuse the existing true field parser at its literal2 port, followed by
its actual temporary4 reverse loop. No new parsing loop or host width. -/
def actual_fields (copy : Bool) (caller : Statement C) (background : RatInput.Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (digits source target : List Bool) :
    RootB234.RatPacketTransport.Path (RootB234.RatPacketTransport.program copy caller)
      (RootB234.RatPacketTransport.state background 2 context memory (cells digits source) [] target)
      (RootB234.RatPacketTransport.state background 4 context (false,false)
        (if copy then cells digits source else source) [] (cells digits target)) (3*digits.length+6) := by
  let old:=RootB234.RatPacketTransport.oldBackground background target
  let word:=(cells digits []).reverse
  let parsed:=(RatDrop.fieldTrace true old context 2 3 digits memory source []).map
    (StackIso.configuration RootB234.RatPacketTransport.roles)
  have front : RootB234.RatPacketTransport.Path (RootB234.RatPacketTransport.program copy caller)
      (RootB234.RatPacketTransport.state background 2 context memory (cells digits source) [] target)
      (RootB234.RatPacketTransport.state background 3 context (true,false) source word target) (digits.length+2) :=
    ⟨parsed,by
      simp only [parsed,List.head?_map,RatDrop.field_head,Option.map_some,old,RootB234.RatPacketTransport.renamed_state]
      rfl,
      RootB234.RatPacketTransport.field_chain copy caller old context 2 3 (by decide) rfl digits memory source [],by
      simp only [parsed,List.getLast?_map,RatDrop.field_last,Option.map_some,old,RootB234.RatPacketTransport.renamed_state]
      simp only [RatDrop.fieldCopied,ite_true,List.append_nil]
      rfl,
      by simp only [parsed,List.length_map,RatDrop.field_length]; rfl⟩
  let reversed:=RootB234.RatPacketTransport.reverseTrace copy background context word (true,false) source target
  have back : RootB234.RatPacketTransport.Path (RootB234.RatPacketTransport.program copy caller)
      (RootB234.RatPacketTransport.state background 3 context (true,false) source word target)
      (RootB234.RatPacketTransport.state background 4 context (false,false)
        (if copy then cells digits source else source) [] (cells digits target)) (word.length+2) :=
    ⟨reversed,RootB234.RatPacketTransport.reverse_head _ _ _ _ _ _ _,
      RootB234.RatPacketTransport.reverse_chain _ _ _ _ _ _ _ _,by
      rw [RootB234.RatPacketTransport.reverse_last]
      simp only [word,List.reverse_reverse,←cells_append],
      by rw [RootB234.RatPacketTransport.reverse_length]⟩
  have result:=front.trans back
  have size : word.length=2*digits.length+2 := by
    simp only [word,List.length_reverse,cells,List.length_append,List.length_cons,List.length_nil,
      PSTRSymbolicRatExport.flagged_length]
  exact result.weaken (by rw [size]; omega)

theorem actual (copy : Bool) (caller : Statement C) (background : RatInput.Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (number : Nat) (source target : List Bool) :
    ∃ run : List (State C),
      run.head?=some (RootB234.RatPacketTransport.state background 2 context memory (NatField.packet number source) [] target) ∧
      run.IsChain (fun a b => TM2.step (RootB234.RatPacketTransport.program copy caller) a=some b) ∧
      run.getLast?=some (RootB234.RatPacketTransport.state background 4 context (false,false)
        (if copy then NatField.packet number source else source) [] (NatField.packet number target)) ∧
      run.length ≤ 3*(PSTRTMNatValue017.rawPayload number).length+6 := by
  let path:=actual_fields copy caller background context memory (PSTRTMNatValue017.rawPayload number) source target
  exact ⟨path.trace,path.head,path.chain,path.tail,path.time⟩

end B23_4_RatWordPrep.NatPacketMove
