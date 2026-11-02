module

public import B23_4_RatWordPrep_SeqCmp_NatFieldRun_050

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.Header

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMWordFrontCode213 PSTRTMWordPreparationFront214

abbrev NativeMemory := BoolOnStacks.Store 37
abbrev Store (C : Type*) := C × NativeMemory
abbrev Statement (C : Type*) := VirtualReturn.Statement C NativeMemory
abbrev State (C : Type*) := VirtualReturn.State C NativeMemory

def source : Unit → VirtualReturn.SmallStatement NativeMemory := VirtualBool.source frontMachine

def program {C : Type*} (caller : Statement C) : Fin 2 → Statement C := VirtualReturn.program source caller

def entry {C : Type*} (context : C) (background : RatInput.Stack → List Bool) (bits : List Bool) : State C :=
  VirtualReturn.configuration context background
    (TM2.init (Γ := PushPop.Alphabet) (Λ := Unit) (σ := NativeMemory) 0 bits)

/-- The actual frozen original header parser, including its paid terminal
head push and active return. All original suffix cells remain on the Tape. -/
theorem actual {C : Type*} (context : C) (background : RatInput.Stack → List Bool)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (run : List (State C)) (final : State C),
      run.head?=some (entry context background (wordInput E target word)) ∧
      run.IsChain (fun before after => TM2.step (program .halt) before=some after) ∧
      run.getLast?=some final ∧ final.l=some 1 ∧
      (VirtualBool.representedState final).Tape=Tape.mk₂
        (fieldLeft [] (wordData E target word).length E.alphabetSize) (wordTail E target word) ∧
      run.length ≤ 16*((wordInput E target word).length+1)^2+1 ∧
      (∀ current∈run,current.var.1=context ∧ ∀ slot,slot≠0→slot≠1→current.stk slot=background slot) ∧
      ∀ current∈run,VirtualReturn.occupiedSlots current.stk ≤ VirtualReturn.outside background+
        64*((wordInput E target word).length+1)^2 := by
  have old:=word_front_runs E target word
  obtain ⟨run,final,first,chain,last,active,represented,_order,count,_context,frames,mass⟩:=
    VirtualBool.same_old_run frontMachine .halt context background (wordInput E target word)
      (frontTrace E target word) (frontFinal E target word) old.1 old.2.1 old.2.2.1 old.2.2.2.1
  have tape:=congrArg TM0.Cfg.Tape represented
  rw [word_front_final_tape] at tape
  have oldSpace : visitedSpace frontMachine (wordInput E target word).length (frontTrace E target word) ≤
      64*((wordInput E target word).length+1)^2 := by
    simpa only [List.take_length] using word_front_prefix_space_le E target word (frontTrace E target word).length
  refine ⟨run,final,first,chain,last,active,tape,?_,frames,?_⟩
  · rw [count]
    exact Nat.add_le_add_right (word_front_time_le E target word) 1
  · intro current member
    exact (mass current member).trans (Nat.add_le_add_left oldSpace _)

theorem count_marker (count : Nat) : ∃ tail,headerLeft [] count=false::true::tail := by
  cases shape : (PSTRTMNatValue017.rawPayload count).reverse with
  | nil =>
    have reversed:=congrArg List.reverse shape
    simp only [List.reverse_reverse,List.reverse_nil] at reversed
    exact False.elim (PSTRSymbolicLaneArchive.rawPayload_nonempty count reversed)
  | cons bit later =>
    refine ⟨bit::PSTRTMRawNat010.leftBlocks later,?_⟩
    rw [headerLeft,shape,List.append_nil]
    rfl

/-- The genuine TRUE in the parsed original count prevents ListBlank from
silently truncating the physical natural field's FALSE end guard. -/
theorem finite_archive (count number : Nat) (bank : RatInput.Stack → List Bool)
    (wholeLeft : ListBlank.mk (bank 1)=ListBlank.mk (fieldLeft [] count number)) :
    ∃ left,bank 1=false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::left) := by
  obtain ⟨countTail,marker⟩:=count_marker count
  rw [fieldLeft,marker] at wholeLeft
  let marked:=false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++[false,false])
  obtain ⟨tail,shape⟩:=PSTRSymbolicNaturalExport.finite_marked_prefix marked countTail (bank 1)
    (by simpa only [marked,List.cons_append,List.append_assoc,List.nil_append] using wholeLeft)
  refine ⟨false::true::tail,?_⟩
  simpa only [marked,List.cons_append,List.append_assoc,List.nil_append] using shape

end B23_4_RatWordPrep.Header
