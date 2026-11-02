module

public import B23_4_RatWordPrep_SeqCmp_NatFieldCode_049

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.NatField

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRSymbolicNaturalExport PSTRTMRawNat010

variable {C : Type*}

theorem restore_labels (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : RatInput.Stack → List Bool) :
    ∀ current∈PSTRSymbolicRatExport.restoreTrace context bit flag mode cells left scratch target background,
      current.l=some 3 ∨ current.l=some 4 := by
  intro current member
  rw [PSTRSymbolicRatExport.restoreTrace] at member
  obtain ⟨small,present,rfl⟩:=List.mem_map.mp member
  rcases PSTRSymbolicRatExport.old_restore_labels context bit flag mode cells left scratch target background small present with h | h
  · left
    change small.l.map PSTRSymbolicRatExport.restoreLabel=some 3
    rw [h]
    rfl
  · right
    change small.l.map PSTRSymbolicRatExport.restoreLabel=some 4
    rw [h]
    cases mode <;> rfl

theorem restore_chain (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : RatInput.Stack → List Bool) :
    (PSTRSymbolicRatExport.restoreTrace context bit flag mode cells left scratch target background).IsChain
      (fun before after => TM2.step (program .halt) before=some after) := by
  apply (PSTRSymbolicRatExport.restore_chain context bit flag mode cells left scratch target background).imp_of_mem_imp
  intro before after member _ edge
  have positions:=restore_labels context bit flag mode cells left scratch target background before member
  rcases positions with h | h
  · cases before with
    | mk position memory contents =>
      change position=some 3 at h
      subst position
      exact edge
  · cases before with
    | mk position memory contents =>
      change position=some 4 at h
      subst position
      exact edge

def fieldTrace (context : C) (bit flag mode : Bool) :
    List Bool → List Bool → List Bool → List Bool → List Bool → (RatInput.Stack → List Bool) → List (State C)
  | [], cells, left, scratch, target, background =>
      state (some 1) (context,(bit,flag,mode)) (false::left)
        (backups cells++true::scratch) target background ::
      PSTRSymbolicRatExport.restoreTrace context bit false mode (false::cells) left scratch target background
  | digit::later, cells, left, scratch, target, background =>
      state (some 1) (context,(bit,flag,mode)) (leftBlocks (digit::later)++false::left)
        (backups cells++true::scratch) target background ::
      fieldTrace context digit true mode later (digit::true::cells) left scratch (true::digit::target) background

theorem field_head (context : C) (bit flag mode : Bool)
    (digits cells left scratch target : List Bool) (background : RatInput.Stack → List Bool) :
    (fieldTrace context bit flag mode digits cells left scratch target background).head?=
      some (state (some 1) (context,(bit,flag,mode)) (leftBlocks digits++false::left)
        (backups cells++true::scratch) target background) := by
  cases digits <;> rfl

theorem field_nonempty (context : C) (bit flag mode : Bool)
    (digits cells left scratch target : List Bool) (background : RatInput.Stack → List Bool) :
    fieldTrace context bit flag mode digits cells left scratch target background≠[] := by
  cases digits <;> intro same <;> cases same

theorem field_length (context : C) (bit flag mode : Bool)
    (digits cells left scratch target : List Bool) (background : RatInput.Stack → List Bool) :
    (fieldTrace context bit flag mode digits cells left scratch target background).length=
      3*digits.length+cells.length+4 := by
  induction digits generalizing bit flag cells target with
  | nil => simp only [fieldTrace,List.length_cons,PSTRSymbolicRatExport.restore_length,List.length_nil]; omega
  | cons digit later ih => simp only [fieldTrace,List.length_cons,ih]; omega

theorem field_chain (context : C) (bit flag mode : Bool)
    (digits cells left scratch target : List Bool) (background : RatInput.Stack → List Bool) :
    (fieldTrace context bit flag mode digits cells left scratch target background).IsChain
      (fun before after => TM2.step (program .halt) before=some after) := by
  induction digits generalizing bit flag cells target with
  | nil =>
    apply List.isChain_cons.mpr
    refine ⟨?_,restore_chain context bit false mode (false::cells) left scratch target background⟩
    intro next member
    rw [PSTRSymbolicRatExport.restore_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    simpa only [backups,List.flatMap_cons,List.cons_append,List.nil_append] using
      end_step context bit flag mode left (backups cells++true::scratch) target background
  | cons digit later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih digit true (digit::true::cells) (true::digit::target)⟩
    intro next member
    rw [field_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    simpa [leftBlocks,backups] using
      data_step context bit flag mode digit (leftBlocks later++false::left)
        (backups cells++true::scratch) target background

theorem field_last (context : C) (bit flag mode : Bool)
    (digits cells left scratch target : List Bool) (background : RatInput.Stack → List Bool) :
    ∃ resultBit,(fieldTrace context bit flag mode digits cells left scratch target background).getLast?=
      some (state (some 4) (context,(resultBit,true,mode))
        (cells.reverse++leftBlocks digits++false::left) scratch (leftBlocks digits.reverse++target) background) := by
  induction digits generalizing bit flag cells target with
  | nil =>
    refine ⟨finalBit (false::cells) bit,?_⟩
    rw [fieldTrace,List.getLast?_cons_of_ne_nil (PSTRSymbolicRatExport.restore_nonempty context bit false mode
      (false::cells) left scratch target background),PSTRSymbolicRatExport.restore_last]
    simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.append_assoc,List.cons_append,
      leftBlocks,List.flatMap_nil,List.append_nil]
  | cons digit later ih =>
    obtain ⟨resultBit,last⟩:=ih digit true (digit::true::cells) (true::digit::target)
    refine ⟨resultBit,?_⟩
    rw [fieldTrace,List.getLast?_cons_of_ne_nil (field_nonempty context digit true mode later
      (digit::true::cells) left scratch (true::digit::target) background),last]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append,
      leftBlocks,List.flatMap_cons,List.flatMap_append,List.flatMap_nil,List.append_nil]

/-- Exact finite field prefix is an internal archive ABI. The preceding
original header parser must establish it from its actual TRUE-marked tape. -/
theorem actual (context : C) (bit flag mode : Bool)
    (digits left scratch target : List Bool) (background : RatInput.Stack → List Bool) :
    ∃ (run : List (State C)) (resultBit : Bool),
      run.head?=some (state (some 0) (context,(bit,flag,mode))
        (false::(leftBlocks digits++false::left)) scratch target background) ∧
      run.IsChain (fun before after => TM2.step (program .halt) before=some after) ∧
      run.getLast?=some (state (some 4) (context,(resultBit,true,mode))
        (false::(leftBlocks digits++false::left)) scratch
        (leftBlocks digits.reverse++false::false::target) background) ∧
      run.length=3*digits.length+6 := by
  let run:=state (some 0) (context,(bit,flag,mode))
    (false::(leftBlocks digits++false::left)) scratch target background ::
    fieldTrace context false flag mode digits [false] left scratch (false::false::target) background
  obtain ⟨resultBit,last⟩:=field_last context false flag mode digits [false] left scratch (false::false::target) background
  refine ⟨run,resultBit,rfl,?_,?_,?_⟩
  · apply List.isChain_cons.mpr
    refine ⟨?_,field_chain context false flag mode digits [false] left scratch (false::false::target) background⟩
    intro next member
    rw [field_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact prepare_step context bit flag mode (leftBlocks digits++false::left) scratch target background
  · rw [List.getLast?_cons_of_ne_nil (field_nonempty context false flag mode digits [false] left scratch
      (false::false::target) background),last]
    rfl
  · simp only [run,List.length_cons,field_length,List.length_nil]

end B23_4_RatWordPrep.NatField
