module

public import B23_4_RatWordPrep_SeqCmp_RewindCode_055

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.Rewind

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool

variable {C : Type*}

def moveTrace (background : RatInput.Stack → List Bool) (memory : Store C) :
    List Bool → List Bool → List Bool → List (State C)
  | [], source, archive =>
      [state background .move memory source archive [],state background .done (memory.1,false,false) source archive []]
  | value::later, source, archive =>
      state background .move memory source archive (value::later)::
        moveTrace background (memory.1,true,value) later (value::source) archive

theorem move_head (background : RatInput.Stack → List Bool) (memory : Store C)
    (backup source archive : List Bool) :
    (moveTrace background memory backup source archive).head?=some (state background .move memory source archive backup) := by
  cases backup <;> rfl

theorem move_nonempty (background : RatInput.Stack → List Bool) (memory : Store C)
    (backup source archive : List Bool) : moveTrace background memory backup source archive≠[] := by
  cases backup <;> intro same <;> cases same

theorem move_length (background : RatInput.Stack → List Bool) (memory : Store C)
    (backup source archive : List Bool) : (moveTrace background memory backup source archive).length=backup.length+2 := by
  induction backup generalizing memory source with
  | nil => rfl
  | cons value later ih => simp only [moveTrace,List.length_cons,ih]

theorem move_last (background : RatInput.Stack → List Bool) (memory : Store C)
    (backup source archive : List Bool) :
    (moveTrace background memory backup source archive).getLast?=
      some (state background .done (memory.1,false,false) (backup.reverse++source) archive []) := by
  induction backup generalizing memory source with
  | nil => rfl
  | cons value later ih =>
    rw [moveTrace,List.getLast?_cons_of_ne_nil (move_nonempty background (memory.1,true,value) later (value::source) archive),ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem move_chain (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (backup source archive : List Bool) :
    (moveTrace background memory backup source archive).IsChain (fun a b => TM2.step (program caller) a=some b) := by
  induction backup generalizing memory source with
  | nil => exact List.isChain_cons_cons.mpr ⟨move_end caller background memory source archive,List.isChain_singleton _⟩
  | cons value later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih (memory.1,true,value) (value::source)⟩
    intro next member
    rw [move_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact move_bit caller background memory value source archive later

def clear1Trace (background : RatInput.Stack → List Bool) (memory : Store C) :
    List Bool → List Bool → List (State C)
  | [], backup => state background (.clear true) memory [] [] backup::moveTrace background (memory.1,false,false) backup [] []
  | value::later, backup => state background (.clear true) memory [] (value::later) backup::
      clear1Trace background (memory.1,true,value) later backup

theorem clear1_head (background : RatInput.Stack → List Bool) (memory : Store C) (archive backup : List Bool) :
    (clear1Trace background memory archive backup).head?=some (state background (.clear true) memory [] archive backup) := by
  cases archive <;> rfl

theorem clear1_nonempty (background : RatInput.Stack → List Bool) (memory : Store C) (archive backup : List Bool) :
    clear1Trace background memory archive backup≠[] := by
  cases archive <;> intro same <;> cases same

theorem clear1_length (background : RatInput.Stack → List Bool) (memory : Store C) (archive backup : List Bool) :
    (clear1Trace background memory archive backup).length=archive.length+backup.length+3 := by
  induction archive generalizing memory with
  | nil => simp only [clear1Trace,List.length_cons,move_length,List.length_nil]; omega
  | cons value later ih => simp only [clear1Trace,List.length_cons,ih]; omega

theorem clear1_last (background : RatInput.Stack → List Bool) (memory : Store C) (archive backup : List Bool) :
    (clear1Trace background memory archive backup).getLast?=
      some (state background .done (memory.1,false,false) backup.reverse [] []) := by
  induction archive generalizing memory with
  | nil =>
    rw [clear1Trace,List.getLast?_cons_of_ne_nil (move_nonempty background (memory.1,false,false) backup [] []),move_last]
    simp only [List.append_nil]
  | cons value later ih =>
    rw [clear1Trace,List.getLast?_cons_of_ne_nil (clear1_nonempty background (memory.1,true,value) later backup),ih]

theorem clear1_chain (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (archive backup : List Bool) :
    (clear1Trace background memory archive backup).IsChain (fun a b => TM2.step (program caller) a=some b) := by
  induction archive generalizing memory with
  | nil =>
    apply List.isChain_cons.mpr
    refine ⟨?_,move_chain caller background (memory.1,false,false) backup [] []⟩
    intro next member
    rw [move_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact clear1_end caller background memory [] backup
  | cons value later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih (memory.1,true,value)⟩
    intro next member
    rw [clear1_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact clear1_bit caller background memory value [] later backup

def clear0Trace (background : RatInput.Stack → List Bool) (memory : Store C) :
    List Bool → List Bool → List Bool → List (State C)
  | [], archive, backup => state background (.clear false) memory [] archive backup::
      clear1Trace background (memory.1,false,false) archive backup
  | value::later, archive, backup => state background (.clear false) memory (value::later) archive backup::
      clear0Trace background (memory.1,true,value) later archive backup

theorem clear0_head (background : RatInput.Stack → List Bool) (memory : Store C) (source archive backup : List Bool) :
    (clear0Trace background memory source archive backup).head?=some (state background (.clear false) memory source archive backup) := by
  cases source <;> rfl

theorem clear0_nonempty (background : RatInput.Stack → List Bool) (memory : Store C) (source archive backup : List Bool) :
    clear0Trace background memory source archive backup≠[] := by
  cases source <;> intro same <;> cases same

theorem clear0_length (background : RatInput.Stack → List Bool) (memory : Store C) (source archive backup : List Bool) :
    (clear0Trace background memory source archive backup).length=source.length+archive.length+backup.length+4 := by
  induction source generalizing memory with
  | nil => simp only [clear0Trace,List.length_cons,clear1_length,List.length_nil]; omega
  | cons value later ih => simp only [clear0Trace,List.length_cons,ih]; omega

theorem clear0_last (background : RatInput.Stack → List Bool) (memory : Store C) (source archive backup : List Bool) :
    (clear0Trace background memory source archive backup).getLast?=
      some (state background .done (memory.1,false,false) backup.reverse [] []) := by
  induction source generalizing memory with
  | nil =>
    rw [clear0Trace,List.getLast?_cons_of_ne_nil (clear1_nonempty background (memory.1,false,false) archive backup),clear1_last]
  | cons value later ih =>
    rw [clear0Trace,List.getLast?_cons_of_ne_nil (clear0_nonempty background (memory.1,true,value) later archive backup),ih]

theorem clear0_chain (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (source archive backup : List Bool) :
    (clear0Trace background memory source archive backup).IsChain (fun a b => TM2.step (program caller) a=some b) := by
  induction source generalizing memory with
  | nil =>
    apply List.isChain_cons.mpr
    refine ⟨?_,clear1_chain caller background (memory.1,false,false) archive backup⟩
    intro next member
    rw [clear1_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact clear0_end caller background memory archive backup
  | cons value later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih (memory.1,true,value)⟩
    intro next member
    rw [clear0_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact clear0_bit caller background memory value later archive backup

theorem actual (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (source archive backup : List Bool) :
    ∃ run : List (State C),
      run.head?=some (state background (.clear false) memory source archive backup) ∧
      run.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      run.getLast?=some (state background .done (memory.1,false,false) backup.reverse [] []) ∧
      run.length=source.length+archive.length+backup.length+4 :=
  ⟨clear0Trace background memory source archive backup,clear0_head _ _ _ _ _,
    clear0_chain _ _ _ _ _ _,clear0_last _ _ _ _ _,clear0_length _ _ _ _ _⟩

end B23_4_RatWordPrep.Rewind
