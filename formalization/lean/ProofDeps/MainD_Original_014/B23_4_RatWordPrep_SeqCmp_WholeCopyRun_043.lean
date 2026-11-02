module

public import B23_4_RatWordPrep_SeqCmp_WholeCopyCode_042

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.WholeCopy

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

variable {C : Type*}

abbrev marked (cells scratch : List Bool) : List Bool :=
  PSTRSymbolicNaturalExport.backups cells ++ true::scratch

def restoreTrace (background : RatInput.Stack → List Bool) (memory : Store C) :
    List Bool → List Bool → List Bool → List Bool → List (State C)
  | [], source, backup, scratch =>
      [state background .restore memory source backup (true::scratch),
       state background .done (memory.1,true,true) source backup scratch]
  | value::later, source, backup, scratch =>
      state background .restore memory source backup (marked (value::later) scratch) ::
        restoreTrace background (memory.1,true,value) later (value::source) backup scratch

theorem restore_head (background : RatInput.Stack → List Bool) (memory : Store C)
    (cells source backup scratch : List Bool) :
    (restoreTrace background memory cells source backup scratch).head?=
      some (state background .restore memory source backup (marked cells scratch)) := by
  cases cells <;> rfl

theorem restore_nonempty (background : RatInput.Stack → List Bool) (memory : Store C)
    (cells source backup scratch : List Bool) :
    restoreTrace background memory cells source backup scratch≠[] := by
  cases cells <;> intro same <;> cases same

theorem restore_length (background : RatInput.Stack → List Bool) (memory : Store C)
    (cells source backup scratch : List Bool) :
    (restoreTrace background memory cells source backup scratch).length=cells.length+2 := by
  induction cells generalizing memory source with
  | nil => rfl
  | cons value later ih => simp only [restoreTrace,List.length_cons,ih]

theorem restore_last (background : RatInput.Stack → List Bool) (memory : Store C)
    (cells source backup scratch : List Bool) :
    (restoreTrace background memory cells source backup scratch).getLast?=
      some (state background .done (memory.1,true,true) (cells.reverse++source) backup scratch) := by
  induction cells generalizing memory source with
  | nil => rfl
  | cons value later ih =>
    rw [restoreTrace,List.getLast?_cons_of_ne_nil (restore_nonempty background (memory.1,true,value)
      later (value::source) backup scratch),ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem restore_chain (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (cells source backup scratch : List Bool) :
    (restoreTrace background memory cells source backup scratch).IsChain
      (fun before after => TM2.step (program caller) before=some after) := by
  induction cells generalizing memory source with
  | nil => exact List.isChain_cons_cons.mpr ⟨restore_end caller background memory source backup scratch,
      List.isChain_singleton _⟩
  | cons value later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih (memory.1,true,value) (value::source)⟩
    intro next member
    rw [restore_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    simpa only [marked,PSTRSymbolicNaturalExport.backups,List.flatMap_cons,List.cons_append,List.nil_append]
      using restore_bit caller background memory value source backup (marked later scratch)

def copyTrace (background : RatInput.Stack → List Bool) (memory : Store C) :
    List Bool → List Bool → List Bool → List Bool → List (State C)
  | [], reverseRead, backupTail, scratch =>
      state background .copy memory [] (reverseRead++backupTail) (marked reverseRead scratch) ::
        restoreTrace background (memory.1,false,false) reverseRead [] (reverseRead++backupTail) scratch
  | value::later, reverseRead, backupTail, scratch =>
      state background .copy memory (value::later) (reverseRead++backupTail) (marked reverseRead scratch) ::
        copyTrace background (memory.1,true,value) later (value::reverseRead) backupTail scratch

theorem copy_head (background : RatInput.Stack → List Bool) (memory : Store C)
    (source reverseRead backupTail scratch : List Bool) :
    (copyTrace background memory source reverseRead backupTail scratch).head?=
      some (state background .copy memory source (reverseRead++backupTail) (marked reverseRead scratch)) := by
  cases source <;> rfl

theorem copy_nonempty (background : RatInput.Stack → List Bool) (memory : Store C)
    (source reverseRead backupTail scratch : List Bool) :
    copyTrace background memory source reverseRead backupTail scratch≠[] := by
  cases source <;> intro same <;> cases same

theorem copy_length (background : RatInput.Stack → List Bool) (memory : Store C)
    (source reverseRead backupTail scratch : List Bool) :
    (copyTrace background memory source reverseRead backupTail scratch).length=
      2*source.length+reverseRead.length+3 := by
  induction source generalizing memory reverseRead with
  | nil => simp only [copyTrace,List.length_cons,restore_length,List.length_nil]; omega
  | cons value later ih => simp only [copyTrace,List.length_cons,ih]; omega

theorem copy_last (background : RatInput.Stack → List Bool) (memory : Store C)
    (source reverseRead backupTail scratch : List Bool) :
    (copyTrace background memory source reverseRead backupTail scratch).getLast?=
      some (state background .done (memory.1,true,true) (reverseRead.reverse++source)
        (source.reverse++reverseRead++backupTail) scratch) := by
  induction source generalizing memory reverseRead with
  | nil =>
    rw [copyTrace,List.getLast?_cons_of_ne_nil (restore_nonempty background (memory.1,false,false)
      reverseRead [] (reverseRead++backupTail) scratch),restore_last]
    simp only [List.append_nil,List.reverse_nil,List.nil_append]
  | cons value later ih =>
    rw [copyTrace,List.getLast?_cons_of_ne_nil (copy_nonempty background (memory.1,true,value)
      later (value::reverseRead) backupTail scratch),ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem copy_chain (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (source reverseRead backupTail scratch : List Bool) :
    (copyTrace background memory source reverseRead backupTail scratch).IsChain
      (fun before after => TM2.step (program caller) before=some after) := by
  induction source generalizing memory reverseRead with
  | nil =>
    apply List.isChain_cons.mpr
    refine ⟨?_,restore_chain caller background (memory.1,false,false) reverseRead [] (reverseRead++backupTail) scratch⟩
    intro next member
    rw [restore_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact copy_end caller background memory (reverseRead++backupTail) (marked reverseRead scratch)
  | cons value later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih (memory.1,true,value) (value::reverseRead)⟩
    intro next member
    rw [copy_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    simpa only [marked,PSTRSymbolicNaturalExport.backups,List.flatMap_cons,List.cons_append,List.nil_append]
      using copy_bit caller background memory value later (reverseRead++backupTail) (marked reverseRead scratch)

def trace (background : RatInput.Stack → List Bool) (memory : Store C)
    (source backup scratch : List Bool) : List (State C) :=
  state background .boot memory source backup scratch :: copyTrace background memory source [] backup scratch

/-- A single fixed real EOF-driven source copies every physical cell,
including FALSE and trailing blanks, with no supplied length/fuel/path. -/
theorem actual (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (source backup scratch : List Bool) :
    ∃ run : List (State C),
      run.head?=some (state background .boot memory source backup scratch) ∧
      run.IsChain (fun before after => TM2.step (program caller) before=some after) ∧
      run.getLast?=some (state background .done (memory.1,true,true) source (source.reverse++backup) scratch) ∧
      run.length=2*source.length+4 := by
  refine ⟨trace background memory source backup scratch,rfl,?_,?_,?_⟩
  · apply List.isChain_cons.mpr
    refine ⟨?_,copy_chain caller background memory source [] backup scratch⟩
    intro next member
    rw [copy_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact boot_step caller background memory source backup scratch
  · rw [trace,List.getLast?_cons_of_ne_nil (copy_nonempty background memory source [] backup scratch),copy_last]
    simp only [List.reverse_nil,List.nil_append,List.append_nil]
  · simp only [trace,List.length_cons,copy_length,List.length_nil]

end B23_4_RatWordPrep.WholeCopy
