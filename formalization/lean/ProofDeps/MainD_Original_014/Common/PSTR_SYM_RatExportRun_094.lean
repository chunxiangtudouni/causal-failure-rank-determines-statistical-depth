module

public import Common.PSTR_SYM_RatExportCode_093

/-! SAME093 execution, in original DEN/NUM/sign physical order. Both field
copies and every restoration cell are actual steps. The untouched RIGHT
suffix and arbitrary old7/15 are carried by the full stack function. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRatExport

open Turing PaperProofs.Common.Native.PSTRWordVM PSTRSymbolicNaturalExport PSTRTMRawNat010

abbrev State (C : Type*) := PSTRSymbolicNaturalExport.State C

theorem old_restore_labels {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    ∀ current ∈ PSTRSymbolicNaturalExport.restoreTrace context bit flag mode cells left scratch target background,
      current.l = some 2 ∨ current.l = some (if mode then 4 else 3) := by
  induction cells generalizing bit flag left with
  | nil =>
    intro current present
    rcases List.mem_cons.mp present with same | later
    · subst current; exact Or.inl rfl
    · have same := List.mem_singleton.mp later
      subst current; exact Or.inr rfl
  | cons cell later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | remaining
    · subst current; exact Or.inl rfl
    · exact ih cell false (cell :: left) current remaining

def restoreTrace {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) : List (State C) :=
  (PSTRSymbolicNaturalExport.restoreTrace context bit flag mode cells left scratch target background).map
    (LabelMap.configuration restoreLabel)

theorem restore_head {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch target background).head? =
      some (state (some 3) (context,(bit,flag,mode)) left (backups cells ++ true :: scratch) target background) := by
  rw [restoreTrace,List.head?_map,PSTRSymbolicNaturalExport.restore_head,Option.map_some]
  rfl

theorem restore_nonempty {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    restoreTrace context bit flag mode cells left scratch target background ≠ [] := by
  intro empty
  have head := restore_head context bit flag mode cells left scratch target background
  rw [empty] at head
  cases head

theorem restore_length {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch target background).length = cells.length+2 := by
  rw [restoreTrace,List.length_map,PSTRSymbolicNaturalExport.restore_length]

theorem restore_chain {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch target background).IsChain
      (fun before after => TM2.step ratProgram before = some after) := by
  apply LabelMap.chain_configuration_on restoreLabel program ratProgram _
    (PSTRSymbolicNaturalExport.restore_chain context bit flag mode cells left scratch target background)
  intro current present label active
  have positions := old_restore_labels context bit flag mode cells left scratch target background
    current (List.mem_of_mem_dropLast present)
  rcases positions with restoring | returned
  · have same : label = 2 := Option.some.inj (active.symm.trans restoring)
    subst label
    exact restore_body
  · have same : label = (if mode then 4 else 3) := Option.some.inj (active.symm.trans returned)
    subst label
    cases mode <;> rfl

theorem restore_last {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch target background).getLast? =
      some (state (some 4) (context,(finalBit cells bit,true,mode))
        (cells.reverse ++ left) scratch target background) := by
  rw [restoreTrace,List.getLast?_map,PSTRSymbolicNaturalExport.restore_last,Option.map_some]
  cases mode <;> rfl

def numeratorTrace {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) : List (State C) :=
  match digits with
  | [] =>
      state (some 2) (context,(bit,flag,mode)) (false :: negative :: left)
        (backups cells ++ true :: scratch) target background ::
      restoreTrace context negative false mode (negative :: false :: cells) left scratch (true :: negative :: target) background
  | digit :: later =>
      state (some 2) (context,(bit,flag,mode)) (leftBlocks (digit :: later) ++ false :: negative :: left)
        (backups cells ++ true :: scratch) target background ::
      numeratorTrace context digit true mode negative later (digit :: true :: cells) left scratch
        (true :: digit :: target) background

theorem numerator_head {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    (numeratorTrace context bit flag mode negative digits cells left scratch target background).head? =
      some (state (some 2) (context,(bit,flag,mode)) (leftBlocks digits ++ false :: negative :: left)
        (backups cells ++ true :: scratch) target background) := by
  cases digits <;> rfl

theorem numerator_nonempty {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    numeratorTrace context bit flag mode negative digits cells left scratch target background ≠ [] := by
  cases digits <;> intro empty <;> cases empty

theorem numerator_length {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    (numeratorTrace context bit flag mode negative digits cells left scratch target background).length =
      3*digits.length+cells.length+5 := by
  induction digits generalizing bit flag cells target with
  | nil => simp only [numeratorTrace,List.length_cons,restore_length,List.length_nil]; omega
  | cons digit later ih => simp only [numeratorTrace,List.length_cons,ih]; omega

theorem numerator_chain {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    (numeratorTrace context bit flag mode negative digits cells left scratch target background).IsChain
      (fun before after => TM2.step ratProgram before = some after) := by
  induction digits generalizing bit flag cells target with
  | nil =>
    apply List.isChain_cons.mpr
    refine ⟨?_,restore_chain context negative false mode (negative :: false :: cells) left scratch (true :: negative :: target) background⟩
    intro next present
    rw [restore_head] at present
    simp only [Option.mem_def,Option.some.injEq] at present
    subst next
    simpa only [backups,List.flatMap_cons,List.cons_append,List.nil_append] using
      numerator_end_step context bit flag mode negative left (backups cells ++ true :: scratch) target background
  | cons digit later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih digit true (digit :: true :: cells) (true :: digit :: target)⟩
    intro next present
    rw [numerator_head] at present
    simp only [Option.mem_def,Option.some.injEq] at present
    subst next
    simpa [leftBlocks,backups] using
      data_step context bit flag mode digit true (leftBlocks later ++ false :: negative :: left)
        (backups cells ++ true :: scratch) target background

theorem numerator_last {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    ∃ resultBit,
      (numeratorTrace context bit flag mode negative digits cells left scratch target background).getLast? =
        some (state (some 4) (context,(resultBit,true,mode))
          (cells.reverse ++ leftBlocks digits ++ false :: negative :: left) scratch
          (true :: negative :: (leftBlocks digits.reverse ++ target)) background) := by
  induction digits generalizing bit flag cells target with
  | nil =>
    refine ⟨finalBit (negative :: false :: cells) negative,?_⟩
    rw [numeratorTrace,List.getLast?_cons_of_ne_nil (restore_nonempty context negative false mode
      (negative :: false :: cells) left scratch (true :: negative :: target) background),restore_last]
    simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.append_assoc,List.cons_append,
      leftBlocks,List.flatMap_nil,List.append_nil]
  | cons digit later ih =>
    obtain ⟨resultBit,last⟩ := ih digit true (digit :: true :: cells) (true :: digit :: target)
    refine ⟨resultBit,?_⟩
    rw [numeratorTrace,List.getLast?_cons_of_ne_nil (numerator_nonempty context digit true mode negative later
      (digit :: true :: cells) left scratch (true :: digit :: target) background),last]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append,
      leftBlocks,List.flatMap_cons,List.flatMap_append,List.flatMap_nil,List.append_nil]

def denominatorTrace {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits numerator cells left scratch target : List Bool) (background : Slot → List Bool) : List (State C) :=
  match digits with
  | [] =>
      state (some 1) (context,(bit,flag,mode)) (false :: (leftBlocks numerator ++ false :: negative :: left))
        (backups cells ++ true :: scratch) target background ::
      numeratorTrace context bit false mode negative numerator (false :: cells) left scratch (false :: false :: target) background
  | digit :: later =>
      state (some 1) (context,(bit,flag,mode))
        (leftBlocks (digit :: later) ++ false :: (leftBlocks numerator ++ false :: negative :: left))
        (backups cells ++ true :: scratch) target background ::
      denominatorTrace context digit true mode negative later numerator (digit :: true :: cells) left scratch
        (true :: digit :: target) background

theorem denominator_head {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits numerator cells left scratch target : List Bool) (background : Slot → List Bool) :
    (denominatorTrace context bit flag mode negative digits numerator cells left scratch target background).head? =
      some (state (some 1) (context,(bit,flag,mode))
        (leftBlocks digits ++ false :: (leftBlocks numerator ++ false :: negative :: left))
        (backups cells ++ true :: scratch) target background) := by
  cases digits <;> rfl

theorem denominator_nonempty {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits numerator cells left scratch target : List Bool) (background : Slot → List Bool) :
    denominatorTrace context bit flag mode negative digits numerator cells left scratch target background ≠ [] := by
  cases digits <;> intro empty <;> cases empty

theorem denominator_length {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits numerator cells left scratch target : List Bool) (background : Slot → List Bool) :
    (denominatorTrace context bit flag mode negative digits numerator cells left scratch target background).length =
      3*(digits.length+numerator.length)+cells.length+7 := by
  induction digits generalizing bit flag cells target with
  | nil => simp only [denominatorTrace,List.length_cons,numerator_length,List.length_nil]; omega
  | cons digit later ih => simp only [denominatorTrace,List.length_cons,ih]; omega

theorem denominator_chain {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits numerator cells left scratch target : List Bool) (background : Slot → List Bool) :
    (denominatorTrace context bit flag mode negative digits numerator cells left scratch target background).IsChain
      (fun before after => TM2.step ratProgram before = some after) := by
  induction digits generalizing bit flag cells target with
  | nil =>
    apply List.isChain_cons.mpr
    refine ⟨?_,numerator_chain context bit false mode negative numerator (false :: cells) left scratch (false :: false :: target) background⟩
    intro next present
    rw [numerator_head] at present
    simp only [Option.mem_def,Option.some.injEq] at present
    subst next
    simpa only [backups,List.flatMap_cons,List.cons_append,List.nil_append] using
      denominator_end_step context bit flag mode (leftBlocks numerator ++ false :: negative :: left)
        (backups cells ++ true :: scratch) target background
  | cons digit later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih digit true (digit :: true :: cells) (true :: digit :: target)⟩
    intro next present
    rw [denominator_head] at present
    simp only [Option.mem_def,Option.some.injEq] at present
    subst next
    simpa [leftBlocks,backups] using
      data_step context bit flag mode digit false (leftBlocks later ++ false :: (leftBlocks numerator ++ false :: negative :: left))
        (backups cells ++ true :: scratch) target background

theorem denominator_last {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits numerator cells left scratch target : List Bool) (background : Slot → List Bool) :
    ∃ resultBit,
      (denominatorTrace context bit flag mode negative digits numerator cells left scratch target background).getLast? =
        some (state (some 4) (context,(resultBit,true,mode))
          (cells.reverse ++ leftBlocks digits ++ false :: (leftBlocks numerator ++ false :: negative :: left)) scratch
          (true :: negative :: (leftBlocks numerator.reverse ++ false :: false :: (leftBlocks digits.reverse ++ target))) background) := by
  induction digits generalizing bit flag cells target with
  | nil =>
    obtain ⟨resultBit,last⟩ := numerator_last context bit false mode negative numerator (false :: cells) left scratch
      (false :: false :: target) background
    refine ⟨resultBit,?_⟩
    rw [denominatorTrace,List.getLast?_cons_of_ne_nil (numerator_nonempty context bit false mode negative numerator
      (false :: cells) left scratch (false :: false :: target) background),last]
    simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.append_assoc,List.cons_append,
      leftBlocks,List.flatMap_nil,List.append_nil]
  | cons digit later ih =>
    obtain ⟨resultBit,last⟩ := ih digit true (digit :: true :: cells) (true :: digit :: target)
    refine ⟨resultBit,?_⟩
    rw [denominatorTrace,List.getLast?_cons_of_ne_nil (denominator_nonempty context digit true mode negative later numerator
      (digit :: true :: cells) left scratch (true :: digit :: target) background),last]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append,
      leftBlocks,List.flatMap_cons,List.flatMap_append,List.flatMap_nil,List.append_nil]

def archive (negative : Bool) (numerator denominator left : List Bool) : List Bool :=
  false :: (leftBlocks denominator ++ false :: (leftBlocks numerator ++ false :: negative :: left))

def packet (negative : Bool) (numerator denominator target : List Bool) : List Bool :=
  true :: negative :: (leftBlocks numerator ++ false :: false :: (leftBlocks denominator ++ false :: false :: target))

def ratTrace {C : Type*} (context : C) (bit flag mode negative : Bool)
    (numerator denominator left scratch target : List Bool) (background : Slot → List Bool) : List (State C) :=
  state (some 0) (context,(bit,flag,mode)) (archive negative numerator denominator left) scratch target background ::
    denominatorTrace context false flag mode negative denominator numerator [false] left scratch (false :: false :: target) background

theorem actual_rat_export {C : Type*} (context : C) (bit flag mode negative : Bool)
    (numerator denominator left scratch target : List Bool) (background : Slot → List Bool) :
    ∃ resultBit,
      (ratTrace context bit flag mode negative numerator denominator left scratch target background).head? =
        some (state (some 0) (context,(bit,flag,mode)) (archive negative numerator denominator left) scratch target background) ∧
      (ratTrace context bit flag mode negative numerator denominator left scratch target background).IsChain
        (fun before after => TM2.step ratProgram before = some after) ∧
      (ratTrace context bit flag mode negative numerator denominator left scratch target background).getLast? =
        some (state (some 4) (context,(resultBit,true,mode)) (archive negative numerator denominator left) scratch
          (packet negative numerator.reverse denominator.reverse target) background) ∧
      (ratTrace context bit flag mode negative numerator denominator left scratch target background).length =
        3*(numerator.length+denominator.length)+9 := by
  obtain ⟨resultBit,last⟩ := denominator_last context false flag mode negative denominator numerator [false] left scratch
    (false :: false :: target) background
  refine ⟨resultBit,rfl,?_,?_,?_⟩
  · apply List.isChain_cons.mpr
    refine ⟨?_,denominator_chain context false flag mode negative denominator numerator [false] left scratch (false :: false :: target) background⟩
    intro next present
    rw [denominator_head] at present
    simp only [Option.mem_def,Option.some.injEq] at present
    subst next
    exact prepare_step context bit flag mode (leftBlocks denominator ++ false :: (leftBlocks numerator ++ false :: negative :: left))
      scratch target background
  · rw [ratTrace,List.getLast?_cons_of_ne_nil (denominator_nonempty context false flag mode negative denominator numerator
      [false] left scratch (false :: false :: target) background),last]
    rfl
  · simp only [ratTrace,List.length_cons,denominator_length,List.length_nil]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRatExport
