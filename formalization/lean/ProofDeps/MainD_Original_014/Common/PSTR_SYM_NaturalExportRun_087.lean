module

public import Common.PSTR_SYM_NaturalExportCode_086
public import Common.PSTR_SYM_LaneArchive_044

/-! Actual traces of086, with arbitrary old scratch/destination tails.
The endpoint is an active ZERO3/POS4 port. Payload is flagged by TRUE
and terminated by two freshly pushed FALSEs, independently of oldTail. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport

open Turing PSTRTMRawNat010

def lane (digits : List Bool) : List Bool := digits.flatMap (fun digit => [digit,false])

def backups (cells : List Bool) : List Bool := cells.flatMap (fun cell => [false,cell])

def finalBit : List Bool → Bool → Bool
  | [], bit => bit
  | cell :: later, _ => finalBit later cell

theorem lane_length (digits : List Bool) : (lane digits).length = 2 * digits.length := by
  induction digits with
  | nil => rfl
  | cons digit later ih =>
    simp only [lane,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *
    omega

theorem backups_append (first later : List Bool) :
    backups (first ++ later) = backups first ++ backups later := by
  exact List.flatMap_append

theorem backups_length (cells : List Bool) : (backups cells).length = 2 * cells.length := by
  induction cells with
  | nil => rfl
  | cons cell later ih =>
    simp only [backups,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *
    omega

def restoreTrace {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) : List (State C) :=
  match cells with
  | [] =>
      [state (some 2) (context,(bit,flag,mode)) left (true :: scratch) target background,
       state (some (if mode then 4 else 3)) (context,(bit,true,mode)) left scratch target background]
  | cell :: later =>
      state (some 2) (context,(bit,flag,mode)) left
        (backups (cell :: later) ++ true :: scratch) target background ::
      restoreTrace context cell false mode later (cell :: left) scratch target background

theorem restore_head {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch target background).head? =
      some (state (some 2) (context,(bit,flag,mode)) left
        (backups cells ++ true :: scratch) target background) := by
  cases cells <;> rfl

theorem restore_nonempty {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    restoreTrace context bit flag mode cells left scratch target background ≠ [] := by
  cases cells <;> intro equal <;> cases equal

theorem restore_length {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch target background).length = cells.length + 2 := by
  induction cells generalizing bit flag left with
  | nil => rfl
  | cons cell later ih =>
    simp only [restoreTrace,List.length_cons,ih]

theorem restore_chain {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch target background).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction cells generalizing bit flag left with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨sentinel_step context bit flag mode left scratch target background,
      List.isChain_singleton _⟩
  | cons cell later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih cell false (cell :: left)⟩
    intro next member
    rw [restore_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    simpa only [backups,List.flatMap_cons,List.cons_append,List.nil_append] using
      restore_step context bit flag mode cell left (backups later ++ true :: scratch) target background

theorem restore_last {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch target background).getLast? =
      some (state (some (if mode then 4 else 3)) (context,(finalBit cells bit,true,mode))
        (cells.reverse ++ left) scratch target background) := by
  induction cells generalizing bit flag left with
  | nil => rfl
  | cons cell later ih =>
    rw [restoreTrace,List.getLast?_cons_of_ne_nil (restore_nonempty context cell false mode later
      (cell :: left) scratch target background),ih]
    simp only [finalBit,List.reverse_cons,List.append_assoc,List.singleton_append]

def loopTrace {C : Type*} (context : C) (bit flag : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) : List (State C) :=
  match digits with
  | [] =>
      state (some 1) (context,(bit,flag,true)) (false :: true :: left)
        (backups cells ++ true :: scratch) target background ::
      restoreTrace context false true true cells (false :: true :: left) scratch target background
  | digit :: later =>
      state (some 1) (context,(bit,flag,true)) (lane (digit :: later) ++ false :: true :: left)
        (backups cells ++ true :: scratch) target background ::
      loopTrace context digit false later (false :: digit :: cells) left scratch
        (true :: digit :: target) background

theorem loop_head {C : Type*} (context : C) (bit flag : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    (loopTrace context bit flag digits cells left scratch target background).head? =
      some (state (some 1) (context,(bit,flag,true)) (lane digits ++ false :: true :: left)
        (backups cells ++ true :: scratch) target background) := by
  cases digits <;> rfl

theorem loop_nonempty {C : Type*} (context : C) (bit flag : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    loopTrace context bit flag digits cells left scratch target background ≠ [] := by
  cases digits <;> intro equal <;> cases equal

theorem loop_length {C : Type*} (context : C) (bit flag : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    (loopTrace context bit flag digits cells left scratch target background).length =
      3 * digits.length + cells.length + 3 := by
  induction digits generalizing bit flag cells target with
  | nil => simp only [loopTrace,List.length_cons,restore_length,List.length_nil]; omega
  | cons digit later ih =>
    simp only [loopTrace,List.length_cons,ih]
    omega

theorem loop_chain {C : Type*} (context : C) (bit flag : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    (loopTrace context bit flag digits cells left scratch target background).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction digits generalizing bit flag cells target with
  | nil =>
    apply List.isChain_cons.mpr
    refine ⟨?_,restore_chain context false true true cells (false :: true :: left) scratch target background⟩
    intro next member
    rw [restore_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact boundary_step context bit flag left (backups cells ++ true :: scratch) target background
  | cons digit later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih digit false (false :: digit :: cells) (true :: digit :: target)⟩
    intro next member
    rw [loop_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    simpa only [lane,backups,List.flatMap_cons,List.cons_append,List.nil_append] using
      payload_step context bit flag digit (lane later ++ false :: true :: left)
        (backups cells ++ true :: scratch) target background

theorem loop_last {C : Type*} (context : C) (bit flag : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    ∃ resultBit,
      (loopTrace context bit flag digits cells left scratch target background).getLast? =
        some (state (some 4) (context,(resultBit,true,true))
          (cells.reverse ++ lane digits ++ false :: true :: left) scratch
          (leftBlocks digits.reverse ++ target) background) := by
  induction digits generalizing bit flag cells target with
  | nil =>
    refine ⟨finalBit cells false,?_⟩
    rw [loopTrace,List.getLast?_cons_of_ne_nil (restore_nonempty context false true true cells
      (false :: true :: left) scratch target background),restore_last]
    simp only [lane,leftBlocks,List.flatMap_nil,List.reverse_nil,List.nil_append,List.append_nil,ite_true]
  | cons digit later ih =>
    obtain ⟨resultBit,last⟩ := ih digit false (false :: digit :: cells) (true :: digit :: target)
    refine ⟨resultBit,?_⟩
    rw [loopTrace,List.getLast?_cons_of_ne_nil (loop_nonempty context digit false later
      (false :: digit :: cells) left scratch (true :: digit :: target) background),last]
    simp only [List.reverse_cons,List.nil_append,lane,leftBlocks,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
      List.append_assoc]

def positiveTrace {C : Type*} (context : C) (bit flag mode : Bool)
    (digits left scratch target : List Bool) (background : Slot → List Bool) : List (State C) :=
  state (some 0) (context,(bit,flag,mode))
    (false :: true :: (lane digits ++ false :: true :: left)) scratch target background ::
  loopTrace context false flag digits [true,false] left scratch (false :: false :: target) background

theorem actual_positive {C : Type*} (context : C) (bit flag mode : Bool)
    (digits left scratch target : List Bool) (background : Slot → List Bool) :
    ∃ resultBit,
      (positiveTrace context bit flag mode digits left scratch target background).head? =
        some (state (some 0) (context,(bit,flag,mode))
          (false :: true :: (lane digits ++ false :: true :: left)) scratch target background) ∧
      (positiveTrace context bit flag mode digits left scratch target background).IsChain
        (fun before after => TM2.step program before = some after) ∧
      (positiveTrace context bit flag mode digits left scratch target background).getLast? =
        some (state (some 4) (context,(resultBit,true,true))
          (false :: true :: (lane digits ++ false :: true :: left)) scratch
          (leftBlocks digits.reverse ++ false :: false :: target) background) ∧
      (positiveTrace context bit flag mode digits left scratch target background).length = 3 * digits.length + 6 := by
  obtain ⟨resultBit,last⟩ := loop_last context false flag digits [true,false] left scratch
    (false :: false :: target) background
  refine ⟨resultBit,rfl,?_,?_,?_⟩
  · apply List.isChain_cons.mpr
    refine ⟨?_,loop_chain context false flag digits [true,false] left scratch (false :: false :: target) background⟩
    intro next member
    rw [loop_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact prepare_step context bit flag mode true (lane digits ++ false :: true :: left) scratch target background
  · rw [positiveTrace,List.getLast?_cons_of_ne_nil (loop_nonempty context false flag digits
      [true,false] left scratch (false :: false :: target) background),last]
    rfl
  · simp only [positiveTrace,List.length_cons,loop_length,List.length_nil]

def zeroTrace {C : Type*} (context : C) (bit flag mode : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) : List (State C) :=
  state (some 0) (context,(bit,flag,mode)) (false :: false :: left) scratch target background ::
    restoreTrace context false flag false [false,false] left scratch (false :: false :: target) background

theorem actual_zero {C : Type*} (context : C) (bit flag mode : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) :
    (zeroTrace context bit flag mode left scratch target background).head? =
      some (state (some 0) (context,(bit,flag,mode)) (false :: false :: left) scratch target background) ∧
    (zeroTrace context bit flag mode left scratch target background).IsChain
      (fun before after => TM2.step program before = some after) ∧
    (zeroTrace context bit flag mode left scratch target background).getLast? =
      some (state (some 3) (context,(false,true,false)) (false :: false :: left) scratch
        (false :: false :: target) background) ∧
    (zeroTrace context bit flag mode left scratch target background).length = 5 := by
  refine ⟨rfl,?_,?_,rfl⟩
  · apply List.isChain_cons.mpr
    refine ⟨?_,restore_chain context false flag false [false,false] left scratch (false :: false :: target) background⟩
    intro next member
    rw [restore_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact prepare_step context bit flag mode false left scratch target background
  · rw [zeroTrace,List.getLast?_cons_of_ne_nil (restore_nonempty context false flag false
      [false,false] left scratch (false :: false :: target) background),restore_last]
    rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport
