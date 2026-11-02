module

public import Structure.L01_3_5_TABLE_Consumer_001

/-! A fixed physical previous-natural cursor on the actual paired archive.
The consumed cells are kept behind an owned sentinel on stack6; stack1 is
restored by real pops/pushes. No host length or record value enters code. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.L01_3_5_TABLE_RecordNav003

open Turing
open PaperProofs.Common.Native.PSTRWordVM
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRSymbolicNaturalExport

abbrev Label := Fin 5
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Memory C)

def slots (left scratch : List Bool) (background : Slot → List Bool) : Slot → List Bool :=
  fun slot => if slot = 1 then left else if slot = 6 then scratch else background slot

def state {C : Type*} (label : Option Label) (memory : Memory C)
    (left scratch : List Bool) (background : Slot → List Bool) : State C :=
  ⟨label,memory,slots left scratch background⟩

def program {C : Type*} (label : Label) : TM2.Stmt Alphabet Label (Memory C) :=
  if label = 0 then
    .push 6 (fun _ => true)
      (.pop 1 captureBit (.push 6 savedBit (.push 6 (fun _ => false)
        (.pop 1 captureFlag (.push 6 savedFlag (.push 6 (fun _ => false)
          (.goto (fun _ => 1))))))))
  else if label = 1 then
    .pop 1 captureBit (.peek 1 captureFlag
      (.branch savedFlag
        (.push 1 savedBit (.goto (fun _ => 2)))
        (.pop 1 (fun memory _ => memory)
          (.push 6 savedBit (.push 6 (fun _ => false)
            (.push 6 (fun _ => false) (.push 6 (fun _ => false)
              (.goto (fun _ => 1)))))))))
  else if label = 3 then
    .pop 6 captureFlag
      (.branch savedFlag (.goto (fun _ => 4))
        (.pop 6 captureBit (.push 1 savedBit (.goto (fun _ => 3)))))
  else .halt

theorem slots_left (left scratch : List Bool) (background : Slot → List Bool) :
    slots left scratch background 1 = left := rfl

theorem slots_scratch (left scratch : List Bool) (background : Slot → List Bool) :
    slots left scratch background 6 = scratch := rfl

theorem slots_frame (left scratch : List Bool) (background : Slot → List Bool)
    (slot : Slot) (notLeft : slot ≠ 1) (notScratch : slot ≠ 6) :
    slots left scratch background slot = background slot := by
  simp only [slots,notLeft,notScratch,ite_false]

theorem update_left (left scratch replacement : List Bool) (background : Slot → List Bool) :
    Function.update (slots left scratch background) 1 replacement = slots replacement scratch background := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem update_scratch (left scratch replacement : List Bool) (background : Slot → List Bool) :
    Function.update (slots left scratch background) 6 replacement = slots left replacement background := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem prepare_step {C : Type*} (context : C) (bit flag mode : Bool)
    (left scratch : List Bool) (background : Slot → List Bool) :
    TM2.step program (state (some 0) (context,(bit,flag,mode))
      (false :: true :: left) scratch background) =
      some (state (some 1) (context,(false,true,mode)) left
        (false :: true :: false :: false :: true :: scratch) background) := by
  simp [program,state,TM2.step,TM2.stepAux,captureBit,captureFlag,savedBit,savedFlag,
    slots_left,slots_scratch,update_left,update_scratch]

theorem payload_step {C : Type*} (context : C) (bit flag mode digit : Bool)
    (left scratch : List Bool) (background : Slot → List Bool) :
    TM2.step program (state (some 1) (context,(bit,flag,mode))
      (digit :: false :: left) scratch background) =
      some (state (some 1) (context,(digit,false,mode)) left
        (false :: false :: false :: digit :: scratch) background) := by
  simp [program,state,TM2.step,TM2.stepAux,captureBit,captureFlag,savedBit,savedFlag,
    slots_left,slots_scratch,update_left,update_scratch]

theorem boundary_step {C : Type*} (context : C) (bit flag mode : Bool)
    (left scratch : List Bool) (background : Slot → List Bool) :
    TM2.step program (state (some 1) (context,(bit,flag,mode))
      (false :: true :: left) scratch background) =
      some (state (some 2) (context,(false,true,mode))
        (false :: true :: left) scratch background) := by
  simp [program,state,TM2.step,TM2.stepAux,captureBit,captureFlag,savedBit,savedFlag,
    slots_left,slots_scratch,update_left]

theorem restore_step {C : Type*} (context : C) (bit flag mode cell : Bool)
    (left scratch : List Bool) (background : Slot → List Bool) :
    TM2.step program (state (some 3) (context,(bit,flag,mode)) left
      (false :: cell :: scratch) background) =
      some (state (some 3) (context,(cell,false,mode)) (cell :: left) scratch background) := by
  simp [program,state,TM2.step,TM2.stepAux,captureBit,captureFlag,savedBit,savedFlag,
    slots_left,slots_scratch,update_left,update_scratch]

theorem sentinel_step {C : Type*} (context : C) (bit flag mode : Bool)
    (left scratch : List Bool) (background : Slot → List Bool) :
    TM2.step program (state (some 3) (context,(bit,flag,mode)) left
      (true :: scratch) background) =
      some (state (some 4) (context,(bit,true,mode)) left scratch background) := by
  simp [program,state,TM2.step,TM2.stepAux,captureFlag,savedFlag,slots_scratch,update_scratch]

def loopTrace {C : Type*} (context : C) (bit flag mode : Bool)
    (digits cells left scratch : List Bool) (background : Slot → List Bool) : List (State C) :=
  match digits with
  | [] =>
      [state (some 1) (context,(bit,flag,mode)) (false :: true :: left)
        (backups cells ++ true :: scratch) background,
       state (some 2) (context,(false,true,mode)) (false :: true :: left)
        (backups cells ++ true :: scratch) background]
  | digit :: later =>
      state (some 1) (context,(bit,flag,mode)) (lane (digit :: later) ++ false :: true :: left)
        (backups cells ++ true :: scratch) background ::
      loopTrace context digit false mode later (false :: digit :: cells) left scratch background

theorem loop_head {C : Type*} (context : C) (bit flag mode : Bool)
    (digits cells left scratch : List Bool) (background : Slot → List Bool) :
    (loopTrace context bit flag mode digits cells left scratch background).head? =
      some (state (some 1) (context,(bit,flag,mode)) (lane digits ++ false :: true :: left)
        (backups cells ++ true :: scratch) background) := by
  cases digits <;> rfl

theorem loop_nonempty {C : Type*} (context : C) (bit flag mode : Bool)
    (digits cells left scratch : List Bool) (background : Slot → List Bool) :
    loopTrace context bit flag mode digits cells left scratch background ≠ [] := by
  cases digits <;> intro equal <;> cases equal

theorem loop_chain {C : Type*} (context : C) (bit flag mode : Bool)
    (digits cells left scratch : List Bool) (background : Slot → List Bool) :
    (loopTrace context bit flag mode digits cells left scratch background).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction digits generalizing bit flag cells with
  | nil =>
      exact List.isChain_cons_cons.mpr ⟨boundary_step context bit flag mode left _ background,
        List.isChain_singleton _⟩
  | cons digit later ih =>
      apply List.isChain_cons.mpr
      refine ⟨?_,ih digit false (false :: digit :: cells)⟩
      intro next member
      rw [loop_head] at member
      simp only [Option.mem_def,Option.some.injEq] at member
      subst next
      simpa only [lane,backups,List.flatMap_cons,List.cons_append,List.nil_append] using
        payload_step context bit flag mode digit (lane later ++ false :: true :: left)
          (backups cells ++ true :: scratch) background

theorem loop_last {C : Type*} (context : C) (bit flag mode : Bool)
    (digits cells left scratch : List Bool) (background : Slot → List Bool) :
    (loopTrace context bit flag mode digits cells left scratch background).getLast? =
      some (state (some 2) (context,(false,true,mode)) (false :: true :: left)
        (backups ((lane digits).reverse ++ cells) ++ true :: scratch) background) := by
  induction digits generalizing bit flag cells with
  | nil => rfl
  | cons digit later ih =>
      rw [loopTrace,List.getLast?_cons_of_ne_nil (loop_nonempty context digit false mode
        later (false :: digit :: cells) left scratch background),ih]
      simp only [lane,List.flatMap_cons,List.cons_append,List.nil_append,List.reverse_cons,
        List.append_assoc]

theorem loop_length {C : Type*} (context : C) (bit flag mode : Bool)
    (digits cells left scratch : List Bool) (background : Slot → List Bool) :
    (loopTrace context bit flag mode digits cells left scratch background).length = digits.length + 2 := by
  induction digits generalizing bit flag cells with
  | nil => rfl
  | cons digit later ih => simp only [loopTrace,List.length_cons,ih]

def skipped (digits : List Bool) : List Bool := false :: true :: lane digits

def skipTrace {C : Type*} (context : C) (bit flag mode : Bool)
    (digits left scratch : List Bool) (background : Slot → List Bool) : List (State C) :=
  state (some 0) (context,(bit,flag,mode)) (skipped digits ++ false :: true :: left) scratch background ::
    loopTrace context false true mode digits [true,false] left scratch background

theorem actual_skip {C : Type*} (context : C) (bit flag mode : Bool)
    (digits left scratch : List Bool) (background : Slot → List Bool) :
    (skipTrace context bit flag mode digits left scratch background).head? =
        some (state (some 0) (context,(bit,flag,mode))
          (skipped digits ++ false :: true :: left) scratch background) ∧
      (skipTrace context bit flag mode digits left scratch background).IsChain
        (fun before after => TM2.step program before = some after) ∧
      (skipTrace context bit flag mode digits left scratch background).getLast? =
        some (state (some 2) (context,(false,true,mode)) (false :: true :: left)
          (backups (skipped digits).reverse ++ true :: scratch) background) ∧
      (skipTrace context bit flag mode digits left scratch background).length = digits.length + 3 := by
  refine ⟨rfl,?_,?_,?_⟩
  · apply List.isChain_cons.mpr
    refine ⟨?_,loop_chain context false true mode digits [true,false] left scratch background⟩
    intro next member
    rw [loop_head] at member
    simp only [Option.mem_def,Option.some.injEq] at member
    subst next
    exact prepare_step context bit flag mode (lane digits ++ false :: true :: left) scratch background
  · rw [skipTrace,List.getLast?_cons_of_ne_nil (loop_nonempty context false true mode
      digits [true,false] left scratch background),loop_last]
    simp only [skipped,List.reverse_cons,List.append_assoc,List.singleton_append]
  · simp only [skipTrace,List.length_cons,loop_length]

def restoreTrace {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch : List Bool) (background : Slot → List Bool) : List (State C) :=
  match cells with
  | [] =>
      [state (some 3) (context,(bit,flag,mode)) left (true :: scratch) background,
       state (some 4) (context,(bit,true,mode)) left scratch background]
  | cell :: later =>
      state (some 3) (context,(bit,flag,mode)) left
        (backups (cell :: later) ++ true :: scratch) background ::
      restoreTrace context cell false mode later (cell :: left) scratch background

theorem restore_head {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch background).head? =
      some (state (some 3) (context,(bit,flag,mode)) left
        (backups cells ++ true :: scratch) background) := by
  cases cells <;> rfl

theorem restore_nonempty {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch : List Bool) (background : Slot → List Bool) :
    restoreTrace context bit flag mode cells left scratch background ≠ [] := by
  cases cells <;> intro equal <;> cases equal

theorem restore_chain {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch background).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction cells generalizing bit flag left with
  | nil => exact List.isChain_cons_cons.mpr ⟨sentinel_step context bit flag mode left scratch background,
      List.isChain_singleton _⟩
  | cons cell later ih =>
      apply List.isChain_cons.mpr
      refine ⟨?_,ih cell false (cell :: left)⟩
      intro next member
      rw [restore_head] at member
      simp only [Option.mem_def,Option.some.injEq] at member
      subst next
      simpa only [backups,List.flatMap_cons,List.cons_append,List.nil_append] using
        restore_step context bit flag mode cell left (backups later ++ true :: scratch) background

theorem restore_last {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch background).getLast? =
      some (state (some 4) (context,(finalBit cells bit,true,mode))
        (cells.reverse ++ left) scratch background) := by
  induction cells generalizing bit flag left with
  | nil => rfl
  | cons cell later ih =>
      rw [restoreTrace,List.getLast?_cons_of_ne_nil (restore_nonempty context cell false mode
        later (cell :: left) scratch background),ih]
      simp only [finalBit,List.reverse_cons,List.append_assoc,List.singleton_append]

theorem restore_length {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch : List Bool) (background : Slot → List Bool) :
    (restoreTrace context bit flag mode cells left scratch background).length = cells.length + 2 := by
  induction cells generalizing bit flag left with
  | nil => rfl
  | cons cell later ih => simp only [restoreTrace,List.length_cons,ih]

end PaperProofs.Common.Native.L01_3_5_TABLE_RecordNav003
