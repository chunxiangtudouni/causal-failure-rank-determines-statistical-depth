module

public import Common.PSTR_WordVM_FieldCopy_003

/-! Actual fixed finite TM2 source for unique-key bank upsert.
This module defines real stack operations; it does not assert the unproved
whole-bank trace contract. Width is a REAL tally, never a control value.
Record-phase traces and allocation-derived bounds are separate obligations. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueStore

open Turing

abbrev Stack := Fin 16
abbrev Label := Fin 16
abbrev Alphabet (_ : Stack) := Bool
abbrev CallerFlags := Fin 4
abbrev Store := FieldCopy.Store × (Bool × CallerFlags)
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def present (memory : Store) : Bool := memory.1.1
def bit (memory : Store) : Bool := memory.1.2
def equal (memory : Store) : Bool := memory.2.1

def captureWidth (memory : Store) (value : Option Bool) : Store :=
  ((value.isSome, memory.1.2), memory.2)

def captureData (memory : Store) (value : Option Bool) : Store :=
  ((value.isSome, value.getD false), memory.2)

def captureCompare (memory : Store) (value : Option Bool) : Store :=
  ((value.isSome, value.getD false),
    (memory.2.1 && (memory.1.2 == value.getD false), memory.2.2))

def initializeEqual (memory : Store) : Store := (memory.1, (true, memory.2.2))

def jump (point : Label) : Statement := .goto (fun _ => point)

def widthBranch (yes no : Statement) : Statement :=
  .pop 11 captureWidth (.branch present yes no)

def restoreWidth (next : Statement) : Statement :=
  .pop 12 (fun memory _ => memory) (.push 11 (fun _ => true) next)

/-- Compile-time field/backup/label arguments. No argument depends on w/U. -/
def copyRead (field backup : Stack) (again next : Label) : Statement :=
  widthBranch
    (.pop field captureData
      (.push backup bit (.push 12 (fun _ => true) (jump again))))
    (jump next)

def copyRestore (field backup : Stack) (again next : Label) (tag : Bool) : Statement :=
  .pop backup captureData
    (.branch present
      (.push field bit (.push 10 bit (restoreWidth (jump again))))
      (if tag then .push 10 (fun _ => true) (jump next) else jump next))

/-- Bank10, reversed scanned frontPart0, query2, new value3, keyBackup5,
valueBackup7, width11 and usedWidth12. Labels 0..12 and 14 are macro syntax;
the actual caller begins at label13 after the charged return edge. -/
def program (caller : Statement) (point : Label) : Statement :=
  if point = 0 then
    .pop 10 captureData
      (.branch bit
        (.push 0 (fun _ => true) (.load initializeEqual (jump 1)))
        (.push 10 (fun _ => false) (jump 7)))
  else if point = 1 then
    widthBranch
      (.pop 10 captureData
        (.push 0 bit
          (.pop 2 captureCompare
            (.push 5 bit (.push 12 (fun _ => true) (jump 1))))))
      (jump 2)
  else if point = 2 then
    .pop 5 captureData
      (.branch present
        (.push 2 bit (restoreWidth (jump 2)))
        (.branch equal (jump 3) (jump 5)))
  else if point = 3 then
    widthBranch
      (.pop 10 (fun memory _ => memory)
        (.pop 3 captureData
          (.push 0 bit (.push 7 bit (.push 12 (fun _ => true) (jump 3))))))
      (jump 4)
  else if point = 4 then
    .pop 7 captureData
      (.branch present
        (.push 3 bit (restoreWidth (jump 4)))
        (jump 11))
  else if point = 5 then
    widthBranch
      (.pop 10 captureData
        (.push 0 bit (.push 12 (fun _ => true) (jump 5))))
      (jump 6)
  else if point = 6 then
    .pop 12 captureWidth
      (.branch present (.push 11 (fun _ => true) (jump 6)) (jump 0))
  else if point = 7 then copyRead 3 7 7 8
  else if point = 8 then copyRestore 3 7 8 9 false
  else if point = 9 then copyRead 2 5 9 10
  else if point = 10 then copyRestore 2 5 10 14 false
  else if point = 11 then
    .pop 0 captureData
      (.branch present (.push 10 bit (jump 11)) (jump 12))
  else if point = 12 then jump 13
  else if point = 13 then caller
  else if point = 14 then .push 10 (fun _ => true) (jump 11)
  else .halt

theorem statement_supports (code : Statement) :
    TM2.SupportsStmt (Finset.univ : Finset Label) code := by
  induction code with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ left right => exact ⟨left, right⟩
  | goto _ => intro memory; exact Finset.mem_univ _
  | halt => trivial

theorem supports (caller : Statement) :
    TM2.Supports (program caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _, fun point _ => statement_supports (program caller point)⟩

theorem actual_return (caller : Statement) (memory : Store)
    (slots : Stack → List Bool) :
    TM2.step (program caller) ⟨some 12, memory, slots⟩ =
      some ⟨some 13, memory, slots⟩ := rfl

theorem actual_caller_entry (caller : Statement) (memory : Store)
    (slots : Stack → List Bool) :
    TM2.step (program caller) ⟨some 13, memory, slots⟩ =
      some (TM2.stepAux caller memory slots) := rfl

/-- These are mathematical record descriptors, not finite-control fields. -/
abbrev Record := List Bool × List Bool

def encodeRecords : List Record → List Bool
  | [] => [false]
  | (key, value) :: later => true :: (key ++ value ++ encodeRecords later)

def upsert (query value : List Bool) : List Record → List Record
  | [] => [(query, value)]
  | (key, oldValue) :: later =>
      if key = query then (key, value) :: later else (key, oldValue) :: upsert query value later

def Valid (width : Nat) (records : List Record) : Prop :=
  (∀ record ∈ records, record.1.length = width ∧ record.2.length = width) ∧
    (records.map Prod.fst).Nodup

end PaperProofs.Common.Native.PSTRWordVM.UniqueStore
