module

public import Paid.PDROC_BitVM_Log_InputCopy_058

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

namespace PDROC.BitVM.Log.InputLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native

/-! True readonly-input load CODE. The13 candidate constants, register roles
and prepare/core mode are finite compile-time choices before every input.
The actual pointer stays Bool DATA on query26; each decision reads only the
flag produced by real per-Bool comparison. There is no host Nat index/test. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Fin 3 ⊕ ((Fin 6 × HeapClear.Label) ⊕ (HeapPointer.Label ⊕
  ((Fin 13 × InputLiteral.Label) ⊕ ((Fin 13 × InputCompare.Label) ⊕
    ((Fin 13 × InputCopy.Label) ⊕ (Fin 13 ⊕ HeapClear.Label))))))
abbrev Store := HeapPointer.Store
abbrev SourceStore := Store × Unit
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store

def typeBranch : Label := .inl 0
def doneLabel : Label := .inl 1
def invalidLabel : Label := .inl 2
def clearLabel (stage : Fin 6) (label : HeapClear.Label) : Label := .inr (.inl (stage, label))
def pointerLabel (label : HeapPointer.Label) : Label := .inr (.inr (.inl label))
def literalLabel (field : Fin 13) (label : InputLiteral.Label) : Label := .inr (.inr (.inr (.inl (field, label))))
def compareLabel (field : Fin 13) (label : InputCompare.Label) : Label := .inr (.inr (.inr (.inr (.inl (field, label)))))
def copyLabel (field : Fin 13) (label : InputCopy.Label) : Label := .inr (.inr (.inr (.inr (.inr (.inl (field, label))))))
def decideLabel (field : Fin 13) : Label := .inr (.inr (.inr (.inr (.inr (.inr (.inl field))))))
def cleanLabel (label : HeapClear.Label) : Label := .inr (.inr (.inr (.inr (.inr (.inr (.inr label))))))
def startLabel : Label := clearLabel 0 0
def workSlot (stage : Fin 6) : Stack := ⟨24 + stage.val, by omega⟩

def nextClear (stage : Fin 6) : Label :=
  if next : stage.val + 1 < 6 then clearLabel ⟨stage.val + 1, next⟩ 0 else pointerLabel 0

def nextCandidate (core : Bool) (field : Fin 13) : Label :=
  if next : field.val + 1 < BankMount.fieldCount core then
    literalLabel ⟨field.val + 1, by have bound := BankMount.fieldCount_le core; omega⟩ InputLiteral.startLabel
  else invalidLabel

def sourceProgram (core : Bool) (pointer destination : Register) : Label → TM2.Stmt Alphabet Label SourceStore
  | .inl control => if control = 0 then
      .branch (fun store => Query.equality store.1.2.1)
        (.goto (fun _ => literalLabel 0 InputLiteral.startLabel)) (.goto (fun _ => invalidLabel))
    else if control = 1 then .load (fun store => (HeapPointer.setTyped store.1 true, store.2)) .halt
    else .load (fun store => (HeapPointer.setTyped store.1 false, store.2)) .halt
  | .inr (.inl (stage, label)) =>
      Inline.statement (τ := Unit) (clearLabel stage) (nextClear stage) (HeapClear.program (workSlot stage) label)
  | .inr (.inr (.inl label)) =>
      Inline.statement (τ := Unit) pointerLabel typeBranch (HeapPointer.program pointer label)
  | .inr (.inr (.inr (.inl (field, label)))) =>
      Inline.statement (τ := Unit) (literalLabel field) (compareLabel field InputCompare.startLabel) (InputLiteral.program field label)
  | .inr (.inr (.inr (.inr (.inl (field, label))))) =>
      Inline.statement (τ := Unit) (compareLabel field) (decideLabel field) (InputCompare.program label)
  | .inr (.inr (.inr (.inr (.inr (.inl (field, label)))))) =>
      Inline.statement (τ := Unit) (copyLabel field) (cleanLabel 0) (InputCopy.program field destination label)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl field)))))) =>
      .branch (fun store => Query.equality store.1.2.1)
        (.goto (fun _ => copyLabel field 0)) (.goto (fun _ => nextCandidate core field))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr label)))))) =>
      Inline.statement (τ := Unit) cleanLabel doneLabel (HeapClear.program 26 label)

def program (core : Bool) (pointer destination : Register) :=
  StoreIso.machine HeapLoad.storeIso (sourceProgram core pointer destination)

theorem clear_agrees (core : Bool) (pointer destination : Register) (stage : Fin 6) : ∀ label,
    sourceProgram core pointer destination (clearLabel stage label) =
      Inline.statement (τ := Unit) (clearLabel stage) (nextClear stage) (HeapClear.program (workSlot stage) label) := by
  intro label; rfl

theorem pointer_agrees (core : Bool) (pointer destination : Register) : ∀ label,
    sourceProgram core pointer destination (pointerLabel label) =
      Inline.statement (τ := Unit) pointerLabel typeBranch (HeapPointer.program pointer label) := by intro label; rfl

theorem literal_agrees (core : Bool) (pointer destination : Register) (field : Fin 13) : ∀ label,
    sourceProgram core pointer destination (literalLabel field label) =
      Inline.statement (τ := Unit) (literalLabel field) (compareLabel field InputCompare.startLabel) (InputLiteral.program field label) := by
  intro label; rfl

theorem compare_agrees (core : Bool) (pointer destination : Register) (field : Fin 13) : ∀ label,
    sourceProgram core pointer destination (compareLabel field label) =
      Inline.statement (τ := Unit) (compareLabel field) (decideLabel field) (InputCompare.program label) := by intro label; rfl

theorem copy_agrees (core : Bool) (pointer destination : Register) (field : Fin 13) : ∀ label,
    sourceProgram core pointer destination (copyLabel field label) =
      Inline.statement (τ := Unit) (copyLabel field) (cleanLabel 0) (InputCopy.program field destination label) := by intro label; rfl

theorem clean_agrees (core : Bool) (pointer destination : Register) : ∀ label,
    sourceProgram core pointer destination (cleanLabel label) =
      Inline.statement (τ := Unit) cleanLabel doneLabel (HeapClear.program 26 label) := by intro label; rfl

theorem source_supports (core : Bool) (pointer destination : Register) :
    TM2.Supports (sourceProgram core pointer destination) (Finset.univ : Finset Label) := by
  have callClosed {Local : Type} [Fintype Local] [Inhabited Local] (labels : Local → Label) (ret : Label)
      (source : Local → TM2.Stmt Alphabet Local Store) (closed : TM2.Supports source (Finset.univ : Finset Local))
      (label : Local) : TM2.SupportsStmt (Finset.univ : Finset Label)
        (Inline.statement (τ := Unit) labels ret (source label)) := by
    apply Inline.supports_statement labels ret (Finset.univ : Finset Local) (Finset.univ : Finset Label)
    · intro index _; exact Finset.mem_univ _
    · exact Finset.mem_univ _
    · exact closed.2 label (Finset.mem_univ _)
  constructor
  · exact Finset.mem_univ _
  · intro label _
    rcases label with control | (⟨stage, clearPart⟩ | (pointerPart | (⟨field, literalPart⟩ |
      (⟨compareField, comparePart⟩ | (⟨copyField, copyPart⟩ | (decision | cleanPart))))))
    · fin_cases control <;> simp [sourceProgram, TM2.SupportsStmt]
    · exact callClosed (clearLabel stage) (nextClear stage) (HeapClear.program (workSlot stage))
        (HeapClear.supports (workSlot stage)) clearPart
    · exact callClosed pointerLabel typeBranch (HeapPointer.program pointer) (HeapPointer.supports pointer) pointerPart
    · exact callClosed (literalLabel field) (compareLabel field InputCompare.startLabel) (InputLiteral.program field)
        (InputLiteral.supports field) literalPart
    · exact callClosed (compareLabel compareField) (decideLabel compareField) InputCompare.program InputCompare.supports comparePart
    · exact callClosed (copyLabel copyField) (cleanLabel 0) (InputCopy.program copyField destination)
        (InputCopy.supports copyField destination) copyPart
    · simp [sourceProgram, TM2.SupportsStmt]
    · exact callClosed cleanLabel doneLabel (HeapClear.program 26) (HeapClear.supports 26) cleanPart

theorem supports (core : Bool) (pointer destination : Register) :
    TM2.Supports (program core pointer destination) (Finset.univ : Finset Label) :=
  StoreIso.supports HeapLoad.storeIso (sourceProgram core pointer destination) (Finset.univ : Finset Label)
    (source_supports core pointer destination)

theorem type_step (core : Bool) (pointer destination : Register) (store : SourceStore) (contents : Stack → List Bool)
    (typed : Query.equality store.1.2.1 = true) :
    TM2.step (sourceProgram core pointer destination) (⟨some typeBranch, store, contents⟩ : SourceState) =
      some (⟨some (literalLabel 0 InputLiteral.startLabel), store, contents⟩ : SourceState) := by
  change some (TM2.stepAux (.branch (fun store : SourceStore => Query.equality store.1.2.1)
    (.goto (fun _ => literalLabel 0 InputLiteral.startLabel)) (.goto (fun _ => invalidLabel))) store contents) = _
  simp only [TM2.stepAux, typed, Bool.cond_true]

theorem type_invalid (core : Bool) (pointer destination : Register) (store : SourceStore) (contents : Stack → List Bool)
    (typed : Query.equality store.1.2.1 = false) :
    TM2.step (sourceProgram core pointer destination) (⟨some typeBranch, store, contents⟩ : SourceState) =
      some (⟨some invalidLabel, store, contents⟩ : SourceState) := by
  change some (TM2.stepAux (.branch (fun store : SourceStore => Query.equality store.1.2.1)
    (.goto (fun _ => literalLabel 0 InputLiteral.startLabel)) (.goto (fun _ => invalidLabel))) store contents) = _
  simp only [TM2.stepAux, typed, Bool.cond_false]

theorem matched_step (core : Bool) (pointer destination : Register) (field : Fin 13)
    (store : SourceStore) (contents : Stack → List Bool) (matched : Query.equality store.1.2.1 = true) :
    TM2.step (sourceProgram core pointer destination) (⟨some (decideLabel field), store, contents⟩ : SourceState) =
      some (⟨some (copyLabel field 0), store, contents⟩ : SourceState) := by
  change some (TM2.stepAux (.branch (fun store : SourceStore => Query.equality store.1.2.1)
    (.goto (fun _ => copyLabel field 0)) (.goto (fun _ => nextCandidate core field))) store contents) = _
  simp only [TM2.stepAux, matched, Bool.cond_true]

theorem unmatched_step (core : Bool) (pointer destination : Register) (field : Fin 13)
    (store : SourceStore) (contents : Stack → List Bool) (unmatched : Query.equality store.1.2.1 = false) :
    TM2.step (sourceProgram core pointer destination) (⟨some (decideLabel field), store, contents⟩ : SourceState) =
      some (⟨some (nextCandidate core field), store, contents⟩ : SourceState) := by
  change some (TM2.stepAux (.branch (fun store : SourceStore => Query.equality store.1.2.1)
    (.goto (fun _ => copyLabel field 0)) (.goto (fun _ => nextCandidate core field))) store contents) = _
  simp only [TM2.stepAux, unmatched, Bool.cond_false]

theorem done_halt (core : Bool) (pointer destination : Register) (store : SourceStore) (contents : Stack → List Bool) :
    TM2.step (sourceProgram core pointer destination) (⟨some doneLabel, store, contents⟩ : SourceState) =
      some (⟨none, (HeapPointer.setTyped store.1 true, store.2), contents⟩ : SourceState) := rfl

theorem invalid_halt (core : Bool) (pointer destination : Register) (store : SourceStore) (contents : Stack → List Bool) :
    TM2.step (sourceProgram core pointer destination) (⟨some invalidLabel, store, contents⟩ : SourceState) =
      some (⟨none, (HeapPointer.setTyped store.1 false, store.2), contents⟩ : SourceState) := rfl

end PDROC.BitVM.Log.InputLoad
