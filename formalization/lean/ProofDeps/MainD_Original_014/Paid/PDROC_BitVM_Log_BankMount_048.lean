module

public import Paid.PDROC_BitVM_Log_BankHeader_047

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

namespace PDROC.BitVM.Log.BankMount

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native

/-! Real fixed6/fixed13 input mount CODE. The Bool mode is a compile-time
prepare/core phase choice; both finite code arrays are fixed before input.
No Nat counter, Cell list, host parse/index or readonly-bank substitution is
in sigma. Every old bank/work word is really cleared before actual reading.
This file establishes code/support/dispatch; the complete joined run follows. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Fin 3 ⊕ ((Fin 16 × HeapClear.Label) ⊕ (BankHeader.Label ⊕
  ((Fin 13 × BankFieldRoot.Label) ⊕ (Fin 3 × HeapClear.Label))))
abbrev Store := HeapPointer.Store
abbrev SourceStore := Store × Unit
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store

def fieldCount (core : Bool) : ℕ := if core then 13 else 6

theorem fieldCount_pos (core : Bool) : 0 < fieldCount core := by cases core <;> decide
theorem fieldCount_le (core : Bool) : fieldCount core ≤ 13 := by cases core <;> decide

def footerLabel : Label := .inl 0
def doneLabel : Label := .inl 1
def invalidLabel : Label := .inl 2
def clearLabel (stage : Fin 16) (label : HeapClear.Label) : Label := .inr (.inl (stage, label))
def headerLabel (label : BankHeader.Label) : Label := .inr (.inr (.inl label))
def fieldLabel (field : Fin 13) (label : BankFieldRoot.Label) : Label := .inr (.inr (.inr (.inl (field, label))))
def cleanLabel (stage : Fin 3) (label : HeapClear.Label) : Label := .inr (.inr (.inr (.inr (stage, label))))
def startLabel : Label := clearLabel 0 0

/-- All13 old readonly slots are really cleared, even for the six-field
phase. The three reused work roles are actual clears too. -/
def preSlot (stage : Fin 16) : Stack :=
  if bank : stage.val < 13 then BankDrain.bankSlot ⟨stage.val, bank⟩
  else if stage.val = 13 then 24 else if stage.val = 14 then 25 else 29

def cleanSlot (stage : Fin 3) : Stack := if stage = 0 then 24 else if stage = 1 then 25 else 29

def nextClear (stage : Fin 16) : Label :=
  if next : stage.val + 1 < 16 then clearLabel ⟨stage.val + 1, next⟩ 0 else headerLabel BankHeader.startLabel

def nextField (core : Bool) (field : Fin 13) : Label :=
  if next : field.val + 1 < fieldCount core then
    fieldLabel ⟨field.val + 1, by have bound := fieldCount_le core; omega⟩ BankFieldRoot.startLabel
  else footerLabel

def nextClean (stage : Fin 3) : Label :=
  if next : stage.val + 1 < 3 then cleanLabel ⟨stage.val + 1, next⟩ 0 else doneLabel

def saveFooter (store : SourceStore) (bit : Option Bool) : SourceStore :=
  (((bit, store.1.1.2), store.1.2), store.2)

def footerFlag (store : SourceStore) := store.1.1.1.isSome && store.1.1.1.getD false

def sourceProgram (core : Bool) : Label → TM2.Stmt Alphabet Label SourceStore
  | .inl control => if control = 0 then
      .pop 0 saveFooter (.branch footerFlag (.goto (fun _ => cleanLabel 0 0)) (.goto (fun _ => invalidLabel)))
    else if control = 1 then .load (fun store => (HeapPointer.setTyped store.1 true, store.2)) .halt
    else .load (fun store => (HeapPointer.setTyped store.1 false, store.2)) .halt
  | .inr (.inl (stage, label)) =>
      Inline.statement (τ := Unit) (clearLabel stage) (nextClear stage) (HeapClear.program (preSlot stage) label)
  | .inr (.inr (.inl label)) =>
      Inline.statement (τ := Unit) headerLabel (fieldLabel 0 BankFieldRoot.startLabel) (BankHeader.program label)
  | .inr (.inr (.inr (.inl (field, label)))) =>
      Inline.statement (τ := Unit) (fieldLabel field) (nextField core field) (BankFieldRoot.program field label)
  | .inr (.inr (.inr (.inr (stage, label)))) =>
      Inline.statement (τ := Unit) (cleanLabel stage) (nextClean stage) (HeapClear.program (cleanSlot stage) label)

def program (core : Bool) := StoreIso.machine HeapLoad.storeIso (sourceProgram core)

theorem clear_agrees (core : Bool) (stage : Fin 16) : ∀ label,
    sourceProgram core (clearLabel stage label) =
      Inline.statement (τ := Unit) (clearLabel stage) (nextClear stage) (HeapClear.program (preSlot stage) label) := by
  intro label; rfl

theorem header_agrees (core : Bool) : ∀ label,
    sourceProgram core (headerLabel label) =
      Inline.statement (τ := Unit) headerLabel (fieldLabel 0 BankFieldRoot.startLabel) (BankHeader.program label) := by
  intro label; rfl

theorem field_agrees (core : Bool) (field : Fin 13) : ∀ label,
    sourceProgram core (fieldLabel field label) =
      Inline.statement (τ := Unit) (fieldLabel field) (nextField core field) (BankFieldRoot.program field label) := by
  intro label; rfl

theorem clean_agrees (core : Bool) (stage : Fin 3) : ∀ label,
    sourceProgram core (cleanLabel stage label) =
      Inline.statement (τ := Unit) (cleanLabel stage) (nextClean stage) (HeapClear.program (cleanSlot stage) label) := by
  intro label; rfl

theorem source_supports (core : Bool) : TM2.Supports (sourceProgram core) (Finset.univ : Finset Label) := by
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
    rcases label with control | (⟨stage, clearPart⟩ | (headerPart | (⟨field, bodyPart⟩ | ⟨cleanup, cleanPart⟩)))
    · fin_cases control <;> simp [sourceProgram, TM2.SupportsStmt]
    · exact callClosed (clearLabel stage) (nextClear stage) (HeapClear.program (preSlot stage))
        (HeapClear.supports (preSlot stage)) clearPart
    · exact callClosed headerLabel (fieldLabel 0 BankFieldRoot.startLabel) BankHeader.program BankHeader.supports headerPart
    · exact callClosed (fieldLabel field) (nextField core field) (BankFieldRoot.program field)
        (BankFieldRoot.supports field) bodyPart
    · exact callClosed (cleanLabel cleanup) (nextClean cleanup) (HeapClear.program (cleanSlot cleanup))
        (HeapClear.supports (cleanSlot cleanup)) cleanPart

theorem supports (core : Bool) : TM2.Supports (program core) (Finset.univ : Finset Label) :=
  StoreIso.supports HeapLoad.storeIso (sourceProgram core) (Finset.univ : Finset Label) (source_supports core)

/-- The canonical TRUE footer is REALLY popped. Its caller suffix may contain
arbitrary physical FALSE padding and is not interpreted as another field. -/
theorem footer_step (core : Bool) (store : SourceStore) (suffix : List Bool) (contents : Stack → List Bool) :
    TM2.step (sourceProgram core) (⟨some footerLabel, store, Function.update contents 0 (true :: suffix)⟩ : SourceState) =
      some (⟨some (cleanLabel 0 0), saveFooter store (some true), Function.update contents 0 suffix⟩ : SourceState) := by
  change some (TM2.stepAux (.pop 0 saveFooter (.branch footerFlag
    (.goto (fun _ => cleanLabel 0 0)) (.goto (fun _ => invalidLabel)))) store
      (Function.update contents 0 (true :: suffix))) = _
  simp only [TM2.stepAux, saveFooter, footerFlag,
    Function.update_self, List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.and_true, Bool.cond_true, Function.update_idem]

theorem done_halt (core : Bool) (store : SourceStore) (contents : Stack → List Bool) :
    TM2.step (sourceProgram core) (⟨some doneLabel, store, contents⟩ : SourceState) =
      some (⟨none, (HeapPointer.setTyped store.1 true, store.2), contents⟩ : SourceState) := rfl

theorem invalid_halt (core : Bool) (store : SourceStore) (contents : Stack → List Bool) :
    TM2.step (sourceProgram core) (⟨some invalidLabel, store, contents⟩ : SourceState) =
      some (⟨none, (HeapPointer.setTyped store.1 false, store.2), contents⟩ : SourceState) := rfl

end PDROC.BitVM.Log.BankMount
