module

public import Paid.PDROC_BitVM_Log_HeapLookup_032
public import Paid.PDROC_BitVM_Log_HeapRelease_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.Log.HeapLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native

/-! Real load code. Six actual pre-clears produce the lookup entry buffers;
pointer type and live/latest-tombstone status are separate actual branches.
Only a successful actual lookup commits result28 to the destination register.
Actual post-clears remove query26/result28; no FALSEpadding is treated empty. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Fin 4 ⊕ ((Fin 6 × HeapClear.Label) ⊕ (HeapPointer.Label ⊕
  (HeapLookup.Label ⊕ (HeapTransfer.Label ⊕ (Fin 2 × HeapClear.Label)))))
abbrev SourceStore := HeapPointer.Store × Unit
abbrev Store := HeapPointer.Store
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store

def typeBranch : Label := .inl 0
def valueBranch : Label := .inl 1
def doneLabel : Label := .inl 2
def invalidLabel : Label := .inl 3
def clearLabel (phase : Fin 6) (label : HeapClear.Label) : Label := .inr (.inl (phase, label))
def pointerLabel (label : HeapPointer.Label) : Label := .inr (.inr (.inl label))
def lookupLabel (label : HeapLookup.Label) : Label := .inr (.inr (.inr (.inl label)))
def transferLabel (label : HeapTransfer.Label) : Label := .inr (.inr (.inr (.inr (.inl label))))
def postLabel (phase : Fin 2) (label : HeapClear.Label) : Label := .inr (.inr (.inr (.inr (.inr (phase, label)))))
def startLabel : Label := clearLabel 0 0
def workSlot (phase : Fin 6) : Stack := ⟨24 + phase.val, by omega⟩
def postSlot (phase : Fin 2) : Stack := if phase = 0 then 26 else 28
def nextClear (phase : Fin 6) : Label :=
  if next : phase.val + 1 < 6 then clearLabel ⟨phase.val + 1, next⟩ 0 else pointerLabel 0
def nextPost (phase : Fin 2) : Label := if phase = 0 then postLabel 1 0 else doneLabel

def sourceProgram (pointer destination : Register) : Label → TM2.Stmt Alphabet Label SourceStore
  | .inl control => if control = 0 then
      .branch (fun store => Query.equality store.1.2.1)
        (.goto (fun _ => lookupLabel HeapLookup.startLabel)) (.goto (fun _ => invalidLabel))
      else if control = 1 then
        .branch (fun store => Query.equality store.1.2.1 && Query.recordTag store.1.2.1)
          (.goto (fun _ => transferLabel 0)) (.goto (fun _ => invalidLabel))
      else if control = 2 then .load (fun store => (HeapPointer.setTyped store.1 true, store.2)) .halt
      else .load (fun store => (HeapPointer.setTyped store.1 false, store.2)) .halt
  | .inr (.inl (phase, label)) =>
      Inline.statement (τ := Unit) (clearLabel phase) (nextClear phase) (HeapClear.program (workSlot phase) label)
  | .inr (.inr (.inl label)) =>
      Inline.statement (τ := Unit) pointerLabel typeBranch (HeapPointer.program pointer label)
  | .inr (.inr (.inr (.inl label))) =>
      Inline.statement (τ := Unit) lookupLabel valueBranch (HeapLookup.program label)
  | .inr (.inr (.inr (.inr (.inl label)))) =>
      Inline.statement (τ := Unit) transferLabel (postLabel 0 0) (HeapTransfer.program true destination label)
  | .inr (.inr (.inr (.inr (.inr (phase, label))))) =>
      Inline.statement (τ := Unit) (postLabel phase) (nextPost phase) (HeapClear.program (postSlot phase) label)

def storeIso : SourceStore ≃ Store where
  toFun := Prod.fst
  invFun := fun store => (store, ())
  left_inv := by intro store; rcases store with ⟨data, marker⟩; cases marker; rfl
  right_inv := by intro store; rfl

def program (pointer destination : Register) := StoreIso.machine storeIso (sourceProgram pointer destination)

theorem clear_agrees (pointer destination : Register) (phase : Fin 6) : ∀ label,
    sourceProgram pointer destination (clearLabel phase label) =
      Inline.statement (τ := Unit) (clearLabel phase) (nextClear phase) (HeapClear.program (workSlot phase) label) := by
  intro label; rfl

theorem pointer_agrees (pointer destination : Register) : ∀ label,
    sourceProgram pointer destination (pointerLabel label) =
      Inline.statement (τ := Unit) pointerLabel typeBranch (HeapPointer.program pointer label) := by
  intro label; rfl

theorem lookup_agrees (pointer destination : Register) : ∀ label,
    sourceProgram pointer destination (lookupLabel label) =
      Inline.statement (τ := Unit) lookupLabel valueBranch (HeapLookup.program label) := by
  intro label; rfl

theorem transfer_agrees (pointer destination : Register) : ∀ label,
    sourceProgram pointer destination (transferLabel label) =
      Inline.statement (τ := Unit) transferLabel (postLabel 0 0) (HeapTransfer.program true destination label) := by
  intro label; rfl

theorem post_agrees (pointer destination : Register) (phase : Fin 2) : ∀ label,
    sourceProgram pointer destination (postLabel phase label) =
      Inline.statement (τ := Unit) (postLabel phase) (nextPost phase) (HeapClear.program (postSlot phase) label) := by
  intro label; rfl

theorem source_supports (pointer destination : Register) :
    TM2.Supports (sourceProgram pointer destination) (Finset.univ : Finset Label) := by
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
    rcases label with control | (⟨phase, localLabel⟩ | (pointerPhase | (lookupPhase | (transferPhase | ⟨postPhase, postLocal⟩))))
    · fin_cases control <;> simp [sourceProgram, TM2.SupportsStmt]
    · exact callClosed (clearLabel phase) (nextClear phase) (HeapClear.program (workSlot phase))
        (HeapClear.supports (workSlot phase)) localLabel
    · exact callClosed pointerLabel typeBranch (HeapPointer.program pointer) (HeapPointer.supports pointer) pointerPhase
    · exact callClosed lookupLabel valueBranch HeapLookup.program HeapLookup.supports lookupPhase
    · exact callClosed transferLabel (postLabel 0 0) (HeapTransfer.program true destination)
        (HeapTransfer.supports true destination) transferPhase
    · exact callClosed (postLabel postPhase) (nextPost postPhase) (HeapClear.program (postSlot postPhase))
        (HeapClear.supports (postSlot postPhase)) postLocal

theorem supports (pointer destination : Register) :
    TM2.Supports (program pointer destination) (Finset.univ : Finset Label) :=
  StoreIso.supports storeIso (sourceProgram pointer destination) (Finset.univ : Finset Label) (source_supports pointer destination)

theorem type_step (pointer destination : Register) (store : SourceStore) (contents : Stack → List Bool)
    (typed : Query.equality store.1.2.1 = true) :
    TM2.step (sourceProgram pointer destination) (⟨some typeBranch, store, contents⟩ : SourceState) =
      some (⟨some (lookupLabel HeapLookup.startLabel), store, contents⟩ : SourceState) := by
  change some (TM2.stepAux (.branch (fun store : SourceStore => Query.equality store.1.2.1)
    (.goto (fun _ => lookupLabel HeapLookup.startLabel)) (.goto (fun _ => invalidLabel))) store contents) = _
  simp only [TM2.stepAux, typed, Bool.cond_true]

theorem type_invalid (pointer destination : Register) (store : SourceStore) (contents : Stack → List Bool)
    (typed : Query.equality store.1.2.1 = false) :
    TM2.step (sourceProgram pointer destination) (⟨some typeBranch, store, contents⟩ : SourceState) =
      some (⟨some invalidLabel, store, contents⟩ : SourceState) := by
  change some (TM2.stepAux (.branch (fun store : SourceStore => Query.equality store.1.2.1)
    (.goto (fun _ => lookupLabel HeapLookup.startLabel)) (.goto (fun _ => invalidLabel))) store contents) = _
  simp only [TM2.stepAux, typed, Bool.cond_false]

theorem value_step (pointer destination : Register) (store : SourceStore) (contents : Stack → List Bool)
    (found : (Query.equality store.1.2.1 && Query.recordTag store.1.2.1) = true) :
    TM2.step (sourceProgram pointer destination) (⟨some valueBranch, store, contents⟩ : SourceState) =
      some (⟨some (transferLabel 0), store, contents⟩ : SourceState) := by
  change some (TM2.stepAux (.branch (fun store : SourceStore => Query.equality store.1.2.1 && Query.recordTag store.1.2.1)
    (.goto (fun _ => transferLabel 0)) (.goto (fun _ => invalidLabel))) store contents) = _
  simp only [TM2.stepAux, found, Bool.cond_true]

theorem value_invalid (pointer destination : Register) (store : SourceStore) (contents : Stack → List Bool)
    (missing : (Query.equality store.1.2.1 && Query.recordTag store.1.2.1) = false) :
    TM2.step (sourceProgram pointer destination) (⟨some valueBranch, store, contents⟩ : SourceState) =
      some (⟨some invalidLabel, store, contents⟩ : SourceState) := by
  change some (TM2.stepAux (.branch (fun store : SourceStore => Query.equality store.1.2.1 && Query.recordTag store.1.2.1)
    (.goto (fun _ => transferLabel 0)) (.goto (fun _ => invalidLabel))) store contents) = _
  simp only [TM2.stepAux, missing, Bool.cond_false]

theorem done_halt (pointer destination : Register) (store : SourceStore) (contents : Stack → List Bool) :
    TM2.step (sourceProgram pointer destination) (⟨some doneLabel, store, contents⟩ : SourceState) =
      some (⟨none, (HeapPointer.setTyped store.1 true, store.2), contents⟩ : SourceState) := rfl

theorem invalid_halt (pointer destination : Register) (store : SourceStore) (contents : Stack → List Bool) :
    TM2.step (sourceProgram pointer destination) (⟨some invalidLabel, store, contents⟩ : SourceState) =
      some (⟨none, (HeapPointer.setTyped store.1 false, store.2), contents⟩ : SourceState) := rfl

end PDROC.BitVM.Log.HeapLoad
