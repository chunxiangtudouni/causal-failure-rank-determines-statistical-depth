module

public import Paid.PDROC_BitVM_Log_HeapClear_019
public import Paid.PDROC_BitVM_Log_HeapPointer_015
public import Paid.PDROC_BitVM_Log_HeapPrepend_018

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Log.HeapRelease

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native

/-! The actual release opcode control: clear24/25/26, read the pointer from
its real register, branch on its actual type flag and prepend a tombstone.
All28 control labels and108 finite store states are fixed before the input. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Fin 3 ⊕ ((Fin 3 × HeapClear.Label) ⊕ (HeapPointer.Label ⊕ HeapPrepend.Label))
abbrev SourceStore := HeapPointer.Store × Unit
abbrev Store := HeapPointer.Store
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store

def branchLabel : Label := .inl 0
def doneLabel : Label := .inl 1
def invalidLabel : Label := .inl 2
def clearLabel (phase : Fin 3) (label : HeapClear.Label) : Label := .inr (.inl (phase, label))
def pointerLabel (label : HeapPointer.Label) : Label := .inr (.inr (.inl label))
def prependLabel (label : HeapPrepend.Label) : Label := .inr (.inr (.inr label))
def startLabel : Label := clearLabel 0 0
def workSlot (phase : Fin 3) : Stack := ⟨24 + phase.val, by omega⟩
def nextClear (phase : Fin 3) : Label :=
  if next : phase.val + 1 < 3 then clearLabel ⟨phase.val + 1, next⟩ 0 else pointerLabel 0

def sourceProgram (pointer : Register) : Label → TM2.Stmt Alphabet Label SourceStore
  | .inl control => if control = 0 then
      .branch (fun store => Query.equality store.1.2.1)
        (.goto (fun _ => prependLabel HeapPrepend.startLabel)) (.goto (fun _ => invalidLabel))
      else .halt
  | .inr (.inl (phase, label)) =>
      Inline.statement (τ := Unit) (clearLabel phase) (nextClear phase) (HeapClear.program (workSlot phase) label)
  | .inr (.inr (.inl label)) =>
      Inline.statement (τ := Unit) pointerLabel branchLabel (HeapPointer.program pointer label)
  | .inr (.inr (.inr label)) =>
      Inline.statement (τ := Unit) prependLabel doneLabel (HeapPrepend.program false label)

def storeIso : SourceStore ≃ Store where
  toFun := Prod.fst
  invFun := fun store => (store, ())
  left_inv := by intro store; rcases store with ⟨data, marker⟩; cases marker; rfl
  right_inv := by intro store; rfl

def program (pointer : Register) := StoreIso.machine storeIso (sourceProgram pointer)

theorem clear_agrees (pointer : Register) (phase : Fin 3) : ∀ label,
    sourceProgram pointer (clearLabel phase label) =
      Inline.statement (τ := Unit) (clearLabel phase) (nextClear phase) (HeapClear.program (workSlot phase) label) := by
  intro label; rfl

theorem pointer_agrees (pointer : Register) : ∀ label,
    sourceProgram pointer (pointerLabel label) =
      Inline.statement (τ := Unit) pointerLabel branchLabel (HeapPointer.program pointer label) := by
  intro label; rfl

theorem prepend_agrees (pointer : Register) : ∀ label,
    sourceProgram pointer (prependLabel label) =
      Inline.statement (τ := Unit) prependLabel doneLabel (HeapPrepend.program false label) := by
  intro label; rfl

theorem source_supports (pointer : Register) : TM2.Supports (sourceProgram pointer) (Finset.univ : Finset Label) := by
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
    rcases label with control | (⟨phase, localLabel⟩ | (pointerPhase | prependPhase))
    · fin_cases control <;> simp [sourceProgram, TM2.SupportsStmt]
    · exact callClosed (clearLabel phase) (nextClear phase) (HeapClear.program (workSlot phase))
        (HeapClear.supports (workSlot phase)) localLabel
    · exact callClosed pointerLabel branchLabel (HeapPointer.program pointer) (HeapPointer.supports pointer) pointerPhase
    · exact callClosed prependLabel doneLabel (HeapPrepend.program false) (HeapPrepend.supports false) prependPhase

theorem supports (pointer : Register) : TM2.Supports (program pointer) (Finset.univ : Finset Label) :=
  StoreIso.supports storeIso (sourceProgram pointer) (Finset.univ : Finset Label) (source_supports pointer)

theorem branch_nat (pointer : Register) (store : SourceStore) (contents : Stack → List Bool)
    (typed : Query.equality store.1.2.1 = true) :
    TM2.step (sourceProgram pointer) (⟨some branchLabel, store, contents⟩ : SourceState) =
      some (⟨some (prependLabel HeapPrepend.startLabel), store, contents⟩ : SourceState) := by
  change some (TM2.stepAux (.branch (fun store : SourceStore => Query.equality store.1.2.1)
    (.goto (fun _ => prependLabel HeapPrepend.startLabel)) (.goto (fun _ => invalidLabel))) store contents) = _
  simp only [TM2.stepAux, typed, Bool.cond_true]

theorem branch_invalid (pointer : Register) (store : SourceStore) (contents : Stack → List Bool)
    (typed : Query.equality store.1.2.1 = false) :
    TM2.step (sourceProgram pointer) (⟨some branchLabel, store, contents⟩ : SourceState) =
      some (⟨some invalidLabel, store, contents⟩ : SourceState) := by
  change some (TM2.stepAux (.branch (fun store : SourceStore => Query.equality store.1.2.1)
    (.goto (fun _ => prependLabel HeapPrepend.startLabel)) (.goto (fun _ => invalidLabel))) store contents) = _
  simp only [TM2.stepAux, typed, Bool.cond_false]

theorem done_halt (pointer : Register) (store : SourceStore) (contents : Stack → List Bool) :
    TM2.step (sourceProgram pointer) (⟨some doneLabel, store, contents⟩ : SourceState) =
      some (⟨none, store, contents⟩ : SourceState) := rfl

theorem invalid_halt (pointer : Register) (store : SourceStore) (contents : Stack → List Bool) :
    TM2.step (sourceProgram pointer) (⟨some invalidLabel, store, contents⟩ : SourceState) =
      some (⟨none, store, contents⟩ : SourceState) := rfl

end PDROC.BitVM.Log.HeapRelease
