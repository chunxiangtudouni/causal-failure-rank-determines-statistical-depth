module

public import Paid.PDROC_BitVM_Log_HeapPointer_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Log.HeapPrepend

open Turing
open PDROC.BitVM.Native

/-! Real store/release record construction. The opcode Bool is a fixed
compile-time choice; address and Cell remain physical Bool stack data.
Seed25, actual address26->25, optional actual Cell28->25, then25->heap21.
No host encoder, heap update or record list appears in transition control. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Fin 2 ⊕ (Drain.Label ⊕ (Drain.Label ⊕ Drain.Label))
abbrev Extra := Kernel.NatMarshal.Store × Unit
abbrev SourceStore := Query.Store × Extra
abbrev Store := HeapPointer.Store
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store
abbrev DrainState := TM2.Cfg Alphabet Drain.Label Query.Store
abbrev Statement := TM2.Stmt Alphabet Label SourceStore

def startLabel : Label := .inl 0
def doneLabel : Label := .inl 1
def addressLabel (label : Drain.Label) : Label := .inr (.inl label)
def cellLabel (label : Drain.Label) : Label := .inr (.inr (.inl label))
def historyLabel (label : Drain.Label) : Label := .inr (.inr (.inr label))

def addressEmbedding : Drain.Stack ↪ Stack where
  toFun := fun index => if index = 0 then 0 else if index = 1 then 24
    else if index = 2 then 27 else if index = 3 then 28 else if index = 4 then 29
    else if index = 5 then 25 else 26
  inj' := by
    intro left right same
    fin_cases left <;> fin_cases right <;> simp_all

def cellEmbedding : Drain.Stack ↪ Stack where
  toFun := fun index => if index = 0 then 0 else if index = 1 then 24
    else if index = 2 then 26 else if index = 3 then 27 else if index = 4 then 29
    else if index = 5 then 25 else 28
  inj' := by
    intro left right same
    fin_cases left <;> fin_cases right <;> simp_all

def addressSource := Lift.machine addressEmbedding (Drain.program true)
def cellSource := Lift.machine cellEmbedding (Drain.program true)
def historySource := Lift.machine Lookup.heapWorkEmbed (Drain.program false)

def code (labels : Drain.Label → Label) (ret : Label)
    (source : Drain.Label → TM2.Stmt Alphabet Drain.Label Query.Store) (label : Drain.Label) : Statement :=
  Inline.statement (τ := Extra) labels ret (source label)

def sourceProgram (stored : Bool) : Label → Statement
  | .inl control => if control = 0 then .push 25 (fun _ => stored) (.goto (fun _ => addressLabel 0)) else .halt
  | .inr (.inl label) => code addressLabel (if stored then cellLabel 0 else historyLabel 0) addressSource label
  | .inr (.inr (.inl label)) => code cellLabel (historyLabel 0) cellSource label
  | .inr (.inr (.inr label)) => code historyLabel doneLabel historySource label

/-- Fixed finite product reordering only, using existing StoreIso execution
transport. All108 flag states and their old values have a true inverse. -/
def storeIso : SourceStore ≃ Store where
  toFun := fun store => (store.2.1, (store.1, store.2.2))
  invFun := fun store => (store.2.1, (store.1, store.2.2))
  left_inv := by intro store; rfl
  right_inv := by intro store; rfl

def program (stored : Bool) := StoreIso.machine storeIso (sourceProgram stored)

def sourceState (label : Option Label) (store : SourceStore) (contents : Stack → List Bool) : SourceState :=
  ⟨label, store, contents⟩

theorem source_supports (stored : Bool) : TM2.Supports (sourceProgram stored) (Finset.univ : Finset Label) := by
  have closedAddress := Lift.supports addressEmbedding (Drain.program true)
    (Finset.univ : Finset Drain.Label) (Drain.supports true)
  have closedCell := Lift.supports cellEmbedding (Drain.program true)
    (Finset.univ : Finset Drain.Label) (Drain.supports true)
  have closedHistory := Lift.supports Lookup.heapWorkEmbed (Drain.program false)
    (Finset.univ : Finset Drain.Label) (Drain.supports false)
  have callClosed (labels : Drain.Label → Label) (ret : Label)
      (source : Drain.Label → TM2.Stmt Alphabet Drain.Label Query.Store)
      (closed : TM2.Supports source (Finset.univ : Finset Drain.Label)) (label : Drain.Label) :
      TM2.SupportsStmt (Finset.univ : Finset Label) (code labels ret source label) := by
    apply Inline.supports_statement labels ret (Finset.univ : Finset Drain.Label) (Finset.univ : Finset Label)
    · intro index _; exact Finset.mem_univ _
    · exact Finset.mem_univ _
    · exact closed.2 label (Finset.mem_univ _)
  constructor
  · exact Finset.mem_univ _
  · intro label _
    rcases label with control | (address | (cell | history))
    · fin_cases control <;> simp [sourceProgram, TM2.SupportsStmt]
    · exact callClosed addressLabel (if stored then cellLabel 0 else historyLabel 0) addressSource closedAddress address
    · exact callClosed cellLabel (historyLabel 0) cellSource closedCell cell
    · exact callClosed historyLabel doneLabel historySource closedHistory history

theorem supports (stored : Bool) : TM2.Supports (program stored) (Finset.univ : Finset Label) :=
  StoreIso.supports storeIso (sourceProgram stored) (Finset.univ : Finset Label) (source_supports stored)

theorem seed_step (stored : Bool) (store : SourceStore) (contents : Stack → List Bool) :
    TM2.step (sourceProgram stored) (sourceState (some startLabel) store contents) =
      some (sourceState (some (addressLabel 0)) store (Function.update contents 25 (stored :: contents 25))) := rfl

theorem done_halt (stored : Bool) (store : SourceStore) (contents : Stack → List Bool) :
    TM2.step (sourceProgram stored) (sourceState (some doneLabel) store contents) =
      some (sourceState none store contents) := rfl

theorem halted (stored : Bool) (store : SourceStore) (contents : Stack → List Bool) :
    TM2.step (sourceProgram stored) (sourceState none store contents) = none := rfl

theorem address_projection (contents : Stack → List Bool) (store : Query.Store) :
    Lift.cfg addressEmbedding (⟨some 0, store, contents⟩ : DrainState) =
      Drain.state true (some 0) store (contents 26) (contents 25)
        (fun index => contents (addressEmbedding index)) := by
  have data : Lift.slots addressEmbedding contents = Drain.slots true (contents 26) (contents 25)
      (fun index => contents (addressEmbedding index)) := by
    funext index
    fin_cases index <;> rfl
  exact congrArg (fun current => (⟨some 0, store, current⟩ : Drain.State)) data

theorem cell_projection (contents : Stack → List Bool) (store : Query.Store) :
    Lift.cfg cellEmbedding (⟨some 0, store, contents⟩ : DrainState) =
      Drain.state true (some 0) store (contents 28) (contents 25)
        (fun index => contents (cellEmbedding index)) := by
  have data : Lift.slots cellEmbedding contents = Drain.slots true (contents 28) (contents 25)
      (fun index => contents (cellEmbedding index)) := by
    funext index
    fin_cases index <;> rfl
  exact congrArg (fun current => (⟨some 0, store, current⟩ : Drain.State)) data

theorem history_projection (contents : Stack → List Bool) (store : Query.Store) :
    Lift.cfg Lookup.heapWorkEmbed (⟨some 0, store, contents⟩ : DrainState) =
      Drain.state false (some 0) store (contents 25) (contents 21)
        (fun index => contents (Lookup.heapWorkEmbed index)) := by
  have data : Lift.slots Lookup.heapWorkEmbed contents = Drain.slots false (contents 25) (contents 21)
      (fun index => contents (Lookup.heapWorkEmbed index)) := by
    funext index
    fin_cases index <;> rfl
  exact congrArg (fun current => (⟨some 0, store, current⟩ : Drain.State)) data

end PDROC.BitVM.Log.HeapPrepend
