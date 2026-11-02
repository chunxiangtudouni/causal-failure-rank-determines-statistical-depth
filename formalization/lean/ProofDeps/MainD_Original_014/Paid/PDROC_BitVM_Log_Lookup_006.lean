module

public import Paid.PDROC_BitVM_Log_Capture_008
public import Paid.PDROC_BitVM_Log_Query_006
public import Paid.PDROC_BitVM_Log_CellSkip_002
public import Paid.PDROC_BitVM_Log_CellCopy_004
public import Paid.PDROC_BitVM_Log_Drain_005
public import Paid.PDROC_BitVM_Log_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

/-! One fixed finite heap-query program. Logical address/Cell/event lists
are absent from its control store. It scans actual newest-first record bits,
captures the address field, compares real Bool words and restores the query.
Matched tombstone goes straight to history restoration; only unmatched stores
skip a real Cell. A matched store copies real Cell bytes before restoration.
This module defines real code/individual dispatch edges, not yet its full run. -/

namespace PDROC.BitVM.Log.Lookup

open Turing

abbrev Stack := Query.Stack
abbrev Label := Fin 4 ⊕ (Capture.Label ⊕ (Query.Label ⊕
  (CellSkip.Label ⊕ (CellCopy.Label ⊕ (Drain.Label ⊕ Drain.Label)))))
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Query.Store × Unit
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def gateLabel : Label := .inl 0
def decideLabel : Label := .inl 1
def doneLabel : Label := .inl 2
def invalidLabel : Label := .inl 3
def captureLabel (label : Capture.Label) : Label := .inr (.inl label)
def compareLabel (label : Query.Label) : Label := .inr (.inr (.inl label))
def skipLabel (label : CellSkip.Label) : Label := .inr (.inr (.inr (.inl label)))
def copyLabel (label : CellCopy.Label) : Label := .inr (.inr (.inr (.inr (.inl label))))
def valueLabel (label : Drain.Label) : Label := .inr (.inr (.inr (.inr (.inr (.inl label)))))
def historyLabel (label : Drain.Label) : Label := .inr (.inr (.inr (.inr (.inr (.inr label)))))

def setRecord (store : Store) (symbol : Option Bool) : Store :=
  (Query.setRecord store.1 symbol, store.2)

def setTag (store : Store) (tag : Bool) : Store :=
  ((store.1.1, (store.1.2.1, (store.1.2.2.1, tag))), store.2)

def missing (store : Store) : Store :=
  (Query.setEquality (setTag store false).1 false, store.2)

def gateCode : Statement :=
  .pop 0 setRecord
    (.branch (fun store => store.1.1.isSome)
      (.push 2 (fun store => store.1.1.getD false)
        (.load (fun store => setTag store (store.1.1.getD false))
          (.goto (fun _ => captureLabel 0))))
      (.load missing (.goto (fun _ => historyLabel 0))))

def decideCode : Statement :=
  .branch (fun store => Query.equality store.1)
    (.branch (fun store => Query.recordTag store.1)
      (.goto (fun _ => copyLabel CellCopy.startLabel))
      (.goto (fun _ => historyLabel 0)))
    (.branch (fun store => Query.recordTag store.1)
      (.goto (fun _ => skipLabel CellSkip.startLabel))
      (.goto (fun _ => gateLabel)))

def callee {Local : Type} (labels : Local → Label) (returnLabel : Label)
    (source : Local → TM2.Stmt Alphabet Local Query.Store) (label : Local) : Statement :=
  Native.Inline.statement (τ := Unit) labels returnLabel (source label)

def program : Label → Statement
  | .inl control => if control = 0 then gateCode else if control = 1 then decideCode else .halt
  | .inr (.inl label) => callee captureLabel (compareLabel 0) Capture.program label
  | .inr (.inr (.inl label)) => callee compareLabel decideLabel Query.program label
  | .inr (.inr (.inr (.inl label))) => callee skipLabel gateLabel CellSkip.program label
  | .inr (.inr (.inr (.inr (.inl label)))) => callee copyLabel (valueLabel 0) CellCopy.program label
  | .inr (.inr (.inr (.inr (.inr (.inl label))))) =>
      callee valueLabel (historyLabel 0) (Drain.program true) label
  | .inr (.inr (.inr (.inr (.inr (.inr label))))) =>
      callee historyLabel doneLabel (Drain.program false) label

theorem callee_supports {Local : Type} [Fintype Local]
    (labels : Local → Label) (returnLabel : Label)
    (source : Local → TM2.Stmt Alphabet Local Query.Store) (label : Local)
    (closed : ∀ index, TM2.SupportsStmt (Finset.univ : Finset Local) (source index)) :
    TM2.SupportsStmt (Finset.univ : Finset Label) (callee labels returnLabel source label) := by
  apply Native.Inline.supports_statement labels returnLabel
    (Finset.univ : Finset Local) (Finset.univ : Finset Label)
  · intro index _; exact Finset.mem_univ _
  · exact Finset.mem_univ _
  · exact closed label

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    rcases label with control | (capture | (compare | (skip | (copy | (value | history)))))
    · fin_cases control <;> simp [program, gateCode, decideCode, TM2.SupportsStmt]
    · exact callee_supports captureLabel (compareLabel 0) Capture.program capture
        (fun index => Capture.supports.2 index (Finset.mem_univ _))
    · exact callee_supports compareLabel decideLabel Query.program compare
        (fun index => Query.supports.2 index (Finset.mem_univ _))
    · exact callee_supports skipLabel gateLabel CellSkip.program skip
        (fun index => CellSkip.supports.2 index (Finset.mem_univ _))
    · exact callee_supports copyLabel (valueLabel 0) CellCopy.program copy
        (fun index => CellCopy.supports.2 index (Finset.mem_univ _))
    · exact callee_supports valueLabel (historyLabel 0) (Drain.program true) value
        (fun index => (Drain.supports true).2 index (Finset.mem_univ _))
    · exact callee_supports historyLabel doneLabel (Drain.program false) history
        (fun index => (Drain.supports false).2 index (Finset.mem_univ _))

def slots (input archive query result : List Bool) : Stack → List Bool :=
  fun index => if index = 0 then input else if index = 2 then archive
    else if index = 3 then query else if index = 5 then result else []

def state (label : Option Label) (store : Store) (input archive query result : List Bool) : State :=
  ⟨label, store, slots input archive query result⟩

theorem update_input (input archive query result replacement : List Bool) :
    Function.update (slots input archive query result) 0 replacement = slots replacement archive query result := by
  funext index; fin_cases index <;> simp [slots]

theorem update_archive (input archive query result replacement : List Bool) :
    Function.update (slots input archive query result) 2 replacement = slots input replacement query result := by
  funext index; fin_cases index <;> simp [slots]

theorem gate_tag (bit : Bool) (input archive query result : List Bool) (store : Store) :
    TM2.step program (state (some gateLabel) store (bit :: input) archive query result) =
      some (state (some (captureLabel 0))
        (setTag (setRecord store (some bit)) bit) input (bit :: archive) query result) := by
  change (some ⟨some (captureLabel 0), setTag (setRecord store (some bit)) bit,
    Function.update (Function.update (slots (bit :: input) archive query result) 0 input)
      2 (bit :: archive)⟩ : Option State) = _
  rw [update_input, update_archive]
  rfl

theorem gate_eof (archive query result : List Bool) (store : Store) :
    TM2.step program (state (some gateLabel) store [] archive query result) =
      some (state (some (historyLabel 0)) (missing (setRecord store none)) [] archive query result) := by
  change (some ⟨some (historyLabel 0), missing (setRecord store none),
    Function.update (slots [] archive query result) 0 []⟩ : Option State) = _
  rw [update_input]
  rfl

theorem decide_tombstone (contents : Stack → List Bool) (store : Store)
    (matched : Query.equality store.1 = true) (tombstone : Query.recordTag store.1 = false) :
    TM2.step program (⟨some decideLabel, store, contents⟩ : State) =
      some (⟨some (historyLabel 0), store, contents⟩ : State) := by
  change some (TM2.stepAux decideCode store contents) = _
  simp only [decideCode, TM2.stepAux,
    matched, tombstone, Bool.cond_true, Bool.cond_false]

theorem decide_store (contents : Stack → List Bool) (store : Store)
    (matched : Query.equality store.1 = true) (present : Query.recordTag store.1 = true) :
    TM2.step program (⟨some decideLabel, store, contents⟩ : State) =
      some (⟨some (copyLabel CellCopy.startLabel), store, contents⟩ : State) := by
  change some (TM2.stepAux decideCode store contents) = _
  simp only [decideCode, TM2.stepAux, matched, present, Bool.cond_true]

theorem decide_skip (contents : Stack → List Bool) (store : Store)
    (different : Query.equality store.1 = false) (present : Query.recordTag store.1 = true) :
    TM2.step program (⟨some decideLabel, store, contents⟩ : State) =
      some (⟨some (skipLabel CellSkip.startLabel), store, contents⟩ : State) := by
  change some (TM2.stepAux decideCode store contents) = _
  simp only [decideCode, TM2.stepAux,
    different, present, Bool.cond_true, Bool.cond_false]

theorem decide_older (contents : Stack → List Bool) (store : Store)
    (different : Query.equality store.1 = false) (tombstone : Query.recordTag store.1 = false) :
    TM2.step program (⟨some decideLabel, store, contents⟩ : State) =
      some (⟨some gateLabel, store, contents⟩ : State) := by
  change some (TM2.stepAux decideCode store contents) = _
  simp only [decideCode, TM2.stepAux,
    different, tombstone, Bool.cond_false]

theorem done_halt (input archive query result : List Bool) (store : Store) :
    TM2.step program (state (some doneLabel) store input archive query result) =
      some (state none store input archive query result) := rfl

theorem halted (input archive query result : List Bool) (store : Store) :
    TM2.step program (state none store input archive query result) = none := rfl

end PDROC.BitVM.Log.Lookup
