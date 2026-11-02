module

public import Paid.PDROC_BitVM_Log_CellField_001
public import Paid.PDROC_BitVM_Native_StoreTrace_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

/-! A fixed finite Cell-copy program. It reads the actual tag/sign, mirrors
all consumed bits to historyArchive2 and Cell-reverse6, and calls the genuine
mirrored Nat-field program once/twice. StoreIso removes a fixed Unit carrier;
it does not decode a Cell or put any Nat/Rat/word in control. -/

namespace PDROC.BitVM.Log.CellCopy

open Turing

abbrev Stack := Query.Stack
abbrev Label := Fin 4 ⊕ (CellField.Label ⊕ (CellField.Label ⊕ CellField.Label))
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Query.Store
abbrev Enriched := Store × Unit
abbrev State := TM2.Cfg Alphabet Label Store
abbrev EnrichedState := TM2.Cfg Alphabet Label Enriched
abbrev Statement := TM2.Stmt Alphabet Label Store
abbrev EnrichedStatement := TM2.Stmt Alphabet Label Enriched

def startLabel : Label := .inl 0
def signLabel : Label := .inl 1
def doneLabel : Label := .inl 2
def invalidLabel : Label := .inl 3
def naturalLabel (label : CellField.Label) : Label := .inr (.inl label)
def numeratorLabel (label : CellField.Label) : Label := .inr (.inr (.inl label))
def denominatorLabel (label : CellField.Label) : Label := .inr (.inr (.inr label))

def peel : Enriched ≃ Store where
  toFun := Prod.fst
  invFun := fun store => (store, ())
  left_inv := by intro pair; rcases pair with ⟨store, marker⟩; cases marker; rfl
  right_inv := by intro store; rfl

def setRecord (store : Enriched) (symbol : Option Bool) : Enriched :=
  (Query.setRecord store.1 symbol, store.2)

def fieldCode (labels : CellField.Label → Label) (returnLabel : Label)
    (label : CellField.Label) : EnrichedStatement :=
  Native.Inline.statement (τ := Unit) labels returnLabel (CellField.program label)

def tagCode : EnrichedStatement :=
  .pop 0 setRecord
    (.branch (fun store => store.1.1.isSome)
      (.push 2 (fun store => store.1.1.getD false)
        (.push 6 (fun store => store.1.1.getD false)
          (.branch (fun store => store.1.1.getD false)
            (.goto (fun _ => signLabel)) (.goto (fun _ => naturalLabel 0)))))
      (.goto (fun _ => invalidLabel)))

def signCode : EnrichedStatement :=
  .pop 0 setRecord
    (.branch (fun store => store.1.1.isSome)
      (.push 2 (fun store => store.1.1.getD false)
        (.push 6 (fun store => store.1.1.getD false) (.goto (fun _ => numeratorLabel 0))))
      (.goto (fun _ => invalidLabel)))

def enrichedProgram : Label → EnrichedStatement
  | .inl control => if control = 0 then tagCode else if control = 1 then signCode else .halt
  | .inr (.inl label) => fieldCode naturalLabel doneLabel label
  | .inr (.inr (.inl label)) => fieldCode numeratorLabel (denominatorLabel 0) label
  | .inr (.inr (.inr label)) => fieldCode denominatorLabel doneLabel label

def program : Label → Statement := Native.StoreIso.machine peel enrichedProgram

theorem field_supports (labels : CellField.Label → Label) (returnLabel : Label)
    (label : CellField.Label) :
    TM2.SupportsStmt (Finset.univ : Finset Label) (fieldCode labels returnLabel label) := by
  apply Native.Inline.supports_statement labels returnLabel
    (Finset.univ : Finset CellField.Label) (Finset.univ : Finset Label)
  · intro sourceLabel _; exact Finset.mem_univ _
  · exact Finset.mem_univ _
  · exact CellField.supports.2 label (Finset.mem_univ _)

theorem enriched_supports : TM2.Supports enrichedProgram (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    rcases label with control | (natural | (numerator | denominator))
    · fin_cases control <;> simp [enrichedProgram, tagCode, signCode, TM2.SupportsStmt]
    · exact field_supports naturalLabel doneLabel natural
    · exact field_supports numeratorLabel (denominatorLabel 0) numerator
    · exact field_supports denominatorLabel doneLabel denominator

theorem supports : TM2.Supports program (Finset.univ : Finset Label) :=
  Native.StoreIso.supports peel enrichedProgram Finset.univ enriched_supports

def enrichedState (label : Option Label) (store : Enriched) (input ticks archive captured : List Bool)
    (other : Stack → List Bool) : EnrichedState :=
  ⟨label, store, Capture.slots input ticks archive captured other⟩

def state (label : Option Label) (store : Store) (input ticks archive captured : List Bool)
    (other : Stack → List Bool) : State :=
  ⟨label, store, Capture.slots input ticks archive captured other⟩

theorem tag_false (input ticks archive captured : List Bool) (other : Stack → List Bool) (store : Enriched) :
    TM2.step enrichedProgram (enrichedState (some startLabel) store
      (false :: input) ticks archive captured other) =
      some (enrichedState (some (naturalLabel 0)) (setRecord store (some false))
        input ticks (false :: archive) (false :: captured) other) := by
  change (some ⟨some (naturalLabel 0), setRecord store (some false),
    Function.update (Function.update (Function.update
      (Capture.slots (false :: input) ticks archive captured other) 0 input)
      2 (false :: archive)) 6 (false :: captured)⟩ : Option EnrichedState) = _
  rw [Capture.update_input, Capture.update_archive, Capture.update_captured]
  rfl

theorem tag_true (input ticks archive captured : List Bool) (other : Stack → List Bool) (store : Enriched) :
    TM2.step enrichedProgram (enrichedState (some startLabel) store
      (true :: input) ticks archive captured other) =
      some (enrichedState (some signLabel) (setRecord store (some true))
        input ticks (true :: archive) (true :: captured) other) := by
  change (some ⟨some signLabel, setRecord store (some true),
    Function.update (Function.update (Function.update
      (Capture.slots (true :: input) ticks archive captured other) 0 input)
      2 (true :: archive)) 6 (true :: captured)⟩ : Option EnrichedState) = _
  rw [Capture.update_input, Capture.update_archive, Capture.update_captured]
  rfl

theorem sign_bit (bit : Bool) (input ticks archive captured : List Bool) (other : Stack → List Bool) (store : Enriched) :
    TM2.step enrichedProgram (enrichedState (some signLabel) store
      (bit :: input) ticks archive captured other) =
      some (enrichedState (some (numeratorLabel 0)) (setRecord store (some bit))
        input ticks (bit :: archive) (bit :: captured) other) := by
  change (some ⟨some (numeratorLabel 0), setRecord store (some bit),
    Function.update (Function.update (Function.update
      (Capture.slots (bit :: input) ticks archive captured other) 0 input)
      2 (bit :: archive)) 6 (bit :: captured)⟩ : Option EnrichedState) = _
  rw [Capture.update_input, Capture.update_archive, Capture.update_captured]
  rfl

theorem done_halt (input ticks archive captured : List Bool) (other : Stack → List Bool) (store : Enriched) :
    TM2.step enrichedProgram (enrichedState (some doneLabel) store input ticks archive captured other) =
      some (enrichedState none store input ticks archive captured other) := rfl

theorem halted (input ticks archive captured : List Bool) (other : Stack → List Bool) (store : Enriched) :
    TM2.step enrichedProgram (enrichedState none store input ticks archive captured other) = none := rfl

end PDROC.BitVM.Log.CellCopy
