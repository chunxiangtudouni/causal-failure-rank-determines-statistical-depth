module

public import Paid.PDROC_BitVM_Log_Lookup_013
public import Paid.PDROC_BitVM_Kernel_NatMarshal_001
public import Paid.PDROC_BitVM_Kernel_Register_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Log.HeapPointer

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Genuine pointer marshalling from the actual register Cell. A peek of the
real Cell tag selects Nat versus failure before any source byte is removed.
The program has eight fixed labels and108 finite store states before input.
The carried lookup fields are flags, never addresses, values or heap maps. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Fin 8
abbrev Store := Kernel.NatMarshal.Store × Lookup.Store
abbrev State := TM2.Cfg Alphabet Label Store
abbrev SourceState := TM2.Cfg Alphabet Kernel.NatMarshal.Label Kernel.NatMarshal.Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def embedding (pointer : Register) : Fin 3 ↪ Stack where
  toFun := fun index => if index = 0 then registerSlot pointer else if index = 1 then 26 else 24
  inj' := by
    intro left right same
    have values := congrArg Fin.val same
    have bounds := registerSlot_bounds pointer
    fin_cases left <;> fin_cases right <;> simp at values ⊢ <;> omega

def sourceProgram (pointer : Register) := Lift.machine (embedding pointer) Kernel.NatMarshal.program

def marshalLabel (label : Kernel.NatMarshal.Label) : Label := ⟨label.val + 1, by omega⟩

def saveTag (store : Store) (symbol : Option Bool) : Store := ((symbol, store.1.2), store.2)

def setTyped (store : Store) (typed : Bool) : Store :=
  (store.1, (Query.setEquality store.2.1 typed, store.2.2))

def guardCode (pointer : Register) : Statement :=
  .peek (registerSlot pointer) saveTag
    (.branch (fun store => store.1.1 == some false)
      (.goto (fun _ => marshalLabel 0)) (.goto (fun _ => 7)))

def program (pointer : Register) (label : Label) : Statement :=
  if label = 0 then guardCode pointer
  else if label = 1 then Inline.statement marshalLabel 6 (sourceProgram pointer 0)
  else if label = 2 then Inline.statement marshalLabel 6 (sourceProgram pointer 1)
  else if label = 3 then Inline.statement marshalLabel 6 (sourceProgram pointer 2)
  else if label = 4 then Inline.statement marshalLabel 6 (sourceProgram pointer 3)
  else if label = 5 then Inline.statement marshalLabel 6 (sourceProgram pointer 4)
  else if label = 6 then .load (fun store => setTyped store true) .halt
  else .load (fun store => setTyped store false) .halt

def state (label : Option Label) (store : Store) (contents : Stack → List Bool) : State :=
  ⟨label, store, contents⟩

theorem marshal_agrees (pointer : Register) : ∀ label,
    program pointer (marshalLabel label) = Inline.statement marshalLabel 6 (sourceProgram pointer label) := by
  intro label; fin_cases label <;> rfl

theorem supports (pointer : Register) : TM2.Supports (program pointer) (Finset.univ : Finset Label) := by
  have sourceClosed := Lift.supports (embedding pointer) Kernel.NatMarshal.program
    (Finset.univ : Finset Kernel.NatMarshal.Label) Kernel.NatMarshal.supports
  have callClosed (label : Kernel.NatMarshal.Label) :
      TM2.SupportsStmt (Finset.univ : Finset Label)
        (Inline.statement (τ := Lookup.Store) marshalLabel 6 (sourceProgram pointer label)) := by
    apply Inline.supports_statement marshalLabel 6
      (Finset.univ : Finset Kernel.NatMarshal.Label) (Finset.univ : Finset Label)
    · intro index _; exact Finset.mem_univ _
    · exact Finset.mem_univ _
    · exact sourceClosed.2 label (Finset.mem_univ _)
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    · simp [program, guardCode, TM2.SupportsStmt]
    · exact callClosed 0
    · exact callClosed 1
    · exact callClosed 2
    · exact callClosed 3
    · exact callClosed 4
    · simp [program, TM2.SupportsStmt]
    · simp [program, TM2.SupportsStmt]

theorem guard_nat (pointer : Register) (contents : Stack → List Bool) (store : Store)
    (head : (contents (registerSlot pointer)).head? = some false) :
    TM2.step (program pointer) (state (some 0) store contents) =
      some (state (some (marshalLabel 0)) (saveTag store (some false)) contents) := by
  change some (TM2.stepAux (guardCode pointer) store contents) = _
  simp [guardCode, TM2.stepAux, head, saveTag, state]

theorem guard_rat (pointer : Register) (contents : Stack → List Bool) (store : Store)
    (head : (contents (registerSlot pointer)).head? = some true) :
    TM2.step (program pointer) (state (some 0) store contents) =
      some (state (some 7) (saveTag store (some true)) contents) := by
  change some (TM2.stepAux (guardCode pointer) store contents) = _
  simp [guardCode, TM2.stepAux, head, saveTag, state]

theorem guard_empty (pointer : Register) (contents : Stack → List Bool) (store : Store)
    (head : (contents (registerSlot pointer)).head? = none) :
    TM2.step (program pointer) (state (some 0) store contents) =
      some (state (some 7) (saveTag store none) contents) := by
  change some (TM2.stepAux (guardCode pointer) store contents) = _
  simp [guardCode, TM2.stepAux, head, saveTag, state]

theorem success_step (pointer : Register) (contents : Stack → List Bool) (store : Store) :
    TM2.step (program pointer) (state (some 6) store contents) =
      some (state none (setTyped store true) contents) := rfl

theorem invalid_step (pointer : Register) (contents : Stack → List Bool) (store : Store) :
    TM2.step (program pointer) (state (some 7) store contents) =
      some (state none (setTyped store false) contents) := rfl

theorem halted (pointer : Register) (contents : Stack → List Bool) (store : Store) :
    TM2.step (program pointer) (state none store contents) = none := rfl

theorem setTyped_spec (store : Store) (typed : Bool) :
    Query.equality (setTyped store typed).2.1 = typed ∧
      (setTyped store typed).1 = store.1 ∧
      Query.recordTag (setTyped store typed).2.1 = Query.recordTag store.2.1 ∧
      Query.querySymbol (setTyped store typed).2.1 = Query.querySymbol store.2.1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The only operand premise names the actual register bytes. No supplied
encoded operand is installed into query26 by a host function. -/
theorem initial_projection (pointer : Register) (value : ℕ) (contents : Stack → List Bool) (saved : Option Bool)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value))
    (scratch : contents 24 = []) :
    Lift.cfg (embedding pointer) (⟨some 0, (saved, ()), contents⟩ : SourceState) =
      Kernel.NatMarshal.before (encodeNatBits value) (contents 26) saved := by
  have data : Lift.slots (embedding pointer) contents =
      TwoStack.threeStacks (false :: encodeNatBits value) (contents 26) [] := by
    funext index
    fin_cases index
    · exact register
    · rfl
    · exact scratch
  change (⟨some 0, (saved, ()), Lift.slots (embedding pointer) contents⟩ : Kernel.NatMarshal.State) = _
  rw [data]
  rfl

end PDROC.BitVM.Log.HeapPointer
