module

public import Paid.PDROC_BitVM_Log_InputLiteral_057

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

namespace PDROC.BitVM.Log.InputCopy

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal

/-! Reuse the already passed REAL result28→register transfer by a fixed
total Fin32 swap of28 and the selected readonly bank. No new copy algorithm,
host bank indexing or free register write is introduced. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := HeapTransfer.Label
abbrev Store := HeapPointer.Store
abbrev State := TM2.Cfg Alphabet Label Store

def permutation (field : Fin 13) : Stack ≃ Stack := Equiv.swap 28 (BankDrain.bankSlot field)
def embedding (field : Fin 13) : Stack ↪ Stack := (permutation field).toEmbedding
def program (field : Fin 13) (destination : Register) := Lift.machine (embedding field) (HeapTransfer.program true destination)

theorem source_slot (field : Fin 13) : embedding field 28 = BankDrain.bankSlot field :=
  Equiv.swap_apply_left _ _

theorem scratch_fixed (field : Fin 13) : embedding field 24 = 24 :=
  Equiv.swap_apply_of_ne_of_ne (by decide) (BankDrain.bankSlot_ne field 24 (by decide)).symm

theorem register_fixed (field : Fin 13) (destination : Register) :
    embedding field (registerSlot destination) = registerSlot destination := by
  have bounds := registerSlot_bounds destination
  have not28 : registerSlot destination ≠ 28 := by
    intro equal
    have values := congrArg Fin.val equal
    change (registerSlot destination).val = 28 at values
    omega
  exact Equiv.swap_apply_of_ne_of_ne not28
    (BankDrain.bankSlot_ne field (registerSlot destination) (Or.inr bounds.1)).symm

theorem supports (field : Fin 13) (destination : Register) :
    TM2.Supports (program field destination) (Finset.univ : Finset Label) :=
  Lift.supports (embedding field) (HeapTransfer.program true destination) (Finset.univ : Finset Label)
    (HeapTransfer.supports true destination)

theorem runs (field : Fin 13) (destination : Register) (before : State)
    (position : before.l = some 0) (scratch : before.stk 24 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program field destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program field destination) after = none ∧ after.l = none ∧
      after.var = HeapLoad.cleared before.var ∧
      after.stk = Function.update before.stk (registerSlot destination) (before.stk (BankDrain.bankSlot field)) ∧
      run.length = (before.stk (registerSlot destination)).length +
        2 * (before.stk (BankDrain.bankSlot field)).length + 6 := by
  let contents := Lift.slots (embedding field) before.stk
  let sourceStart : HeapTransfer.State := ⟨some 0, before.var, contents⟩
  have sourceScratch : contents 24 = [] := by
    change before.stk (embedding field 24) = []
    rw [scratch_fixed]
    exact scratch
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    HeapTransfer.runs true destination contents before.var sourceScratch
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq : first = sourceStart := Option.some.inj sourceHead
    subst first
    have represented : Lift.cfg (embedding field) before = sourceStart := by
      change (⟨before.l, before.var, contents⟩ : HeapTransfer.State) = _
      rw [position]
    obtain ⟨posts, after, length, chain, last, projected, frame⟩ :=
      Lift.path (embedding field) (HeapTransfer.program true destination) before sourceStart sourceFinal rest
        represented sourceChain sourceLast
    have halt : TM2.step (program field destination) after = none := by
      apply Lift.halt_project (embedding field) (HeapTransfer.program true destination) after
      rw [projected]
      exact sourceHalt
    have done : after.l = none := (congrArg (fun state : HeapTransfer.State => state.l) projected).trans sourceDone
    have vars : after.var = HeapLoad.cleared before.var :=
      (congrArg (fun state : HeapTransfer.State => state.var) projected).trans sourceVar
    change sourceFinal.stk = Function.update contents (registerSlot destination) (contents 28) at sourceData
    have dataSlots : Lift.slots (embedding field) after.stk =
        Function.update contents (registerSlot destination) (before.stk (BankDrain.bankSlot field)) := by
      have actual := (congrArg (fun state : HeapTransfer.State => state.stk) projected).trans sourceData
      simp only [Lift.cfg] at actual
      change Lift.slots (embedding field) after.stk =
        Function.update contents (registerSlot destination) (before.stk (embedding field 28)) at actual
      rw [source_slot] at actual
      exact actual
    have expected : Lift.slots (embedding field)
        (Function.update before.stk (registerSlot destination) (before.stk (BankDrain.bankSlot field))) =
      Function.update contents (registerSlot destination) (before.stk (BankDrain.bankSlot field)) := by
      simpa only [register_fixed] using Lift.slots_update (embedding field) before.stk
        (registerSlot destination) (before.stk (BankDrain.bankSlot field))
    have data : after.stk = Function.update before.stk (registerSlot destination) (before.stk (BankDrain.bankSlot field)) := by
      funext index
      have fact := congrFun (dataSlots.trans expected.symm) ((permutation field).symm index)
      change after.stk ((permutation field) ((permutation field).symm index)) =
        Function.update before.stk (registerSlot destination) (before.stk (BankDrain.bankSlot field))
          ((permutation field) ((permutation field).symm index)) at fact
      let expectedData : Stack → List Bool := Function.update before.stk (registerSlot destination) (before.stk (BankDrain.bankSlot field))
      have back := (permutation field).apply_symm_apply index
      calc
        after.stk index = after.stk ((permutation field) ((permutation field).symm index)) := congrArg after.stk back.symm
        _ = expectedData ((permutation field) ((permutation field).symm index)) := fact
        _ = expectedData index := congrArg expectedData back
    refine ⟨before :: posts, after, rfl, chain, last, halt, done, vars, data, ?_⟩
    change (sourceStart :: rest).length = (contents (registerSlot destination)).length + 2 * (contents 28).length + 6 at sourceLength
    have sourceLengthExact : (sourceStart :: rest).length = (before.stk (registerSlot destination)).length +
        2 * (before.stk (BankDrain.bankSlot field)).length + 6 := by
      change (sourceStart :: rest).length = (before.stk (embedding field (registerSlot destination))).length +
        2 * (before.stk (embedding field 28)).length + 6 at sourceLength
      rw [register_fixed, source_slot] at sourceLength
      exact sourceLength
    simp only [List.length_cons] at sourceLengthExact ⊢
    omega

end PDROC.BitVM.Log.InputCopy
