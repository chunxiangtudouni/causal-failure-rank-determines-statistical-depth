module

public import Paid.PDROC_BitVM_Log_Drain_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.Log.BankDrain

open Turing
open PDROC.BitVM.Native

/-! A real reverse drain from capture29 into one statically chosen readonly
bank role1..13. No Nat field index enters sigma. The old target word is
preserved as a suffix here; the outer bank reader must ACTUALLY clear it. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Drain.Label
abbrev Store := Query.Store
abbrev State := TM2.Cfg Alphabet Label Store

def bankSlot (field : Fin 13) : Stack := ⟨field.val + 1, by omega⟩

theorem bankSlot_ne (field : Fin 13) (index : Stack) (outside : index.val = 0 ∨ 14 ≤ index.val) :
    bankSlot field ≠ index := by
  intro equal
  have values := congrArg Fin.val equal
  change field.val + 1 = index.val at values
  have bound := field.isLt
  omega

def slot (field : Fin 13) (index : Drain.Stack) : Stack :=
  if index = 0 then 0 else if index = 1 then 24 else if index = 2 then 25
    else if index = 3 then 26 else if index = 4 then 27 else if index = 5 then bankSlot field else 29

def embedding (field : Fin 13) : Drain.Stack ↪ Stack where
  toFun := slot field
  inj' := by
    intro left right equal
    have values := congrArg Fin.val equal
    have bound := field.isLt
    fin_cases left <;> fin_cases right <;> simp [slot, bankSlot] at values ⊢ <;> omega

def program (field : Fin 13) := Lift.machine (embedding field) (Drain.program true)

theorem supports (field : Fin 13) : TM2.Supports (program field) (Finset.univ : Finset Label) :=
  Lift.supports (embedding field) (Drain.program true) (Finset.univ : Finset Label) (Drain.supports true)

def drained (field : Fin 13) (contents : Stack → List Bool) :=
  Function.update (Function.update contents 29 []) (bankSlot field)
    ((contents 29).reverse ++ contents (bankSlot field))

theorem representation (field : Fin 13) (before : State) (position : before.l = some 0) :
    Lift.cfg (embedding field) before = Drain.state true (some 0) before.var
      (before.stk 29) (before.stk (bankSlot field)) (Lift.slots (embedding field) before.stk) := by
  have slots : Lift.slots (embedding field) before.stk = Drain.slots true
      (before.stk 29) (before.stk (bankSlot field)) (Lift.slots (embedding field) before.stk) := by
    funext index
    fin_cases index <;> simp [Lift.slots, embedding, slot, Drain.slots, Drain.source, Drain.target]
  change (⟨before.l, before.var, Lift.slots (embedding field) before.stk⟩ : Drain.State) = _
  rw [position]
  exact congrArg (fun contents : Drain.Stack → List Bool => (⟨some 0, before.var, contents⟩ : Drain.State)) slots

theorem drained_shape (field : Fin 13) (contents data : Stack → List Bool)
    (projected : Lift.slots (embedding field) data = Drain.slots true []
      ((contents 29).reverse ++ contents (bankSlot field)) (Lift.slots (embedding field) contents))
    (frame : ∀ index : Stack, (∀ localIndex, index ≠ embedding field localIndex) → data index = contents index) :
    data = drained field contents := by
  funext index
  by_cases atBank : index = bankSlot field
  · subst index
    rw [drained, Function.update_self]
    have fact := congrFun projected 5
    simpa [Lift.slots, embedding, slot, Drain.slots, Drain.source, Drain.target] using fact
  · by_cases at29 : index = 29
    · subst index
      rw [drained, Function.update_of_ne atBank, Function.update_self]
      have fact := congrFun projected 6
      simpa [Lift.slots, embedding, slot, Drain.slots, Drain.source, Drain.target] using fact
    · rw [drained, Function.update_of_ne atBank, Function.update_of_ne at29]
      by_cases mapped : ∃ localIndex, embedding field localIndex = index
      · rcases mapped with ⟨localIndex, rfl⟩
        have fact := congrFun projected localIndex
        fin_cases localIndex
        all_goals first
          | exact False.elim (atBank rfl)
          | exact False.elim (at29 rfl)
          | simpa [Lift.slots, embedding, slot, Drain.slots, Drain.source, Drain.target] using fact
      · exact frame index (fun localIndex equal => mapped ⟨localIndex, equal.symm⟩)

/-- The captured word is really popped and reversed into the selected bank.
All other30 stacks, including history25 and source0, are arbitrary carry. -/
theorem runs (field : Fin 13) (before : State) (position : before.l = some 0) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program field) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program field) after = none ∧ after.l = none ∧
      after.var = (none, before.var.2) ∧ after.stk = drained field before.stk ∧
      run.length = (before.stk 29).length + 3 := by
  let other := Lift.slots (embedding field) before.stk
  let sourceStart := Drain.state true (some 0) before.var (before.stk 29) (before.stk (bankSlot field)) other
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    Drain.drain_runs true (before.stk 29) (before.stk (bankSlot field)) other before.var
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq : first = sourceStart := Option.some.inj sourceHead
    subst first
    obtain ⟨posts, after, length, chain, last, projected, frame⟩ :=
      Lift.path (embedding field) (Drain.program true) before sourceStart sourceFinal rest
        (representation field before position) sourceChain sourceLast
    have halt : TM2.step (program field) after = none := by
      apply Lift.halt_project (embedding field) (Drain.program true) after
      rw [projected]
      exact sourceHalt
    have done : after.l = none :=
      (congrArg (fun state : Drain.State => state.l) projected).trans sourceDone
    have vars : after.var = (none, before.var.2) :=
      (congrArg (fun state : Drain.State => state.var) projected).trans sourceVar
    have data : Lift.slots (embedding field) after.stk = Drain.slots true []
        ((before.stk 29).reverse ++ before.stk (bankSlot field)) other := by
      have actual := (congrArg (fun state : Drain.State => state.stk) projected).trans sourceData
      simpa only [Lift.cfg] using actual
    refine ⟨before :: posts, after, rfl, chain, last, halt, done, vars,
      drained_shape field before.stk after.stk data frame, ?_⟩
    simp only [List.length_cons] at sourceLength ⊢
    omega

end PDROC.BitVM.Log.BankDrain
