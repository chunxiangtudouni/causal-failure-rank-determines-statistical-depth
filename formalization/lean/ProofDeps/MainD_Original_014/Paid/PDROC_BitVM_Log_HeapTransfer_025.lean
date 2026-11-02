module

public import Paid.PDROC_BitVM_Log_HeapPointer_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.Log.HeapTransfer

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Actual register/work Cell transfer, reusing the parent's destination
clear and word-copy code. Direction is a fixed finite opcode choice, not a
runtime Nat address. No encoded source operand is supplied to the machine. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Fin 6
abbrev Store := HeapPointer.Store
abbrev State := TM2.Cfg Alphabet Label Store
abbrev SourceState := TM2.Cfg Alphabet Kernel.RegisterMove.Label Kernel.RegisterMove.Store

def sourceSlot (toRegister : Bool) (reg : Register) : Stack := if toRegister then 28 else registerSlot reg
def targetSlot (toRegister : Bool) (reg : Register) : Stack := if toRegister then registerSlot reg else 28

def embedding (toRegister : Bool) (reg : Register) : Fin 3 ↪ Stack where
  toFun := fun index => if index = 0 then sourceSlot toRegister reg else if index = 1 then targetSlot toRegister reg else 24
  inj' := by
    intro left right same
    have values := congrArg Fin.val same
    have bounds := registerSlot_bounds reg
    cases toRegister <;> fin_cases left <;> fin_cases right <;>
      simp [sourceSlot, targetSlot] at values ⊢ <;> omega

def sourceProgram (toRegister : Bool) (reg : Register) := Lift.machine (embedding toRegister reg) Kernel.RegisterMove.program
def copyLabel (label : Kernel.RegisterMove.Label) : Label := ⟨label.val, by omega⟩

def program (toRegister : Bool) (reg : Register) (label : Label) : TM2.Stmt Alphabet Label Store :=
  if label = 0 then Inline.statement (τ := Lookup.Store) copyLabel 5 (sourceProgram toRegister reg 0)
  else if label = 1 then Inline.statement (τ := Lookup.Store) copyLabel 5 (sourceProgram toRegister reg 1)
  else if label = 2 then Inline.statement (τ := Lookup.Store) copyLabel 5 (sourceProgram toRegister reg 2)
  else if label = 3 then Inline.statement (τ := Lookup.Store) copyLabel 5 (sourceProgram toRegister reg 3)
  else if label = 4 then Inline.statement (τ := Lookup.Store) copyLabel 5 (sourceProgram toRegister reg 4)
  else .halt

theorem agrees (toRegister : Bool) (reg : Register) : ∀ label,
    program toRegister reg (copyLabel label) =
      Inline.statement (τ := Lookup.Store) copyLabel 5 (sourceProgram toRegister reg label) := by
  intro label; fin_cases label <;> rfl

theorem supports (toRegister : Bool) (reg : Register) :
    TM2.Supports (program toRegister reg) (Finset.univ : Finset Label) := by
  have closed := Lift.supports (embedding toRegister reg) Kernel.RegisterMove.program
    (Finset.univ : Finset Kernel.RegisterMove.Label) Kernel.RegisterMove.supports
  have callClosed (label : Kernel.RegisterMove.Label) : TM2.SupportsStmt (Finset.univ : Finset Label)
      (Inline.statement (τ := Lookup.Store) copyLabel 5 (sourceProgram toRegister reg label)) := by
    apply Inline.supports_statement copyLabel 5 (Finset.univ : Finset Kernel.RegisterMove.Label) (Finset.univ : Finset Label)
    · intro index _; exact Finset.mem_univ _
    · exact Finset.mem_univ _
    · exact closed.2 label (Finset.mem_univ _)
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    · exact callClosed 0
    · exact callClosed 1
    · exact callClosed 2
    · exact callClosed 3
    · exact callClosed 4
    · simp [program, TM2.SupportsStmt]

theorem initial_projection (toRegister : Bool) (reg : Register) (contents : Stack → List Bool) (saved : Option Bool)
    (scratch : contents 24 = []) :
    Lift.cfg (embedding toRegister reg) (⟨some 0, (saved, ()), contents⟩ : SourceState) =
      Kernel.RegisterMove.before (contents (sourceSlot toRegister reg)) (contents (targetSlot toRegister reg)) saved := by
  have data : Lift.slots (embedding toRegister reg) contents = TwoStack.threeStacks
      (contents (sourceSlot toRegister reg)) (contents (targetSlot toRegister reg)) [] := by
    funext index
    fin_cases index
    · rfl
    · rfl
    · exact scratch
  exact congrArg (fun current => (⟨some 0, (saved, ()), current⟩ : Kernel.RegisterMove.State)) data

/-- The genuine source-copy path preserves its physical source, clears its
old destination including FALSE cells, and restores scratch24 to empty. -/
theorem source_runs (toRegister : Bool) (reg : Register) (contents : Stack → List Bool) (saved : Option Bool)
    (scratch : contents 24 = []) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some 0, (saved, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram toRegister reg) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram toRegister reg) after = none ∧
      after.l = none ∧ after.var = (none, ()) ∧
      after.stk = Function.update contents (targetSlot toRegister reg) (contents (sourceSlot toRegister reg)) ∧
      run.length = (contents (targetSlot toRegister reg)).length + 2 * (contents (sourceSlot toRegister reg)).length + 5 := by
  obtain ⟨source, sourceHead, sourceChain, sourceLast, sourceHalt, sourceLength,
    sourceWord, targetWord, scratchWord⟩ :=
    Kernel.RegisterMove.move_word_runs (contents (sourceSlot toRegister reg)) (contents (targetSlot toRegister reg)) saved
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq : first = Kernel.RegisterMove.before (contents (sourceSlot toRegister reg))
        (contents (targetSlot toRegister reg)) saved := Option.some.inj sourceHead
    subst first
    let before : SourceState := ⟨some 0, (saved, ()), contents⟩
    obtain ⟨posts, final, length, chain, last, projected, frame⟩ :=
      Lift.path (embedding toRegister reg) Kernel.RegisterMove.program before
        (Kernel.RegisterMove.before (contents (sourceSlot toRegister reg)) (contents (targetSlot toRegister reg)) saved)
        (Kernel.RegisterMove.final (contents (sourceSlot toRegister reg))) rest
        (initial_projection toRegister reg contents saved scratch) sourceChain sourceLast
    have halt : TM2.step (sourceProgram toRegister reg) final = none := by
      apply Lift.halt_project
      rw [projected]
      exact sourceHalt
    have done : final.l = none := congrArg (fun current : Kernel.RegisterMove.State => current.l) projected
    have finalVar : final.var = (none, ()) := congrArg (fun current : Kernel.RegisterMove.State => current.var) projected
    have localData (index : Fin 3) : final.stk (embedding toRegister reg index) =
        (Kernel.RegisterMove.final (contents (sourceSlot toRegister reg))).stk index :=
      congrArg (fun current : Kernel.RegisterMove.State => current.stk index) projected
    have data : final.stk = Function.update contents (targetSlot toRegister reg) (contents (sourceSlot toRegister reg)) := by
      funext index
      by_cases target : index = targetSlot toRegister reg
      · subst index
        simpa [embedding, Kernel.RegisterMove.final, TwoStack.threeStacks] using localData 1
      · rw [Function.update_of_ne target]
        by_cases sourceEq : index = sourceSlot toRegister reg
        · subst index
          exact localData 0
        · by_cases scratchEq : index = 24
          · subst index
            exact (localData 2).trans scratch.symm
          · exact frame index (by
              intro localIndex
              fin_cases localIndex
              · exact sourceEq
              · exact target
              · exact scratchEq)
    refine ⟨before :: posts, final, rfl, chain, last, halt, done, finalVar, data, ?_⟩
    simp only [List.length_cons] at sourceLength ⊢
    omega

/-- One selected actual transfer path, with a real call return and final
HALT. All lookup flags and arbitrary non-destination stack data carry. -/
theorem runs (toRegister : Bool) (reg : Register) (contents : Stack → List Bool) (store : Store)
    (scratch : contents 24 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some 0, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program toRegister reg) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program toRegister reg) after = none ∧
      after.l = none ∧ after.var = ((none, store.1.2), store.2) ∧
      after.stk = Function.update contents (targetSlot toRegister reg) (contents (sourceSlot toRegister reg)) ∧
      run.length = (contents (targetSlot toRegister reg)).length + 2 * (contents (sourceSlot toRegister reg)).length + 6 := by
  rcases store with ⟨⟨saved, marker⟩, extra⟩
  cases marker
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := source_runs toRegister reg contents saved scratch
  obtain ⟨returned, after, head, chain, last, atReturn, data, varEq, length⟩ :=
    Inline.actual_return_trace copyLabel 5 (sourceProgram toRegister reg) (program toRegister reg)
      (agrees toRegister reg) source (⟨some 0, (saved, ()), contents⟩ : SourceState)
      sourceFinal extra sourceHead sourceChain sourceLast sourceHalt
  let finalContents := Function.update contents (targetSlot toRegister reg) (contents (sourceSlot toRegister reg))
  have finalVar : after.var = ((none, ()), extra) := by rw [varEq, sourceVar]
  have finalData : after.stk = finalContents := data.trans sourceData
  have afterEq : after = (⟨some 5, ((none, ()), extra), finalContents⟩ : State) := by
    rcases after with ⟨label, vars, current⟩
    change label = some 5 at atReturn
    change vars = ((none, ()), extra) at finalVar
    change current = finalContents at finalData
    subst label; subst vars; subst current
    rfl
  let final : State := ⟨none, ((none, ()), extra), finalContents⟩
  let run := returned ++ [final]
  have actual : run.IsChain (fun a b => TM2.step (program toRegister reg) a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    rw [afterEq]
    rfl
  have entry : returned.head? = some (⟨some 0, ((saved, ()), extra), contents⟩ : State) := head
  refine ⟨run, final, ?_, actual, List.getLast?_append_cons returned final [], rfl, rfl, rfl, rfl, ?_⟩
  · change (returned ++ [final]).head? = some (⟨some 0, ((saved, ()), extra), contents⟩ : State)
    simp only [List.head?_append, entry, Option.some_or]
  · simp only [run, List.length_append, List.length_cons, List.length_nil]
    omega

end PDROC.BitVM.Log.HeapTransfer
