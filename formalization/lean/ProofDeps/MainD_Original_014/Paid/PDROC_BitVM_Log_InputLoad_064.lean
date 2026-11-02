module

public import Paid.PDROC_BitVM_Log_InputLoad_063

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.InputLoad

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Kernel.RegisterGlobal

/-! True selected-bank commit and true invalid HALT. The destination is
actually cleared/copied only AFTER address selection; pointer may alias it.
The final query26 clear removes the actual marshalled pointer word. -/

def committed (field : Fin 13) (destination : Register) (contents : Stack → List Bool) :=
  Function.update (Function.update contents (registerSlot destination) (contents (BankDrain.bankSlot field))) 26 []

theorem copied_query (field : Fin 13) (destination : Register) (contents : Stack → List Bool) :
    Function.update contents (registerSlot destination) (contents (BankDrain.bankSlot field)) 26 = contents 26 := by
  cases destination <;> simp [registerSlot, PaperProofs.Structure.LaminarTree.IndexedRAM.Register.word]

theorem commit_runs (core : Bool) (pointer destination : Register) (field : Fin 13)
    (contents : Stack → List Bool) (store : Store) (scratch : contents 24 = []) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some (copyLabel field 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.1.2.1 = true ∧ after.stk = committed field destination contents ∧
      2 ≤ run.length ∧ run.length ≤ (contents (registerSlot destination)).length +
        2 * (contents (BankDrain.bankSlot field)).length + (contents 26).length + 12 := by
  obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ := copy_return core pointer destination field contents store scratch
  let copied := Function.update contents (registerSlot destination) (contents (BankDrain.bankSlot field))
  obtain ⟨right, rightHead, rightChain, rightLast, rightLength⟩ :=
    clean_return core pointer destination copied (HeapLoad.cleared store)
  let final : SourceState := ⟨none, (HeapPointer.setTyped (HeapLoad.cleared store) true, ()), committed field destination contents⟩
  let body := right ++ [final]
  have bodyHead : body.head? = some (⟨some (cleanLabel 0), (HeapLoad.cleared store, ()), copied⟩ : SourceState) := by
    simp only [body, List.head?_append, rightHead, Option.some_or]
  have bodyChain : body.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) := by
    apply rightChain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [rightLast, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    exact done_halt core pointer destination (HeapLoad.cleared store, ()) (committed field destination contents)
  have rightPositive : 0 < right.length := by omega
  have bodyNotOne : body.length ≠ 1 := by simp only [body, List.length_append, List.length_cons, List.length_nil]; omega
  have bodyLast : body.getLast? = some final := List.getLast?_append_cons right final []
  let middle : SourceState := ⟨some (cleanLabel 0), (HeapLoad.cleared store, ()), copied⟩
  let run := left ++ body.tail
  have head : run.head? = some (⟨some (copyLabel field 0), (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, leftHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) :=
    TwoStack.join_chain left body middle leftChain bodyChain leftLast bodyHead
  have last : run.getLast? = some final := by
    simp only [run, List.getLast?_append, List.getLast?_tail, bodyNotOne, ↓reduceIte, bodyLast, Option.some_or]
  refine ⟨run, final, head, chain, last, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [run, body, List.length_append, List.length_cons, List.length_nil, List.length_tail]
    omega
  · have rightExact : right.length = (contents 26).length + 3 := by
      simpa only [copied, copied_query] using rightLength
    simp only [run, body, List.length_append, List.length_cons, List.length_nil, List.length_tail]
    omega

theorem invalid_runs (core : Bool) (pointer destination : Register) (contents : Stack → List Bool) (store : Store) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some invalidLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.1.2.1 = false ∧ after.stk = contents ∧ run.length = 2 := by
  let before : SourceState := ⟨some invalidLabel, (store, ()), contents⟩
  let after : SourceState := ⟨none, (HeapPointer.setTyped store false, ()), contents⟩
  refine ⟨[before, after], after, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact List.isChain_cons_cons.mpr ⟨invalid_halt core pointer destination (store, ()) contents, List.isChain_singleton _⟩

end PDROC.BitVM.Log.InputLoad
