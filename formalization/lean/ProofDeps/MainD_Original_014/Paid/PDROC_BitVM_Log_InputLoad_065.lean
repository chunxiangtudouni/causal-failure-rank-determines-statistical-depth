module

public import Paid.PDROC_BitVM_Log_InputLoad_064

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.InputLoad

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Kernel.RegisterGlobal

/-! The whole opcode's real clear/read/type/candidate prefix. There are NO
empty-work or caller-encoded address assumptions: Ready comes from the actual
six clears and actual Nat register read in062. -/

theorem marshalled_ready (query : ℕ) (contents : Stack → List Bool) : Ready query (marshalled query contents) := by
  have fields := HeapLoad.marshalled_fields query contents
  exact ⟨fields.2.1, fields.2.2.2.1, fields.2.2.2.2.1, fields.2.2.2.2.2.1⟩

theorem marshalled_register (query : ℕ) (reg : Register) (contents : Stack → List Bool) :
    marshalled query contents (registerSlot reg) = contents (registerSlot reg) := by
  cases reg <;> simp [marshalled, HeapLoad.marshalled, HeapLoad.preCleared, registerSlot,
    PaperProofs.Structure.LaminarTree.IndexedRAM.Register.word]

theorem marshalled_bank (query : ℕ) (field : Fin 13) (contents : Stack → List Bool) :
    marshalled query contents (BankDrain.bankSlot field) = contents (BankDrain.bankSlot field) := by
  have not26 := BankDrain.bankSlot_ne field 26 (by decide)
  have outside : (BankDrain.bankSlot field).val < 24 := by
    change field.val + 1 < 24
    omega
  rw [marshalled, HeapLoad.marshalled, Function.update_of_ne not26]
  exact HeapLoad.preCleared_outside contents (BankDrain.bankSlot field) (Or.inl outside)

def selectionBudget (query : ℕ) (contents : Stack → List Bool) :=
  clearBudget contents + 2 * (encodeNatBits query).length + 50 * (query + 1) + 10

theorem selected_prefix_runs (core : Bool) (pointer destination : Register) (query : ℕ)
    (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query))
    (range : query < BankMount.fieldCount core) :
    ∃ (run : List SourceState) (vars : Store),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (copyLabel ⟨query, by have limit := BankMount.fieldCount_le core; omega⟩ 0),
        (vars, ()), marshalled query contents⟩ : SourceState) ∧
      Query.equality vars.2.1 = true ∧ run.length ≤ selectionBudget query contents := by
  obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ := natural_ready core pointer destination query contents store register
  let pointerStore := pointerResult (cleared store)
  let pointerContents := marshalled query contents
  obtain ⟨right, vars, rightHead, rightChain, rightLast, flag, rightLength⟩ :=
    selected_runs core pointer destination query 0 range (by omega) pointerContents pointerStore (marshalled_ready query contents)
  have rightHeadExact : right.head? = some (⟨some (literalLabel 0 InputLiteral.startLabel),
      (pointerStore, ()), pointerContents⟩ : SourceState) := by
    simpa only [Fin.mk_zero] using rightHead
  let boundary : SourceState := ⟨some typeBranch, (pointerStore, ()), pointerContents⟩
  let body := boundary :: right
  have bodyHead : body.head? = some boundary := rfl
  have bodyChain : body.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) := by
    apply List.IsChain.cons rightChain
    intro next member
    rw [rightHeadExact] at member
    have equal := Option.mem_some_iff.mp member
    subst next
    exact type_step core pointer destination (pointerStore, ()) pointerContents rfl
  have bodyLast : body.getLast? = some (⟨some (copyLabel ⟨query, by have limit := BankMount.fieldCount_le core; omega⟩ 0),
      (vars, ()), pointerContents⟩ : SourceState) := by
    simp only [body, List.getLast?_cons, rightLast, Option.getD_some]
  have rightPositive : 0 < right.length := by
    cases right with
    | nil => simp only [List.head?_nil, reduceCtorEq] at rightHead
    | cons first rest => simp only [List.length_cons]; omega
  have bodyNotOne : body.length ≠ 1 := by simp only [body, List.length_cons]; omega
  let run := left ++ body.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, leftHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) :=
    TwoStack.join_chain left body boundary leftChain bodyChain leftLast bodyHead
  have last : run.getLast? = some (⟨some (copyLabel ⟨query, by have limit := BankMount.fieldCount_le core; omega⟩ 0),
      (vars, ()), pointerContents⟩ : SourceState) := by
    simp only [run, List.getLast?_append, List.getLast?_tail, bodyNotOne, ↓reduceIte, bodyLast, Option.some_or]
  refine ⟨run, vars, head, chain, last, flag, ?_⟩
  simp only [run, body, List.length_append, List.length_tail, List.length_cons, selectionBudget]
  omega

end PDROC.BitVM.Log.InputLoad
