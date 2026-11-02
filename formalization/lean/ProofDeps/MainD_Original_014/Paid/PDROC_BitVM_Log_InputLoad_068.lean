module

public import Paid.PDROC_BitVM_Log_InputLoad_067
public import Paid.PDROC_BitVM_Log_HeapLoad_041

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.InputLoad

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Original RAM input semantics. BankAt is the actual physical relation
produced by BankMount54, carried by the intervening real opcode frames.
No host bank indexing is a transition; the program still compares Bool words. -/

abbrev RAMState := PaperProofs.Paid.Computation.State
abbrev ramLoaded := HeapLoad.ramLoaded

def BankAt (input : List Cell) (contents : Stack → List Bool) : Prop :=
  ∀ field : Fin 13, contents (BankDrain.bankSlot field) = BankMount.bankWords input field

theorem committed_register (field : Fin 13) (destination reg : Register) (contents : Stack → List Bool) :
    committed field destination contents (registerSlot reg) =
      if reg = destination then contents (BankDrain.bankSlot field) else contents (registerSlot reg) := by
  cases destination <;> cases reg <;>
    simp [committed, registerSlot, PaperProofs.Structure.LaminarTree.IndexedRAM.Register.word]

theorem committed_bank (field other : Fin 13) (destination : Register) (contents : Stack → List Bool) :
    committed field destination contents (BankDrain.bankSlot other) = contents (BankDrain.bankSlot other) := by
  have not26 := BankDrain.bankSlot_ne other 26 (by decide)
  have notReg := BankDrain.bankSlot_ne other (registerSlot destination) (Or.inr (registerSlot_bounds destination).1)
  simp only [committed, Function.update_of_ne not26, Function.update_of_ne notReg]

theorem marshalled_outside (query : ℕ) (contents : Stack → List Bool) (index : Stack)
    (outside : index.val < 24 ∨ 30 ≤ index.val) : marshalled query contents index = contents index := by
  have not26 : index ≠ 26 := by intro equal; subst index; norm_num at outside
  rw [marshalled, HeapLoad.marshalled, Function.update_of_ne not26]
  exact HeapLoad.preCleared_outside contents index outside

theorem committed_outside (field : Fin 13) (destination : Register) (contents : Stack → List Bool) (index : Stack)
    (notReg : index ≠ registerSlot destination) (not26 : index ≠ 26) :
    committed field destination contents index = contents index := by
  simp only [committed, Function.update_of_ne not26, Function.update_of_ne notReg]

theorem execute_input_nat (input : List Cell) (ram : RAMState) (pointer destination : Register) (query : ℕ) (value : Cell)
    (natural : ram.register pointer = .natural query) (found : input[query]? = some value) :
    Instruction.execute input (.loadInput destination pointer) ram = some (ramLoaded ram destination value) := by
  simp [Instruction.execute, natural, Cell.nat?, found, ramLoaded, HeapLoad.ramLoaded]

/-- The real bank word is read/copy-restored, and agrees with the original
source input read. The SAME run proves source execute and physical state. -/
theorem load_found_refinement (core : Bool) (input : List Cell) (ram : RAMState)
    (pointer destination : Register) (query : ℕ) (value : Cell) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (size : input.length = BankMount.fieldCount core) (bank : BankAt input before.stk)
    (natural : ram.register pointer = .natural query) (found : input[query]? = some value) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = true ∧
      Instruction.execute input (.loadInput destination pointer) ram = some (ramLoaded ram destination value) ∧
      RegistersRepresent (ramLoaded ram destination value) after ∧ BankAt input after.stk ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → index ≠ registerSlot destination →
        after.stk index = before.stk index) ∧
      run.length ≤ selectionBudget query before.stk + (encodeCellBits (ram.register destination)).length +
        2 * (encodeCellBits value).length + (encodeNatBits query).length + 12 := by
  have inInput : query < input.length := by
    by_contra absent
    have none : input[query]? = none := List.getElem?_eq_none (by omega)
    rw [found] at none
    cases none
  have range : query < BankMount.fieldCount core := by omega
  let field : Fin 13 := ⟨query, by have limit := BankMount.fieldCount_le core; omega⟩
  have bankWord : before.stk (BankDrain.bankSlot field) = encodeCellBits value := by
    rw [bank field]
    simp only [BankMount.bankWords, field, found, Option.map_some, Option.getD_some]
  have actualRegister : before.stk (registerSlot pointer) = encodeCellBits (.natural query) := by
    simpa only [natural] using represented pointer
  obtain ⟨run, after, head, chain, last, halt, done, flag, data, length⟩ :=
    found_runs core pointer destination query before.stk before.var actualRegister range
  have headBefore : run.head? = some before := by
    rcases before with ⟨label, vars, contents⟩
    change label = some startLabel at position
    subst label
    exact head
  refine ⟨run, after, headBefore, chain, last, halt, done, flag,
    execute_input_nat input ram pointer destination query value natural found, ?_, ?_, ?_, ?_⟩
  · intro reg
    rw [data, committed_register]
    by_cases same : reg = destination
    · subst reg
      rw [ite_eq_left rfl, marshalled_bank]
      change before.stk (BankDrain.bankSlot field) = _
      rw [bankWord]
      simp only [ramLoaded, HeapLoad.ramLoaded, PaperProofs.Paid.Computation.State.set, Function.update_self]
    · rw [ite_eq_right same, marshalled_register]
      simpa only [ramLoaded, HeapLoad.ramLoaded, PaperProofs.Paid.Computation.State.set, Function.update_of_ne same] using represented reg
  · intro other
    rw [data, committed_bank, marshalled_bank]
    exact bank other
  · intro index outside notReg
    have not26 : index ≠ 26 := by intro equal; subst index; norm_num at outside
    rw [data, committed_outside _ destination _ index notReg not26]
    exact marshalled_outside query before.stk index outside
  · change run.length ≤ foundBudget query field destination before.stk at length
    simpa only [foundBudget, bankWord, represented destination] using length

end PDROC.BitVM.Log.InputLoad
