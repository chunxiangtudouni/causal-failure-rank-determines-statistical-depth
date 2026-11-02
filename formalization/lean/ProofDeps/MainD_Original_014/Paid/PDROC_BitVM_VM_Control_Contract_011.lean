module

public import Paid.PDROC_BitVM_VM_Control_Whole_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.Control.Indirect

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Common.IO

/-- Meaning of the actually produced finite flag for every original
Cell. This relation is proof-only, not an evaluator used by the machine. -/
def JumpMeaning (code : Program) (value : Cell) (choice : Option (PC code)) : Prop :=
  match value with
  | .natural query => SearchMeaning code query 0 choice
  | .rational _ => choice = none

def before (code : Program) (store : Store code) (contents : Stack → List Bool) : State code :=
  atEntry code (selectedIndex code) store contents

/-- TOTAL actual unknown-register indirect callee: one fixed finite
program before all input values, true source HALT, literal-PC selection
by actual byte equality, all used scratch physically cleared, and exact
frame for every other stack. No target/width/fuel/source-run is supplied.
The parent maps the actual local HALT to its normal caller return. -/
theorem cell_runs (code : Program) (pointer : Register) (value : Cell)
    (store : Store code) (contents : Stack → List Bool)
    (register : contents (registerSlot pointer) = encodeCellBits value) :
    ∃ (run : List (State code)) (after : State code),
      run.head? = some (before code store contents) ∧
      run.IsChain (fun first final => TM2.step (program code pointer) first = some final) ∧
      run.getLast? = some after ∧ TM2.step (program code pointer) after = none ∧ after.l = none ∧
      after.stk = cleared contents ∧ JumpMeaning code value (selected code after.var) ∧
      run.length ≤ scratchCost contents + 3 * (encodeCellBits value).length + code.size * candidateBudget code + 34 := by
  cases value with
  | natural query =>
    obtain ⟨nextStore, path, meaning, count⟩ := natural_path code pointer query store contents register
    let after : State code := ⟨none, nextStore, cleared contents⟩
    let run := before code store contents :: path.posts
    refine ⟨run, after, rfl, path.chain, path.last, rfl, rfl, rfl, meaning, ?_⟩
    have posts : path.posts.length ≤ scratchCost contents + 3 * (encodeNatBits query).length + code.size * candidateBudget code + 33 := count
    have cellLength : (encodeCellBits (.natural query)).length = (encodeNatBits query).length + 1 := rfl
    simp only [run, List.length_cons, cellLength]
    omega
  | rational query =>
    obtain ⟨nextStore, path, unselected, count⟩ := rational_path code pointer query store contents register
    let after : State code := ⟨none, nextStore, cleared contents⟩
    let run := before code store contents :: path.posts
    refine ⟨run, after, rfl, path.chain, path.last, rfl, rfl, rfl, unselected, ?_⟩
    have posts : path.posts.length = scratchCost contents + 29 := count
    simp only [run, List.length_cons]
    omega

/-- The observable finite flag on a real successful source next-fetch
is Some with its original Nat PC. The bound is derived by the parent's
full original RAMRuns/final-HALT theorem, not a new input qualification.
The proof-only Fin witness below is used to refute no-match; it is never
in program code or a replacement for the real comparison/selection. -/
theorem meaning_valid_pc (code : Program) (query : Nat) (choice : Option (PC code))
    (meaning : SearchMeaning code query 0 choice) (valid : query < code.size) :
    ∃ actual : PC code, choice = some actual ∧ actual.val = query := by
  cases choice with
  | some actual => exact ⟨actual, rfl, meaning.1⟩
  | none => exact False.elim (meaning ⟨query, valid⟩ (Nat.zero_le _) rfl)

theorem original_registers_preserved (code : Program) (pointer : Register) (value : Cell)
    (store : Store code) (contents : Stack → List Bool)
    (register : contents (registerSlot pointer) = encodeCellBits value) :
    ∃ (run : List (State code)) (after : State code),
      run.head? = some (before code store contents) ∧
      run.IsChain (fun first final => TM2.step (program code pointer) first = some final) ∧
      run.getLast? = some after ∧ after.l = none ∧
      (∀ reg : Register, after.stk (registerSlot reg) = contents (registerSlot reg)) ∧
      (∀ slot : Stack, (∀ index : Fin 4, slot ≠ clearSlot index) → after.stk slot = contents slot) ∧
      (∀ index : Fin 4, after.stk (clearSlot index) = []) ∧
      JumpMeaning code value (selected code after.var) ∧
      run.length ≤ scratchCost contents + 3 * (encodeCellBits value).length + code.size * candidateBudget code + 34 := by
  obtain ⟨run, after, head, chain, last, _, halt, data, meaning, count⟩ := cell_runs code pointer value store contents register
  refine ⟨run, after, head, chain, last, halt, ?_, ?_, ?_, meaning, count⟩
  · intro reg
    rw [data]
    exact cleared_register contents reg
  · intro slot outside
    rw [data]
    exact cleared_other contents slot outside
  · intro index
    rw [data]
    exact cleared_empty contents index

end PDROC.BitVM.VM.Control.Indirect
