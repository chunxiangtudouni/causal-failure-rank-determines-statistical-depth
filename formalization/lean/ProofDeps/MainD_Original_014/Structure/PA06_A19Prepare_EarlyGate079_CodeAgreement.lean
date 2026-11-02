module

public import Structure.PA06_A19Prepare_EarlyGate079_Program
public import PaperProofs.Structure.PackingProgramPrefix

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual-code agreement beyond the replaced first10 ops.
The run theorem consumes an explicit internal old-run PC window, which
the checker control certificate will discharge. Endpoint equality alone
is never used to infer equality of runs of different whole programs. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawIncidenceLaminarRAM RawTreePreprocessingClaims

theorem program_append (handlerPC : Nat) (left right : List PackingOp) (bound : 10 ≤ left.length) :
    program handlerPC (left ++ right) = program handlerPC left ++ right := by
  simp only [program, List.drop_append_of_le_length bound, List.append_assoc]

theorem slot_after_ten (handlerPC : Nat) (old : List PackingOp) (index : Nat)
    (lo : 10 ≤ index) (hi : index < old.length) :
    (program handlerPC old)[index]'(by rw [program_length handlerPC old (by omega)]; exact hi) =
      old[index] := by
  change (head handlerPC ++ old.drop 10)[index]'(by
    simp only [List.length_append, head_length, List.length_drop]
    omega) = old[index]
  rw [List.getElem_append_right (by rw [head_length]; exact lo)]
  simp only [head_length, List.getElem_drop]
  congr 1
  omega

theorem natFetch_after_ten (handlerPC : Nat) (old : List PackingOp) (index : Nat)
    (lo : 10 ≤ index) (hi : index < old.length) :
    natFetch (program handlerPC old) (5 * index) = natFetch old (5 * index) := by
  rw [natFetch_body (program handlerPC old) index (by rw [program_length handlerPC old (by omega)]; exact hi),
    natFetch_body old index hi, slot_after_ten handlerPC old index lo hi]

theorem natStep_after_ten (rom : PhysicalROM) (handlerPC : Nat) (old : List PackingOp)
    (state : NatState) (index : Nat) (lo : 10 ≤ index) (hi : index < old.length)
    (pc : state.pc = 5 * index) :
    natStep rom (program handlerPC old) state = natStep rom old state := by
  simp only [natStep, pc, natFetch_after_ten handlerPC old index lo hi]

theorem natRun_of_old_window (rom : PhysicalROM) (handlerPC : Nat) (old : List PackingOp)
    (before : NatState) (count : Nat)
    (window : ∀ clock < count, ∃ index, 10 ≤ index ∧ index < old.length ∧
      (natRun rom old clock before).pc = 5 * index) :
    natRun rom (program handlerPC old) count before = natRun rom old count before := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have beforeEq := ih (by intro clock bound; exact window clock (by omega))
      rw [natRun_succ, natRun_succ, beforeEq]
      obtain ⟨index, lo, hi, pc⟩ := window count (by omega)
      exact natStep_after_ten rom handlerPC old _ index lo hi pc

end PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079
