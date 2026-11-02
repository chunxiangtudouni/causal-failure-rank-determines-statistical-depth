module

public import Paid.PDCompute_SolverJump_096

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def choiceFirstPC (origin : ℕ) : ℕ := origin+8
def choiceSecondPC (first : ℕ → List Instruction) (origin : ℕ) : ℕ :=
  choiceFirstPC origin+(first (choiceFirstPC origin)).length+1
def choiceEndPC (first second : ℕ → List Instruction) (origin : ℕ) : ℕ :=
  choiceSecondPC first origin+(second (choiceSecondPC first origin)).length

/-- Both finite literal bodies are present in the program. Only the
original ISA guard selects a path at runtime. Body labels are generated
with their actual absolute entry, independent of all input data. -/
def choiceCode (guard : ℕ → ℕ → List Instruction) (first second : ℕ → List Instruction) (origin : ℕ) : List Instruction :=
  guard (choiceSecondPC first origin) (choiceFirstPC origin)++first (choiceFirstPC origin)++
    [.jump (choiceEndPC first second origin)]++second (choiceSecondPC first origin)

theorem choice_guard_fetch (guard : ℕ → ℕ → List Instruction) (first second : ℕ → List Instruction)
    (program : Program) (origin : ℕ) (fetch : FetchesCode program origin (choiceCode guard first second origin)) :
    FetchesCode program origin (guard (choiceSecondPC first origin) (choiceFirstPC origin)) :=
  fetch.append_left.append_left.append_left

theorem choice_first_fetch (guard : ℕ → ℕ → List Instruction) (first second : ℕ → List Instruction)
    (size : ∀ a b,(guard a b).length=8) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (choiceCode guard first second origin)) :
    FetchesCode program (choiceFirstPC origin) (first (choiceFirstPC origin)) := by
  have body:=fetch.append_left.append_left.append_right
  simpa only [size,choiceFirstPC] using body

theorem choice_jump_fetch (guard : ℕ → ℕ → List Instruction) (first second : ℕ → List Instruction)
    (size : ∀ a b,(guard a b).length=8) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (choiceCode guard first second origin)) :
    program[choiceFirstPC origin+(first (choiceFirstPC origin)).length]?=
      some (.jump (choiceEndPC first second origin)) := by
  have jumpFetch:=fetch.append_left.append_right
  have instruction:=jumpFetch 0 (by change 0 < 1; decide)
  simpa only [List.length_append,size,choiceFirstPC,Nat.add_zero,Nat.add_assoc,List.getElem?_cons_zero] using instruction

theorem choice_second_fetch (guard : ℕ → ℕ → List Instruction) (first second : ℕ → List Instruction)
    (size : ∀ a b,(guard a b).length=8) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (choiceCode guard first second origin)) :
    FetchesCode program (choiceSecondPC first origin) (second (choiceSecondPC first origin)) := by
  have body:=fetch.append_right
  simpa only [List.length_append,size,List.length_singleton,choiceSecondPC,choiceFirstPC,Nat.add_assoc] using body

theorem choiceCode_end (guard : ℕ → ℕ → List Instruction) (first second : ℕ → List Instruction)
    (size : ∀ a b,(guard a b).length=8) (origin : ℕ) :
    origin+(choiceCode guard first second origin).length=choiceEndPC first second origin := by
  simp only [choiceCode,List.length_append,size,List.length_singleton,choiceEndPC,choiceSecondPC,choiceFirstPC]
  omega

end PDCompute.Solver
