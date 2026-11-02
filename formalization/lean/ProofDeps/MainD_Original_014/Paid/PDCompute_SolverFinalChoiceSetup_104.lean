module

public import Paid.PDCompute_SolverSelectedChoice_103

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation

def finalChoiceCommands : List HeaderCommand :=
  [.copy 24 28,.copy 2 24]++terminalFieldsCommands true

def finalChoiceValues (values : ℕ → Cell) : ℕ → Cell :=
  terminalFieldsValues (Function.update (Function.update values 28 (values 24)) 24 (values 2)) true

theorem finalChoiceCommands_valid : ∀ command ∈ finalChoiceCommands,command.Valid := by
  intro command member
  rcases List.mem_append.mp member with first|last
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at first
    rcases first with same|same <;> subst command <;> dsimp only [HeaderCommand.Valid,headerWords] <;> decide
  · exact terminalFieldsCommands_valid true command last

theorem finalChoiceCommands_eval (values : ℕ → Cell) :
    headerEval finalChoiceCommands values=some (finalChoiceValues values) := by
  change headerEval (terminalFieldsCommands true)
    (Function.update (Function.update values 28 (values 24)) 24 (values 2))=_
  exact terminalFieldsCommands_eval true _

theorem finalChoiceValues_dense (values : ℕ → Cell) : DenseFields (finalChoiceValues values) abandonEntry :=
  terminalFieldsValues_dense true _

theorem finalChoiceValues_score (values : ℕ → Cell) : finalChoiceValues values 28=values 24 := by
  simp [finalChoiceValues,terminalFieldsValues]

theorem finalChoiceValues_cutoff (values : ℕ → Cell) : finalChoiceValues values 24=values 2 := by
  simp [finalChoiceValues,terminalFieldsValues]

theorem finalChoiceValues_preserves (values : ℕ → Cell) (slot : ℕ)
    (h24 : slot ≠ 24) (h28 : slot ≠ 28) (outside : slot < 40 ∨ 46 ≤ slot) :
    finalChoiceValues values slot=values slot := by
  have h40 : slot ≠ 40 := by omega
  have h41 : slot ≠ 41 := by omega
  have h42 : slot ≠ 42 := by omega
  have h43 : slot ≠ 43 := by omega
  have h44 : slot ≠ 44 := by omega
  have h45 : slot ≠ 45 := by omega
  simp only [finalChoiceValues,terminalFieldsValues,Function.update_of_ne h24,Function.update_of_ne h28,
    Function.update_of_ne h40,Function.update_of_ne h41,Function.update_of_ne h42,Function.update_of_ne h43,
    Function.update_of_ne h44,Function.update_of_ne h45]

end PDCompute.Solver
