module

public import Paid.PDCompute_SolverRuntimeCommands_085

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation

/-- Actual initialization for all M+1 scan iterations. Cache source and
penalty are read from their saved header slots, not compiled constants. -/
def scanResetCommands : List RuntimeCommand :=
  [.scalar (.constant 23 (.natural 0)),.scalar (.copy 2 24),.scalar (.constant 25 (.natural 0)),
   .scalar (.constant 46 (.natural 1)),.natural .add 0 46 39]

def scanResetValues (values : ℕ → Cell) (source : ℕ) (penalty : ℚ) : ℕ → Cell :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update values 23 (.natural 0)) 24 (.rational penalty)) 25 (.natural 0)) 46 (.natural 1))
      39 (.natural (source+1))

theorem scanResetCommands_valid : ∀ command ∈ scanResetCommands,command.Valid := by
  intro command member
  simp only [scanResetCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h <;> subst command <;>
    dsimp only [RuntimeCommand.Valid,HeaderCommand.Valid,headerWords] <;> decide

theorem scanResetCommands_eval (values : ℕ → Cell) (source : ℕ) (penalty : ℚ)
    (hsource : values 0=.natural source) (hpenalty : values 2=.rational penalty) :
    runtimeEval scanResetCommands values=some (scanResetValues values source penalty) := by
  simp [scanResetCommands,runtimeEval,RuntimeCommand.eval,HeaderCommand.eval,Cell.nat?,NatOp.eval,
    hsource,hpenalty,scanResetValues]

theorem scanResetValues_preserves (values : ℕ → Cell) (source slot : ℕ) (penalty : ℚ)
    (h23 : slot ≠ 23) (h24 : slot ≠ 24) (h25 : slot ≠ 25) (h39 : slot ≠ 39) (h46 : slot ≠ 46) :
    scanResetValues values source penalty slot=values slot := by
  simp only [scanResetValues,Function.update_of_ne h23,Function.update_of_ne h24,
    Function.update_of_ne h25,Function.update_of_ne h39,Function.update_of_ne h46]

end PDCompute.Solver
