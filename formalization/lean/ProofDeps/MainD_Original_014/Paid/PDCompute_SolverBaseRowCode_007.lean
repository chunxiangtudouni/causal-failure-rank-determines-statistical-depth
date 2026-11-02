module

public import Paid.PDCompute_SolverDenseLayout_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation

/-- Six actual stores write exactly the dense original finishEntry.
Address advances by six and the entry countdown decreases by one.
The final jump returns to the actual loop test, not a meta-level fold. -/
def baseRowBody (testPC : ℕ) : List Instruction :=
  [.constant .value (.natural 0),
   .store .address .value,.natOp .add .address .address .flag,
   .store .address .value,.natOp .add .address .address .flag,
   .store .address .value,.natOp .add .address .address .flag,
   .constant .value (.rational 0),
   .store .address .value,.natOp .add .address .address .flag,
   .store .address .value,.natOp .add .address .address .flag,
   .store .address .value,.natOp .add .address .address .flag,
   .natOp .subtract .index .index .flag,.jump testPC]

def baseRowCode (origin : ℕ) : List Instruction :=
  [.constant .flag (.natural 1),.branchZero .index (origin+18) (origin+2)]++baseRowBody (origin+1)

theorem baseRowBody_length (testPC : ℕ) : (baseRowBody testPC).length=16 := rfl
theorem baseRowCode_length (origin : ℕ) : (baseRowCode origin).length=18 := rfl

theorem baseRowCode_noInput (origin : ℕ) :
    ∀ instruction ∈ baseRowCode origin, PDMenu.ComputeFrame.NoInputInstruction instruction := by
  intro instruction hi
  simp only [baseRowCode,baseRowBody,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with h|h
  · rcases h with h|h <;> subst instruction <;> trivial
  · rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst instruction <;> trivial

end PDCompute.Solver
