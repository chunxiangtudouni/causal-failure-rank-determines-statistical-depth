module

public import Paid.PDCompute_SolverEntryObjectives_073

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def zeroBadCommands : List HeaderCommand :=
  [.constant 31 (.rational 0),.constant 32 (.rational 0),.constant 33 (.rational 1),
   .constant 34 (.natural 0),.copy 2 22]

def zeroBadValues (values : ℕ → Cell) (penalty : ℚ) : ℕ → Cell :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update values 31 (.rational 0)) 32 (.rational 0)) 33 (.rational 1)) 34 (.natural 0)) 22 (.rational penalty)

theorem zeroBadCommands_valid : ∀ command ∈ zeroBadCommands, command.Valid := by
  intro command member
  simp only [zeroBadCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h <;> subst command <;> dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem zeroBadCommands_eval (values : ℕ → Cell) (penalty : ℚ) (hpenalty : values 2=.rational penalty) :
    headerEval zeroBadCommands values=some (zeroBadValues values penalty) := by
  simp [zeroBadCommands,headerEval,HeaderCommand.eval,hpenalty,zeroBadValues]

theorem zeroBadValues_original (P : Parameters) (values : ℕ → Cell) (fee penalty : ℚ) (previous : MenuRow) :
    zeroBadValues values penalty 31=.rational (P.menuBadBranch fee penalty previous 0).2.observation ∧
    zeroBadValues values penalty 32=.rational (P.menuBadBranch fee penalty previous 0).2.repairs ∧
    zeroBadValues values penalty 33=.rational (P.menuBadBranch fee penalty previous 0).2.failure ∧
    zeroBadValues values penalty 34=.natural 0 ∧
    zeroBadValues values penalty 22=.rational ((P.menuBadBranch fee penalty previous 0).2.objective fee penalty) := by
  simp [Parameters.menuBadBranch,zeroBadValues,abandonEntry,MenuEntry.objective]

theorem zeroBad_trace_memory (program : Program) (input : List Cell) (before : State)
    (base n k : ℕ) (values : ℕ → Cell) (penalty : ℚ)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hpenalty : values 2=.rational penalty)
    (fetched : FetchesCode program before.pc (headerCode zeroBadCommands)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 990 ∧ Header after base (zeroBadValues values penalty) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(headerCode zeroBadCommands).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base :=
  headerCode_trace_memory zeroBadCommands program input before base n k values _ zeroBadCommands_valid header hbase
    (zeroBadCommands_eval values penalty hpenalty) fetched

theorem goodObjective_trace_memory (program : Program) (input : List Cell) (before : State)
    (base n k : ℕ) (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (hobs : values 10=.rational entry.observation) (hrep : values 11=.rational entry.repairs)
    (hfail : values 12=.rational entry.failure)
    (fetched : FetchesCode program before.pc (headerCode goodObjectiveCommands)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 825 ∧ Header after base (goodObjectiveValues values fee penalty entry.observation entry.repairs entry.failure) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(headerCode goodObjectiveCommands).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base :=
  headerCode_trace_memory goodObjectiveCommands program input before base n k values _ goodObjectiveCommands_valid header hbase
    (goodObjectiveCommands_eval values fee penalty entry hfee hpenalty hobs hrep hfail) fetched

end PDCompute.Solver
