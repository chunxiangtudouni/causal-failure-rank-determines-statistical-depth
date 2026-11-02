module

public import Paid.PDCompute_SolverEntryWriter_094

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

/-- The TWO fixed literal terminal blocks; the full program contains
both and chooses via real guards, never by host evaluation of input. -/
def terminalFieldsCommands (abandon : Bool) : List HeaderCommand :=
  [.constant 40 (.natural (if abandon then 1 else 0)),.constant 41 (.natural 0),.constant 42 (.natural 0),
   .constant 43 (.rational 0),.constant 44 (.rational 0),.constant 45 (.rational (if abandon then 1 else 0))]

def terminalFieldsValues (values : ℕ → Cell) (abandon : Bool) : ℕ → Cell :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update values 40 (.natural (if abandon then 1 else 0))) 41 (.natural 0)) 42 (.natural 0))
      43 (.rational 0)) 44 (.rational 0)) 45 (.rational (if abandon then 1 else 0))

theorem terminalFieldsCommands_valid (abandon : Bool) : ∀ command ∈ terminalFieldsCommands abandon,command.Valid := by
  intro command member
  simp only [terminalFieldsCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h <;> subst command <;> dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem terminalFieldsCommands_eval (abandon : Bool) (values : ℕ → Cell) :
    headerEval (terminalFieldsCommands abandon) values=some (terminalFieldsValues values abandon) := by
  simp [terminalFieldsCommands,headerEval,HeaderCommand.eval,terminalFieldsValues]

theorem terminalFieldsValues_dense (abandon : Bool) (values : ℕ → Cell) :
    DenseFields (terminalFieldsValues values abandon) (if abandon then abandonEntry else finishEntry) := by
  cases abandon <;> simp [DenseFields,List.range_succ,terminalFieldsValues,denseEncodeEntry,abandonEntry,finishEntry]

theorem terminalFields_trace_memory (abandon : Bool) (program : Program) (input : List Cell) (before : State)
    (base n k : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (fetch : FetchesCode program before.pc (headerCode (terminalFieldsCommands abandon))) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 1155 ∧ Header after base (terminalFieldsValues values abandon) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(headerCode (terminalFieldsCommands abandon)).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace,HeaderMemory before state base :=
  headerCode_trace_memory (terminalFieldsCommands abandon) program input before base n k values _
    (terminalFieldsCommands_valid abandon) header hbase (terminalFieldsCommands_eval abandon values) fetch

def finishRowFieldsCommands : List HeaderCommand := .copy 35 37::terminalFieldsCommands false

def finishRowFieldsValues (values : ℕ → Cell) : ℕ → Cell :=
  terminalFieldsValues (Function.update values 37 (values 35)) false

theorem finishRowFieldsCommands_valid : ∀ command ∈ finishRowFieldsCommands,command.Valid := by
  intro command member
  rcases List.mem_cons.mp member with first|later
  · subst command
    dsimp only [HeaderCommand.Valid,headerWords]
    decide
  · exact terminalFieldsCommands_valid false command later

theorem finishRowFieldsCommands_eval (values : ℕ → Cell) :
    headerEval finishRowFieldsCommands values=some (finishRowFieldsValues values) := by
  change headerEval (terminalFieldsCommands false) (Function.update values 37 (values 35))=
    some (terminalFieldsValues (Function.update values 37 (values 35)) false)
  exact terminalFieldsCommands_eval false (Function.update values 37 (values 35))

end PDCompute.Solver
