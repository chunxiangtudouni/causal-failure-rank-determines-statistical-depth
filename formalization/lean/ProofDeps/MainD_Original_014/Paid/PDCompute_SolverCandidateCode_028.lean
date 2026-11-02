module

public import Paid.PDCompute_SolverHeaderSequence_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def candidateCommands : List HeaderCommand :=
  [.constant 28 (.rational 1),.rational .subtract 28 26 29,.rational .multiply 29 21 30,
    .rational .multiply 26 22 29,.rational .add 30 29 28,.rational .add 27 28 28]

def candidateValues (values : ℕ → Cell) (error charge good bad : ℚ) : ℕ → Cell :=
  let one := Function.update values 28 (.rational 1)
  let two := Function.update one 29 (.rational (1-error))
  let three := Function.update two 30 (.rational ((1-error)*good))
  let four := Function.update three 29 (.rational (error*bad))
  let five := Function.update four 28 (.rational ((1-error)*good+error*bad))
  Function.update five 28 (.rational (charge+((1-error)*good+error*bad)))

theorem candidateCommands_valid : ∀ command ∈ candidateCommands, command.Valid := by
  intro command member
  simp only [candidateCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h <;> subst command <;>
    dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem candidateCode_length : (headerCode candidateCommands).length=54 := rfl

theorem candidateCommands_eval (values : ℕ → Cell) (error charge good bad : ℚ)
    (herror : values 26=.rational error) (hcharge : values 27=.rational charge)
    (hgood : values 21=.rational good) (hbad : values 22=.rational bad) :
    headerEval candidateCommands values=some (candidateValues values error charge good bad) := by
  simp [candidateCommands,headerEval,HeaderCommand.eval,Cell.rat?,RatOp.eval,herror,hcharge,hgood,hbad,candidateValues]

theorem candidateValues_objective (values : ℕ → Cell) (error charge good bad : ℚ) :
    candidateValues values error charge good bad 28=.rational (charge+(1-error)*good+error*bad) := by
  simp only [candidateValues,Function.update_self]
  rw [add_assoc]

/-- Real fixed54-instruction candidate objective, consumed by the
strict-less endpoint scan. The original tie rule is proved in011. -/
theorem candidateCode_trace (program : Program) (input : List Cell) (before : State)
    (base n k : ℕ) (values : ℕ → Cell) (error charge good bad : ℚ)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (herror : values 26=.rational error) (hcharge : values 27=.rational charge)
    (hgood : values 21=.rational good) (hbad : values 22=.rational bad)
    (hfetch : FetchesCode program before.pc (headerCode candidateCommands)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 1155 ∧
      after.heap (base+28)=.rational (charge+(1-error)*good+error*bad) ∧
      Header after base (candidateValues values error charge good bad) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+54 ∧
      Frame before after base n k ∧ after.output=before.output := by
  obtain ⟨trace,after,hh,hl,hchain,ht,hr,hb,hpc,hf,ho,_⟩ :=
    headerCode_trace candidateCommands program input before base n k values _ candidateCommands_valid header hbase
      (candidateCommands_eval values error charge good bad herror hcharge hgood hbad) hfetch
  refine ⟨trace,after,hh,hl,hchain,ht,?_,hr,hb,hpc,hf,ho⟩
  exact (hr.value 28 (by decide)).trans (candidateValues_objective values error charge good bad)

end PDCompute.Solver
