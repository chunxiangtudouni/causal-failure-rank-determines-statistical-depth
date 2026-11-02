module

public import Paid.PDCompute_SolverConditionalHeader_072

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation

/-- The six genuinely read good-entry cells occupy slots7--12. -/
def goodObjectiveCommands : List HeaderCommand :=
  [.rational .multiply 5 11 29,.rational .multiply 2 12 30,
   .rational .add 10 29 21,.rational .add 21 30 21]

def goodObjectiveValues (values : ℕ → Cell) (fee penalty observation repairs failure : ℚ) : ℕ → Cell :=
  let first:=Function.update values 29 (.rational (fee*repairs))
  let second:=Function.update first 30 (.rational (penalty*failure))
  let third:=Function.update second 21 (.rational (observation+fee*repairs))
  Function.update third 21 (.rational (observation+fee*repairs+penalty*failure))

theorem goodObjectiveCommands_valid : ∀ command ∈ goodObjectiveCommands, command.Valid := by
  intro command member
  simp only [goodObjectiveCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h <;> subst command <;> dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem goodObjectiveCommands_eval (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry)
    (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (hobs : values 10=.rational entry.observation) (hrep : values 11=.rational entry.repairs)
    (hfail : values 12=.rational entry.failure) :
    headerEval goodObjectiveCommands values=
      some (goodObjectiveValues values fee penalty entry.observation entry.repairs entry.failure) := by
  simp [goodObjectiveCommands,headerEval,HeaderCommand.eval,Cell.rat?,RatOp.eval,
    hfee,hpenalty,hobs,hrep,hfail,goodObjectiveValues]

theorem goodObjectiveValues_objective (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry) :
    goodObjectiveValues values fee penalty entry.observation entry.repairs entry.failure 21=
      .rational (entry.objective fee penalty) := rfl

/-- The actually read preceding-tools entry uses slots13--18. The
candidate repair stats are retained in40--42 while31--34 initially hold
the genuine abandon branch. No final answer is supplied to this code. -/
def badPreparationCommands : List HeaderCommand :=
  [.copy 16 40,.constant 29 (.rational 1),.rational .add 29 17 41,.copy 18 42,
   .rational .multiply 5 41 29,.rational .multiply 2 42 30,
   .rational .add 40 29 28,.rational .add 28 30 28,
   .constant 31 (.rational 0),.constant 32 (.rational 0),.constant 33 (.rational 1),
   .constant 34 (.natural 0),.copy 2 22,.copy 2 24]

def badPreparationValues (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry) : ℕ → Cell :=
  let one:=Function.update values 40 (.rational entry.observation)
  let two:=Function.update one 29 (.rational 1)
  let three:=Function.update two 41 (.rational (1+entry.repairs))
  let four:=Function.update three 42 (.rational entry.failure)
  let five:=Function.update four 29 (.rational (fee*(1+entry.repairs)))
  let six:=Function.update five 30 (.rational (penalty*entry.failure))
  let seven:=Function.update six 28 (.rational (entry.observation+fee*(1+entry.repairs)))
  let eight:=Function.update seven 28 (.rational ((repairEntry entry).objective fee penalty))
  let nine:=Function.update eight 31 (.rational 0)
  let ten:=Function.update nine 32 (.rational 0)
  let eleven:=Function.update ten 33 (.rational 1)
  let twelve:=Function.update eleven 34 (.natural 0)
  Function.update (Function.update twelve 22 (.rational penalty)) 24 (.rational penalty)

theorem badPreparationCommands_valid : ∀ command ∈ badPreparationCommands, command.Valid := by
  intro command member
  simp only [badPreparationCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst command <;>
    dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem badPreparationCommands_eval (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry)
    (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (hobs : values 16=.rational entry.observation) (hrep : values 17=.rational entry.repairs)
    (hfail : values 18=.rational entry.failure) :
    headerEval badPreparationCommands values=some (badPreparationValues values fee penalty entry) := by
  simp [badPreparationCommands,headerEval,HeaderCommand.eval,Cell.rat?,RatOp.eval,
    hfee,hpenalty,hobs,hrep,hfail,badPreparationValues,repairEntry,MenuEntry.objective]

def acceptRepairCommands : List HeaderCommand :=
  [.copy 40 31,.copy 41 32,.copy 42 33,.constant 34 (.natural 1),.copy 28 22]

def acceptRepairValues (values : ℕ → Cell) : ℕ → Cell :=
  let first:=Function.update values 31 (values 40)
  let second:=Function.update first 32 (values 41)
  let third:=Function.update second 33 (values 42)
  let fourth:=Function.update third 34 (.natural 1)
  Function.update fourth 22 (values 28)

theorem acceptRepairCommands_valid : ∀ command ∈ acceptRepairCommands, command.Valid := by
  intro command member
  simp only [acceptRepairCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h <;> subst command <;> dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem acceptRepairCommands_eval (values : ℕ → Cell) :
    headerEval acceptRepairCommands values=some (acceptRepairValues values) := by
  simp [acceptRepairCommands,headerEval,HeaderCommand.eval,acceptRepairValues]

theorem badChoice_original (P : Parameters) (values : ℕ → Cell) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) :
    let child:=previous.getD tools abandonEntry
    let prepared:=badPreparationValues values fee penalty child
    let chosen:=if (repairEntry child).objective fee penalty < penalty then acceptRepairValues prepared else prepared
    chosen 31=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.observation ∧
    chosen 32=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.repairs ∧
    chosen 33=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.failure ∧
    chosen 34=.natural (if (P.menuBadBranch fee penalty previous (tools+1)).1=.repair then 1 else 0) ∧
    chosen 22=.rational ((P.menuBadBranch fee penalty previous (tools+1)).2.objective fee penalty) := by
  dsimp only [Parameters.menuBadBranch]
  split_ifs <;> simp_all [acceptRepairValues,badPreparationValues,repairEntry,abandonEntry,MenuEntry.objective]

end PDCompute.Solver
