module

public import Paid.PDCompute_SolverEntryObjectives_073

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

/-- Literal original-ISA scalar expansion for the selected testing
entry's SIX working cells. Its original4/6 output is serialized later. -/
def testingFieldsCommands : List HeaderCommand :=
  [.constant 29 (.rational 1),.rational .subtract 29 26 29,
   .rational .multiply 29 10 43,.rational .multiply 26 31 30,
   .rational .add 43 30 43,.rational .add 27 43 43,
   .rational .multiply 29 11 44,.rational .multiply 26 32 30,.rational .add 44 30 44,
   .rational .multiply 29 12 45,.rational .multiply 26 33 30,.rational .add 45 30 45,
   .constant 40 (.natural 2),.copy 23 41,.copy 34 42]

def testingFieldsValues (values : ℕ → Cell) (error charge : ℚ) (good bad : MenuEntry)
    (level repairFlag : ℕ) : ℕ → Cell :=
  let a:=Function.update values 29 (.rational 1)
  let b:=Function.update a 29 (.rational (1-error))
  let c:=Function.update b 43 (.rational ((1-error)*good.observation))
  let d:=Function.update c 30 (.rational (error*bad.observation))
  let e:=Function.update d 43 (.rational ((1-error)*good.observation+error*bad.observation))
  let f:=Function.update e 43 (.rational (charge+((1-error)*good.observation+error*bad.observation)))
  let g:=Function.update f 44 (.rational ((1-error)*good.repairs))
  let h:=Function.update g 30 (.rational (error*bad.repairs))
  let i:=Function.update h 44 (.rational ((1-error)*good.repairs+error*bad.repairs))
  let j:=Function.update i 45 (.rational ((1-error)*good.failure))
  let l:=Function.update j 30 (.rational (error*bad.failure))
  let m:=Function.update l 45 (.rational ((1-error)*good.failure+error*bad.failure))
  let o:=Function.update m 40 (.natural 2)
  Function.update (Function.update o 41 (.natural level)) 42 (.natural repairFlag)

theorem testingFieldsCommands_valid : ∀ command ∈ testingFieldsCommands, command.Valid := by
  intro command member
  simp only [testingFieldsCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst command <;>
    dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem testingFieldsCommands_eval (values : ℕ → Cell) (error charge : ℚ) (good bad : MenuEntry)
    (level repairFlag : ℕ)
    (he : values 26=.rational error) (hc : values 27=.rational charge)
    (hgo : values 10=.rational good.observation) (hgr : values 11=.rational good.repairs)
    (hgf : values 12=.rational good.failure)
    (hbo : values 31=.rational bad.observation) (hbr : values 32=.rational bad.repairs)
    (hbf : values 33=.rational bad.failure)
    (hl : values 23=.natural level) (hb : values 34=.natural repairFlag) :
    headerEval testingFieldsCommands values=some (testingFieldsValues values error charge good bad level repairFlag) := by
  simp [testingFieldsCommands,headerEval,HeaderCommand.eval,Cell.rat?,RatOp.eval,
    he,hc,hgo,hgr,hgf,hbo,hbr,hbf,hl,hb,testingFieldsValues]

theorem testingFieldsValues_original (P : Parameters) (values : ℕ → Cell) (fee penalty : ℚ)
    (previous : MenuRow) (tools level : ℕ) :
    let endpoint:=P.cachedEndpoint P.endpointCache level
    let bad:=P.menuBadBranch fee penalty previous tools
    let fields:=testingFieldsValues values endpoint.error endpoint.charge (previous.getD tools abandonEntry) bad.2
      level (if bad.1=.repair then 1 else 0)
    (List.range 6).map (fun offset => fields (40+offset))=
      denseEncodeEntry (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level) := by
  simp [List.range_succ,testingFieldsValues,denseEncodeEntry,Parameters.cachedMenuTestingEntry,add_assoc]

theorem testingFields_trace_memory (program : Program) (input : List Cell) (before : State)
    (base n k : ℕ) (values : ℕ → Cell) (error charge : ℚ) (good bad : MenuEntry)
    (level repairFlag : ℕ)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (he : values 26=.rational error) (hc : values 27=.rational charge)
    (hgo : values 10=.rational good.observation) (hgr : values 11=.rational good.repairs)
    (hgf : values 12=.rational good.failure)
    (hbo : values 31=.rational bad.observation) (hbr : values 32=.rational bad.repairs)
    (hbf : values 33=.rational bad.failure)
    (hl : values 23=.natural level) (hb : values 34=.natural repairFlag)
    (fetch : FetchesCode program before.pc (headerCode testingFieldsCommands)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2640 ∧ Header after base (testingFieldsValues values error charge good bad level repairFlag) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(headerCode testingFieldsCommands).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base :=
  headerCode_trace_memory testingFieldsCommands program input before base n k values _ testingFieldsCommands_valid header hbase
    (testingFieldsCommands_eval values error charge good bad level repairFlag he hc hgo hgr hgf hbo hbr hbf hl hb) fetch

end PDCompute.Solver
