module

public import Paid.PDCompute_SolverSequenceBits_155
public import Paid.PDCompute_SolverScalarBits_152
public import Paid.PDCompute_SolverEntryObjectives_073

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

theorem goodObjectiveCommands_evaluated_bits (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry) (S L T budget : ℕ)
    (initial : HeaderValueBits values budget) (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (hobs : values 10=.rational entry.observation) (hrep : values 11=.rational entry.repairs) (hfail : values 12=.rational entry.failure)
    (observation : ratEncodingBits entry.observation≤S) (repairs : ratEncodingBits entry.repairs≤S) (failure : ratEncodingBits entry.failure≤S)
    (feeBits : ratEncodingBits fee≤L) (penaltyBits : ratEncodingBits penalty≤T) (room : 1+16*(S+L+T+1)≤budget) :
    HeaderEvaluatedBits budget goodObjectiveCommands values := by
  let first:=Function.update values 29 (.rational (fee*entry.repairs))
  let second:=Function.update first 30 (.rational (penalty*entry.failure))
  let third:=Function.update second 21 (.rational (entry.observation+fee*entry.repairs))
  let fourth:=Function.update third 21 (.rational (entry.objective fee penalty))
  have numbers:=solverObjective_intermediate_bits entry fee penalty S L T observation repairs failure feeBits penaltyBits
  have firstBits : HeaderValueBits first budget := initial.update (by change 1+ratEncodingBits (fee*entry.repairs)≤budget; omega)
  have secondBits : HeaderValueBits second budget := firstBits.update (by change 1+ratEncodingBits (penalty*entry.failure)≤budget; omega)
  have thirdBits : HeaderValueBits third budget := secondBits.update (by change 1+ratEncodingBits (entry.observation+fee*entry.repairs)≤budget; omega)
  have fourthBits : HeaderValueBits fourth budget := thirdBits.update (by change 1+ratEncodingBits (entry.objective fee penalty)≤budget; omega)
  refine ⟨first,?_,firstBits,second,?_,secondBits,third,?_,thirdBits,fourth,?_,fourthBits,True.intro⟩
  all_goals simp [HeaderCommand.eval,first,second,third,fourth,hfee,hpenalty,hobs,hrep,hfail,Cell.rat?,RatOp.eval,MenuEntry.objective]

/-- Original40-op loaded-good objective block, actual prefix memory and
SAME complete-state SafeBits. The original stored-field encoding bound
and real fee/penalty bits discharge every arithmetic guard. -/
theorem goodObjective_trace_bits (program : Program) (input : List Cell) (before : State) (base n k budget S L T : ℕ)
    (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (hobs : values 10=.rational entry.observation) (hrep : values 11=.rational entry.repairs) (hfail : values 12=.rational entry.failure)
    (observation : ratEncodingBits entry.observation≤S) (repairs : ratEncodingBits entry.repairs≤S) (failure : ratEncodingBits entry.failure≤S)
    (feeBits : ratEncodingBits fee≤L) (penaltyBits : ratEncodingBits penalty≤T) (room : 1+16*(S+L+T+1)≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+40)≤budget)
    (fetch : FetchesCode program before.pc (headerCode goodObjectiveCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤825 ∧
      Header after base (goodObjectiveValues values fee penalty entry.observation entry.repairs entry.failure) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+40 ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have bounded:=goodObjectiveCommands_evaluated_bits values fee penalty entry S L T budget (HeaderValueBits.of_safe header safe)
    hfee hpenalty hobs hrep hfail observation repairs failure feeBits penaltyBits room
  have codeLength : (headerCode goodObjectiveCommands).length=40 := rfl
  have commandCost : 165*(goodObjectiveCommands.length+1)=825 := rfl
  simpa only [codeLength,commandCost] using headerCode_trace_bits goodObjectiveCommands program input before base n k budget values
    (goodObjectiveValues values fee penalty entry.observation entry.repairs entry.failure) goodObjectiveCommands_valid header fresh
    (goodObjectiveCommands_eval values fee penalty entry hfee hpenalty hobs hrep hfail) safe bounded addressBits pcBits fetch

end PDCompute.Solver
