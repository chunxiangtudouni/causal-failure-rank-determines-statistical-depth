module

public import Paid.PDCompute_SolverSequenceBits_155
public import Paid.PDCompute_SolverScalarBits_152
public import Paid.PDCompute_SolverCandidateCode_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Discharge the finite arithmetic-value predicate for the ACTUAL six
candidate commands. The score bound has fixed depth and running best
does not appear among the arithmetic operands. -/
theorem candidateCommands_evaluated_bits (values : ℕ → Cell) (error charge good bad : ℚ) (L G budget : ℕ)
    (initial : HeaderValueBits values budget) (herror : values 26=.rational error) (hcharge : values 27=.rational charge)
    (hgood : values 21=.rational good) (hbad : values 22=.rational bad)
    (errorBits : ratEncodingBits error≤L) (chargeBits : ratEncodingBits charge≤L)
    (goodBits : ratEncodingBits good≤G) (badBits : ratEncodingBits bad≤G) (room : 1+64*(L+G+1)≤budget) :
    HeaderEvaluatedBits budget candidateCommands values := by
  let one:=Function.update values 28 (.rational 1)
  let two:=Function.update one 29 (.rational (1-error))
  let three:=Function.update two 30 (.rational ((1-error)*good))
  let four:=Function.update three 29 (.rational (error*bad))
  let five:=Function.update four 28 (.rational ((1-error)*good+error*bad))
  let six:=Function.update five 28 (.rational (charge+((1-error)*good+error*bad)))
  have numbers:=solverCandidate_intermediate_bits error charge good bad L G errorBits chargeBits goodBits badBits
  have oneBits : HeaderValueBits one budget := initial.update (by change 1+ratEncodingBits (1:ℚ)≤budget; omega)
  have twoBits : HeaderValueBits two budget := oneBits.update (by change 1+ratEncodingBits (1-error)≤budget; omega)
  have threeBits : HeaderValueBits three budget := twoBits.update (by change 1+ratEncodingBits ((1-error)*good)≤budget; omega)
  have fourBits : HeaderValueBits four budget := threeBits.update (by change 1+ratEncodingBits (error*bad)≤budget; omega)
  have fiveBits : HeaderValueBits five budget := fourBits.update (by change 1+ratEncodingBits ((1-error)*good+error*bad)≤budget; omega)
  have sixBits : HeaderValueBits six budget := fiveBits.update (by change 1+ratEncodingBits (charge+((1-error)*good+error*bad))≤budget; omega)
  refine ⟨one,?_,oneBits,two,?_,twoBits,three,?_,threeBits,four,?_,fourBits,five,?_,fiveBits,six,?_,sixBits,True.intro⟩
  all_goals simp [HeaderCommand.eval,one,two,three,four,five,six,herror,hcharge,hgood,hbad,Cell.rat?,RatOp.eval]

/-- SAME actual fixed54-op candidate trace, EVERY-prefix complete-state
operand bits and Header memory; all numerical guards above are proved
from real error/charge/good/bad values rather than a postulated run. -/
theorem candidateCode_trace_bits (program : Program) (input : List Cell) (before : State) (base n k budget L G : ℕ)
    (values : ℕ → Cell) (error charge good bad : ℚ) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (herror : values 26=.rational error) (hcharge : values 27=.rational charge)
    (hgood : values 21=.rational good) (hbad : values 22=.rational bad)
    (errorBits : ratEncodingBits error≤L) (chargeBits : ratEncodingBits charge≤L)
    (goodBits : ratEncodingBits good≤G) (badBits : ratEncodingBits bad≤G) (room : 1+64*(L+G+1)≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+54)≤budget)
    (fetch : FetchesCode program before.pc (headerCode candidateCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤1155 ∧
      Header after base (candidateValues values error charge good bad) ∧ after.register .fresh=.natural base ∧ after.pc=before.pc+54 ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have bounded:=candidateCommands_evaluated_bits values error charge good bad L G budget (HeaderValueBits.of_safe header safe)
    herror hcharge hgood hbad errorBits chargeBits goodBits badBits room
  have commandCost : 165*(candidateCommands.length+1)=1155 := rfl
  simpa only [candidateCode_length,commandCost] using headerCode_trace_bits candidateCommands program input before base n k budget values
    (candidateValues values error charge good bad) candidateCommands_valid header fresh
    (candidateCommands_eval values error charge good bad herror hcharge hgood hbad) safe bounded addressBits pcBits fetch

end PDCompute.Solver
