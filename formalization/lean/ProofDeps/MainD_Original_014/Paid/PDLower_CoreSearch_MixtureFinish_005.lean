module

public import Paid.PDLower_CoreSearch_TargetMemory_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

/-- After the genuine ratio/zero branch, compute the ORIGINAL mixture
cost and its half. The stop left-hand side38 is deliberately preserved. -/
def mixtureFinishCommands : List HeaderCommand :=
  [.constant 41 (.rational 1),.rational .subtract 41 31 41,
   .rational .multiply 41 33 34,.rational .multiply 31 32 35,
   .rational .add 35 34 36,.constant 39 (.rational (1/2)),.rational .multiply 36 39 41]

def mixtureFinishValues (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (values : ℕ→Cell) : ℕ→Cell :=
  let one := Function.update values 41 (.rational 1)
  let two := Function.update one 41 (.rational (1-P.mixtureWeight lower upper))
  let three := Function.update two 34 (.rational ((1-P.mixtureWeight lower upper)*P.solveCost fee upper))
  let four := Function.update three 35 (.rational (P.mixtureWeight lower upper*P.solveCost fee lower))
  let five := Function.update four 36 (.rational (P.mixtureCost fee lower upper))
  let six := Function.update five 39 (.rational (1/2))
  Function.update six 41 (.rational (P.mixtureCost fee lower upper/2))

theorem mixtureFinish_valid : ∀ command∈mixtureFinishCommands,command.Valid := by
  intro command member
  simp only [mixtureFinishCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same|same|same|same|same|same|same <;> subst command <;>
    dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem mixtureFinish_targets : ∀ command∈mixtureFinishCommands,commandTarget command∈scalarRegion := by
  intro command member
  simp only [mixtureFinishCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same|same|same|same|same|same|same <;> subst command <;> decide

theorem mixtureFinish_length : (headerCode mixtureFinishCommands).length=58 := rfl

theorem mixtureFinish_eval (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (values : ℕ→Cell)
    (ratio : values 31=.rational (P.mixtureWeight lower upper))
    (lowerCost : values 32=.rational (P.solveCost fee lower)) (upperCost : values 33=.rational (P.solveCost fee upper)) :
    headerEval mixtureFinishCommands values=some (mixtureFinishValues P fee lower upper values) := by
  simp [mixtureFinishCommands,headerEval,HeaderCommand.eval,Cell.rat?,RatOp.eval,mixtureFinishValues,
    ratio,lowerCost,upperCost,mixtureCost,div_eq_mul_inv]

theorem mixtureFinish_fields (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (values : ℕ→Cell) :
    mixtureFinishValues P fee lower upper values 36=.rational (P.mixtureCost fee lower upper) ∧
    mixtureFinishValues P fee lower upper values 41=.rational (P.mixtureCost fee lower upper/2) ∧
    mixtureFinishValues P fee lower upper values 38=values 38 := by simp [mixtureFinishValues]

theorem mixtureFinish_trace (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (ratio : values 31=.rational (P.mixtureWeight lower upper))
    (lowerCost : values 32=.rational (P.solveCost fee lower)) (upperCost : values 33=.rational (P.solveCost fee upper))
    (fetched : FetchesCode program before.pc (headerCode mixtureFinishCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤885 ∧
      Header after 0 (mixtureFinishValues P fee lower upper values) ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+58 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  obtain ⟨trace,after,head,last,chain,cost,_run,afterHeader,afterFresh,pc,output,memory⟩ :=
    commands_trace_scalar mixtureFinishCommands program input before values (mixtureFinishValues P fee lower upper values)
      mixtureFinish_valid mixtureFinish_targets header fresh (mixtureFinish_eval P fee lower upper values ratio lowerCost upperCost) fetched
  exact ⟨trace,after,head,last,chain,by simpa only [mixtureFinish_length] using cost,afterHeader,afterFresh,
    by simpa only [mixtureFinish_length] using pc,output,memory⟩

end PDLower.CoreSearch
