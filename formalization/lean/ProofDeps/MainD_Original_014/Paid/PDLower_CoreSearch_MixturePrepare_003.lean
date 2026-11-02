module

public import Paid.PDLower_CoreSearch_TargetMemory_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

/-- Straight ORIGINAL bracket arithmetic before the genuine denominator
branch. Cell41 is produced before any later ratio read;39 is set here,
so the block assumes no previous midpoint or initialized scratch. -/
def mixturePrepareCommands : List HeaderCommand :=
  [.rational .subtract 18 21 30,.rational .subtract 3 21 41,
   .rational .multiply 5 17 32,.rational .add 16 32 32,
   .rational .multiply 5 20 33,.rational .add 19 33 33,
   .rational .subtract 15 14 37,.rational .multiply 37 3 38,
   .constant 39 (.rational (1/2))]

def mixturePrepareValues (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (values : ℕ→Cell) : ℕ→Cell :=
  let one := Function.update values 30 (.rational (P.solveRisk lower-P.solveRisk upper))
  let two := Function.update one 41 (.rational (P.certificate.risk-P.solveRisk upper))
  let three := Function.update two 32 (.rational (fee*(P.solveRecord lower).repairs))
  let four := Function.update three 32 (.rational (P.solveCost fee lower))
  let five := Function.update four 33 (.rational (fee*(P.solveRecord upper).repairs))
  let six := Function.update five 33 (.rational (P.solveCost fee upper))
  let seven := Function.update six 37 (.rational (upper.multiplier-lower.multiplier))
  let eight := Function.update seven 38 (.rational ((upper.multiplier-lower.multiplier)*P.certificate.risk))
  Function.update eight 39 (.rational (1/2))

theorem mixturePrepareCommands_valid : ∀ command∈mixturePrepareCommands,command.Valid := by
  intro command member
  simp only [mixturePrepareCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same|same|same|same|same|same|same|same|same <;> subst command <;>
    dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem mixturePrepareCommands_targets : ∀ command∈mixturePrepareCommands,commandTarget command∈scalarRegion := by
  intro command member
  simp only [mixturePrepareCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same|same|same|same|same|same|same|same|same <;> subst command <;> decide

theorem mixturePrepareCode_length : (headerCode mixturePrepareCommands).length=84 := rfl

theorem mixturePrepareCommands_eval (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (values : ℕ→Cell)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper)) :
    headerEval mixturePrepareCommands values=some (mixturePrepareValues P fee lower upper values) := by
  simp [mixturePrepareCommands,headerEval,HeaderCommand.eval,Cell.rat?,RatOp.eval,mixturePrepareValues,
    risk,feeValue,lowerPrice,upperPrice,lowerObs,lowerRep,lowerRisk,upperObs,upperRep,upperRisk,solveCost]

theorem mixturePrepareValues_fields (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (values : ℕ→Cell) :
    mixturePrepareValues P fee lower upper values 30=.rational (P.solveRisk lower-P.solveRisk upper) ∧
    mixturePrepareValues P fee lower upper values 41=.rational (P.certificate.risk-P.solveRisk upper) ∧
    mixturePrepareValues P fee lower upper values 32=.rational (P.solveCost fee lower) ∧
    mixturePrepareValues P fee lower upper values 33=.rational (P.solveCost fee upper) ∧
    mixturePrepareValues P fee lower upper values 37=.rational (upper.multiplier-lower.multiplier) ∧
    mixturePrepareValues P fee lower upper values 38=.rational ((upper.multiplier-lower.multiplier)*P.certificate.risk) ∧
    mixturePrepareValues P fee lower upper values 39=.rational (1/2) := by simp [mixturePrepareValues]

/-- Real84-op straight preparation for the source mixtureCost and
searchStopped expression. Any actual typed lower/upper root records are
accepted: no optimality, reachable-bracket or successful-search premise. -/
theorem mixturePrepare_trace (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper))
    (fetched : FetchesCode program before.pc (headerCode mixturePrepareCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤1275 ∧
      Header after 0 (mixturePrepareValues P fee lower upper values) ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+84 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  obtain ⟨trace,after,head,last,chain,cost,_run,afterHeader,afterFresh,pc,output,memory⟩ :=
    commands_trace_scalar mixturePrepareCommands program input before values (mixturePrepareValues P fee lower upper values)
      mixturePrepareCommands_valid mixturePrepareCommands_targets header fresh
      (mixturePrepareCommands_eval P fee lower upper values risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk upperObs upperRep upperRisk) fetched
  exact ⟨trace,after,head,last,chain,by simpa only [mixturePrepareCode_length] using cost,afterHeader,afterFresh,
    by simpa only [mixturePrepareCode_length] using pc,output,memory⟩

end PDLower.CoreSearch
