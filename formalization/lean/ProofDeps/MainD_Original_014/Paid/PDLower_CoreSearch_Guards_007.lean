module

public import Paid.PDLower_CoreSearch_Compare_006
public import Paid.PDLower_CoreSearch_MixturePrepare_003
public import Paid.PDLower_CoreSearch_MixtureRatio_004
public import Paid.PDLower_CoreSearch_MixtureFinish_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

/-- Actual zero producer for denominator comparison. In particular an
arbitrary old cell42 is not assumed to contain a rational zero. -/
def zeroLiteralCommands : List HeaderCommand := [.constant 42 (.rational 0)]

theorem zeroLiteral_trace (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (fetched : FetchesCode program before.pc (headerCode zeroLiteralCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤75 ∧
      Header after 0 (Function.update values 42 (.rational 0)) ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+4 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  have valid : ∀ command∈zeroLiteralCommands,command.Valid := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    dsimp only [HeaderCommand.Valid,headerWords]
    decide
  have targets : ∀ command∈zeroLiteralCommands,commandTarget command∈scalarRegion := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    decide
  have evaluated : headerEval zeroLiteralCommands values=some (Function.update values 42 (.rational 0)) := rfl
  have length : (headerCode zeroLiteralCommands).length=4 := rfl
  obtain ⟨trace,after,head,last,chain,cost,_run,afterHeader,afterFresh,pc,output,memory⟩ :=
    commands_trace_scalar zeroLiteralCommands program input before values _ valid targets header fresh evaluated fetched
  exact ⟨trace,after,head,last,chain,by simpa only [length] using cost,afterHeader,afterFresh,
    by simpa only [length] using pc,output,memory⟩

theorem denominatorGuard_trace (P : Parameters) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (denominator : values 30=.rational (P.solveRisk lower-P.solveRisk upper)) (zero : values 42=.rational 0)
    (fetched : FetchesCode program before.pc (comparisonStoredCode .equal 30 42)) :
    ∃ trace : List State,trace.head?=some before ∧
      trace.getLast?=some (comparisonStoredResult before 30 42 (decide (P.solveRisk lower-P.solveRisk upper=0))) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤165 ∧
      Header (comparisonStoredResult before 30 42 (decide (P.solveRisk lower-P.solveRisk upper=0))) 0
        (Function.update values 40 (.natural (if P.solveRisk lower-P.solveRisk upper=0 then 1 else 0))) ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  have same : (P.solveRisk lower-P.solveRisk upper==0)=decide (P.solveRisk lower-P.solveRisk upper=0) := by
    by_cases zero : P.solveRisk lower-P.solveRisk upper=0 <;> simp [zero]
  simpa only [Comparison.rat,same,decide_eq_true_eq] using
    comparisonStored_trace .equal 30 42 (P.solveRisk lower-P.solveRisk upper) 0 program input before values header
      (by decide) (by decide) denominator zero fresh fetched

/-- Exactly the ORIGINAL bracket stopping comparison, not a surrogate
duality/optimality criterion. Root owns the actual subsequent loop branch. -/
theorem bracketStopped_trace (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (gap : values 38=.rational ((upper.multiplier-lower.multiplier)*P.certificate.risk))
    (halfCost : values 41=.rational (P.mixtureCost fee lower upper/2))
    (fetched : FetchesCode program before.pc (comparisonStoredCode .lessEqual 38 41)) :
    ∃ trace : List State,trace.head?=some before ∧
      trace.getLast?=some (comparisonStoredResult before 38 41 (P.searchStopped fee (.bracket lower upper))) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤165 ∧
      Header (comparisonStoredResult before 38 41 (P.searchStopped fee (.bracket lower upper))) 0
        (Function.update values 40 (.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0))) ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  exact comparisonStored_trace .lessEqual 38 41 ((upper.multiplier-lower.multiplier)*P.certificate.risk)
    (P.mixtureCost fee lower upper/2) program input before values header (by decide) (by decide) gap halfCost fresh fetched

end PDLower.CoreSearch
