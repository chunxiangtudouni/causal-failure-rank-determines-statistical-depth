module

public import Paid.PDLower_CoreSearch_TargetMemory_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

def mixtureRatioCommands : List HeaderCommand := [.rational .divide 41 30 31]
def mixtureZeroCommands : List HeaderCommand := [.constant 31 (.rational 0)]

theorem mixtureRatio_valid : ∀ command∈mixtureRatioCommands,command.Valid := by
  intro command member
  have same := List.mem_singleton.mp member
  subst command
  dsimp only [HeaderCommand.Valid,headerWords]
  decide

theorem mixtureRatio_targets : ∀ command∈mixtureRatioCommands,commandTarget command∈scalarRegion := by
  intro command member
  have same := List.mem_singleton.mp member
  subst command
  decide

theorem mixtureZero_valid : ∀ command∈mixtureZeroCommands,command.Valid := by
  intro command member
  have same := List.mem_singleton.mp member
  subst command
  dsimp only [HeaderCommand.Valid,headerWords]
  decide

theorem mixtureZero_targets : ∀ command∈mixtureZeroCommands,commandTarget command∈scalarRegion := by
  intro command member
  have same := List.mem_singleton.mp member
  subst command
  decide

theorem mixtureRatio_length : (headerCode mixtureRatioCommands).length=10 := rfl
theorem mixtureZero_length : (headerCode mixtureZeroCommands).length=4 := rfl

/-- Legal division side of the REAL denominator branch. Its premise is
the branch's actual nonzero value, never bracket optimality. -/
theorem mixtureRatio_trace (P : Parameters) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (numerator : values 41=.rational (P.certificate.risk-P.solveRisk upper))
    (denominator : values 30=.rational (P.solveRisk lower-P.solveRisk upper))
    (nonzero : P.solveRisk lower-P.solveRisk upper≠0)
    (fetched : FetchesCode program before.pc (headerCode mixtureRatioCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤165 ∧
      Header after 0 (Function.update values 31 (.rational (P.mixtureWeight lower upper))) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+10 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  have evaluated : headerEval mixtureRatioCommands values=some (Function.update values 31 (.rational (P.mixtureWeight lower upper))) := by
    simp [mixtureRatioCommands,headerEval,HeaderCommand.eval,Cell.rat?,RatOp.eval,numerator,denominator,nonzero,mixtureWeight]
  obtain ⟨trace,after,head,last,chain,cost,_run,afterHeader,afterFresh,pc,output,memory⟩ :=
    commands_trace_scalar mixtureRatioCommands program input before values _ mixtureRatio_valid mixtureRatio_targets header fresh evaluated fetched
  exact ⟨trace,after,head,last,chain,by simpa only [mixtureRatio_length] using cost,afterHeader,afterFresh,
    by simpa only [mixtureRatio_length] using pc,output,memory⟩

/-- Genuine zero branch implements the source's TOTAL Rat division,
whose result is0 at denominator0. Root composes the fetched guard; this
straight block neither assumes a successful ratio nor performs illegal
RatOp.divide on0. -/
theorem mixtureZero_trace (P : Parameters) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (zero : P.solveRisk lower-P.solveRisk upper=0)
    (fetched : FetchesCode program before.pc (headerCode mixtureZeroCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤75 ∧
      Header after 0 (Function.update values 31 (.rational (P.mixtureWeight lower upper))) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+4 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  have evaluated : headerEval mixtureZeroCommands values=some (Function.update values 31 (.rational (P.mixtureWeight lower upper))) := by
    simp [mixtureZeroCommands,headerEval,HeaderCommand.eval,mixtureWeight,zero]
  obtain ⟨trace,after,head,last,chain,cost,_run,afterHeader,afterFresh,pc,output,memory⟩ :=
    commands_trace_scalar mixtureZeroCommands program input before values _ mixtureZero_valid mixtureZero_targets header fresh evaluated fetched
  exact ⟨trace,after,head,last,chain,by simpa only [mixtureZero_length] using cost,afterHeader,afterFresh,
    by simpa only [mixtureZero_length] using pc,output,memory⟩

end PDLower.CoreSearch
