module

public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDLower_CalibrationCompute_CallerEmbedding_073

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open PaperProofs.Paid.Computation PDMenu.ComputeFrame RootD27.Bits

namespace PDLower.CalibrationCompute

/-- The exact actual numeric trace is retained under real caller
embedding. No new fetch/scope premise or substitute existential trace. -/
theorem BitSegment.inCaller {beforeCode suffix : Program} {leftInput rightInput : List Cell}
    {before after : State} {timeBudget bitBudget : ℕ}
    (actual : BitSegment beforeCode.size leftInput before after timeBudget bitBudget) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun a b => step (beforeCode++kernel beforeCode.size++suffix) rightInput a=some b) ∧
      time (beforeCode++kernel beforeCode.size++suffix) trace≤timeBudget+15 ∧
      ∀ state∈trace,SafeBits state bitBudget := by
  obtain ⟨trace,head,last,chain,cost,states⟩ := actual
  have embedded := kernel_chain_in_caller beforeCode suffix leftInput rightInput trace
    (located_chain_scope beforeCode.size (kernel beforeCode.size) leftInput trace chain) chain
  exact ⟨trace,head,last,embedded.1,embedded.2.trans (Nat.add_le_add_right cost 15),states⟩

theorem BitSegment.inStandalone {leftInput rightInput : List Cell} {before after : State} {timeBudget bitBudget : ℕ}
    (actual : BitSegment 1 leftInput before after timeBudget bitBudget) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun a b => step calibrate rightInput a=some b) ∧
      time calibrate trace≤timeBudget+15 ∧ ∀ state∈trace,SafeBits state bitBudget := by
  exact actual.inCaller (beforeCode:=#[Instruction.jump mainStart]) (suffix:=bootstrap mainStart)

end PDLower.CalibrationCompute
