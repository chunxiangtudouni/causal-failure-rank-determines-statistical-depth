module

public import Paid.PDLower_CalibrationCompute_CalleeBits_118
public import Paid.PDLower_CalibrationCompute_CalleeRecords_083
public import Paid.PDLower_CalibrationCompute_BitEmbedding_101
public import Paid.PDROC_D27Prepare_Resources_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

/-- Full original emitting callee with execution, time, all-prefix
record space and all-prefix operand bits on ONE actual trace. The old
caller budget is an input carry, not an original-parameter bound on
arbitrary incoming scratch or output. -/
theorem callee_resources (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma : ℕ)
    (input : List Cell) (before : State)
    (arguments : CallArguments P base endpoints returnPC before)
    (initialSafe : SafeBits before callerBudget) (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma)
    (endpointHeap : HeapList before endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (separate : ∀ offset<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+offset∉workspace base P.certificate.M)
    (position : before.pc=labelAddress origin .enter) :
    ∃ (after : State) (trace : List State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun a b => step (locatedBlock origin (kernel origin)) input a=some b) ∧
      time (locatedBlock origin (kernel origin)) trace≤30000*(P.certificate.Q+1)*(P.certificate.M+1)^2 ∧
      Return P base returnPC before after ∧
      peakCells trace≤workingCells before+workspaceSize P.certificate.M+rowWidth P.certificate.M ∧
      peakOperandBits trace≤calleeOperandBudget P origin callerBudget Lgamma ∧
      ∀ state∈trace,SafeBits state (calleeOperandBudget P origin callerBudget Lgamma) := by
  obtain ⟨after,actual,returned⟩ :=
    callee_bits P origin base endpoints returnPC callerBudget Lgamma input before arguments initialSafe gammaBits endpointHeap separate position
  obtain ⟨trace,head,last,chain,cost,states⟩ := actual
  have contract := returned
  obtain ⟨_pc,_fresh,_old,_address,_index,_cache,output,frame⟩ := returned
  have peak := chain_peakCells_le_final (locatedBlock origin (kernel origin)) input
    (kernelLocated_step_live_mono origin input) trace after chain last
  have finalBound := frame.workingCells_le (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList) output
  rw [encodeCalibrationCache_length] at finalBound
  have operands := PDROC.D27Prepare.Resources.peakOperandBits_le_of_states trace
    (calleeOperandBudget P origin callerBudget Lgamma) states
  exact ⟨after,trace,head,last,chain,cost,contract,peak.trans finalBound,operands,states⟩

end PDLower.CalibrationCompute
