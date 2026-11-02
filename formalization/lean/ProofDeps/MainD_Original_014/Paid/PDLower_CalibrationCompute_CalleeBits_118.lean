module

public import Paid.PDLower_CalibrationCompute_Callee_080
public import Paid.PDLower_CalibrationCompute_HeadBits_108
public import Paid.PDLower_CalibrationCompute_OuterLoopBits_117

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

/-- The original complete emitting callee, including all M+1 outer
levels and the actual indirect return. One trace carries the original
time bound, every-prefix full stateCellBits, original cache and appended
output. Old live workspace and arbitrary old output are allowed. -/
theorem callee_bits (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma : ℕ)
    (input : List Cell) (before : State)
    (arguments : CallArguments P base endpoints returnPC before)
    (initialSafe : SafeBits before callerBudget) (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma)
    (endpointHeap : HeapList before endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (separate : ∀ offset<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+offset∉workspace base P.certificate.M)
    (position : before.pc=labelAddress origin .enter) :
    ∃ after : State,BitSegment origin input before after (30000*(P.certificate.Q+1)*(P.certificate.M+1)^2)
      (calleeOperandBudget P origin callerBudget Lgamma) ∧ Return P base returnPC before after := by
  let started := headResult origin P base before
  let header := Header.initial base endpoints returnPC P.certificate.M P.certificate.Q P.certificate.gamma
  obtain ⟨_headFunctional,represented,pc,startedFresh,headOutput⟩ :=
    head_correct origin input P base endpoints returnPC before arguments position
  have headRun := head_bits P origin input base endpoints returnPC callerBudget Lgamma before arguments initialSafe gammaBits position
  have headFrame : Frame before started base P.certificate.M := headResult_frame origin P base before
  have headEndpoints : HeapList started endpoints (encodeList encodeEndpoint P.endpointCache.toList) :=
    endpointHeap.memoryFrame _ headFrame separate
  have ready : OuterReady P base endpoints returnPC 0 header started := by
    refine ⟨represented,rfl,rfl,rfl,rfl,rfl,rfl,?_,startedFresh,headEndpoints,?_⟩
    · simp only [header,Header.initial,calibrationPrefix_zero,List.length_cons,List.length_nil]
    · exact headResult_cache origin P base before
  obtain ⟨after,extra,outerRun,returnPCValue,finalFresh,finalOld,finalAddress,finalIndex,cache,output,completion,outerFrame⟩ :=
    outerLoop_bits P origin base endpoints returnPC callerBudget Lgamma 0 input before started header ready
      arguments initialSafe gammaBits headRun.final pc (Nat.zero_le _) separate
  have complete : BitSegment origin input before after
      (1600+(13000*(P.certificate.Q+1)*(P.certificate.M+2)*(P.certificate.M+1-0)+420))
      (calleeOperandBudget P origin callerBudget Lgamma) := headRun.trans outerRun
  refine ⟨after,complete.mono ?_,returnPCValue,finalFresh,finalOld,finalAddress,finalIndex,cache,?_,headFrame.trans outerFrame⟩
  · simpa only [Nat.sub_zero] using callee_cost_bound P.certificate.Q P.certificate.M
  · rw [output,headOutput,List.append_assoc]
    rw [calibrationPrefix_zero] at completion
    rw [completion]

end PDLower.CalibrationCompute
