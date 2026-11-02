module

public import Paid.PDLower_CalibrationCompute_OuterLoop_079
public import Paid.PDLower_CalibrationCompute_HeadFrame_075

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

theorem callee_cost_bound (Q M : ℕ) :
    1600+(13000*(Q+1)*(M+2)*(M+1)+420)≤30000*(Q+1)*(M+1)^2 := by
  let scale := (Q+1)*(M+1)^2
  have quadratic : (M+2)*(M+1)≤2*(M+1)^2 := by nlinarith
  have mainBound : 13000*(Q+1)*(M+2)*(M+1)≤26000*scale := by
    calc
      _ = 13000*(Q+1)*((M+2)*(M+1)) := by ring
      _ ≤ 13000*(Q+1)*(2*(M+1)^2) := Nat.mul_le_mul_left _ quadratic
      _ = _ := by dsimp [scale]; ring
  have positive : 0<scale := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have reserve : 2020≤4000*scale := by
    have scaled := Nat.mul_le_mul_left 4000 (Nat.succ_le_of_lt positive)
    exact (by decide : 2020≤4000).trans (by simpa only [Nat.mul_one] using scaled)
  calc
    _ = 13000*(Q+1)*(M+2)*(M+1)+2020 := by ring
    _ ≤ 26000*scale+4000*scale := Nat.add_le_add mainBound reserve
    _ = _ := by dsimp [scale]; ring

/-- The original entire outputting calibration callee. Its entry
premises are the actual scalar arguments and endpoint cache outside the
write region; arbitrary OLD live workspace cells are permitted. Every row,
loop, q, weight, cache store, output and indirect return is executed.
Operand-bit certificates are a separate all-prefix obligation. -/
theorem callee (P : Parameters) (origin base endpoints returnPC : ℕ) (input : List Cell) (before : State)
    (arguments : CallArguments P base endpoints returnPC before)
    (endpointHeap : HeapList before endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (separate : ∀ offset<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+offset∉workspace base P.certificate.M)
    (position : before.pc=labelAddress origin .enter) :
    ∃ after : State,Segment origin input before after (30000*(P.certificate.Q+1)*(P.certificate.M+1)^2) ∧
      Return P base returnPC before after := by
  let started := headResult origin P base before
  let header := Header.initial base endpoints returnPC P.certificate.M P.certificate.Q P.certificate.gamma
  obtain ⟨headRun,represented,pc,startedFresh,headOutput⟩ :=
    head_correct origin input P base endpoints returnPC before arguments position
  have headFrame : Frame before started base P.certificate.M := headResult_frame origin P base before
  have headEndpoints : HeapList started endpoints (encodeList encodeEndpoint P.endpointCache.toList) :=
    endpointHeap.memoryFrame _ headFrame separate
  have ready : OuterReady P base endpoints returnPC 0 header started := by
    refine ⟨represented,rfl,rfl,rfl,rfl,rfl,rfl,?_,startedFresh,headEndpoints,?_⟩
    · simp only [header,Header.initial,calibrationPrefix_zero,List.length_cons,List.length_nil]
    · exact headResult_cache origin P base before
  obtain ⟨after,extra,outerRun,returnPCValue,finalFresh,finalOld,finalAddress,finalIndex,cache,output,completion,outerFrame⟩ :=
    outerLoop P origin base endpoints returnPC 0 input started header ready pc (Nat.zero_le _) separate
  have complete : Segment origin input before after
      (1600+(13000*(P.certificate.Q+1)*(P.certificate.M+2)*(P.certificate.M+1-0)+420)) :=
    headRun.trans outerRun
  refine ⟨after,complete.mono ?_,returnPCValue,finalFresh,finalOld,finalAddress,finalIndex,cache,?_,headFrame.trans outerFrame⟩
  · simpa only [Nat.sub_zero] using callee_cost_bound P.certificate.Q P.certificate.M
  · rw [output,headOutput,List.append_assoc]
    rw [calibrationPrefix_zero] at completion
    rw [completion]

/-- Compatibility with the original standalone Entry, whose genuine
loader provides disjointness. The full caller above needs only endpoint
separation and may reuse dirty live workspace. -/
theorem callee_of_entry (P : Parameters) (origin base endpoints returnPC : ℕ) (input : List Cell) (before : State)
    (entry : Entry P base endpoints returnPC before)
    (position : before.pc=labelAddress origin .enter) :
    ∃ after : State,Segment origin input before after (30000*(P.certificate.Q+1)*(P.certificate.M+1)^2) ∧
      Return P base returnPC before after := by
  rcases entry with ⟨fresh,old,address,total,index,value,endpointHeap,disjoint⟩
  have separate (offset : ℕ) (inside : offset<(encodeList encodeEndpoint P.endpointCache.toList).length) :
      endpoints+offset∉workspace base P.certificate.M := by
    intro inWorkspace
    exact Finset.disjoint_left.mp disjoint (endpointHeap.1 offset inside) inWorkspace
  exact callee P origin base endpoints returnPC input before ⟨fresh,old,address,total,index,value⟩
    endpointHeap separate position

end PDLower.CalibrationCompute
