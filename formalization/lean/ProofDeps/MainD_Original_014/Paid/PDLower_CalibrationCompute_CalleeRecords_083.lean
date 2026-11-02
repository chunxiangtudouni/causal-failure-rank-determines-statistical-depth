module

public import Paid.PDLower_CalibrationCompute_Callee_080
public import Paid.PDLower_CalibrationCompute_CalibrateSpace_066
public import Paid.PDLower_CalibrationCompute_CallerEmbedding_073

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

theorem original_Q_positive (P : Parameters) : 0<P.certificate.Q := by
  have ceiling : ((P.certificate.M : ℚ)+1)/P.certificate.gamma≤(P.certificate.Q : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast P.Q_ge_menu_ceil)
  have numerator : (0 : ℚ)<(P.certificate.M : ℚ)+1 := by positivity
  have positive : (0 : ℚ)<(P.certificate.Q : ℚ) :=
    (div_pos numerator P.certificate.gamma_pos).trans_le ceiling
  exact_mod_cast positive

theorem located_nonreleasing (origin : ℕ) (code : Program)
    (safe : ∀ instruction∈code.toList,PDROC.CalibrationRow.noRelease instruction=true) :
    (locatedBlock origin code).toList.all PDROC.CalibrationRow.noRelease=true := by
  apply List.all_eq_true.mpr
  intro instruction member
  rw [locatedBlock,Array.toList_append,Array.toList_replicate] at member
  rcases List.mem_append.mp member with padding|actual
  · have equal : instruction=Instruction.halt := (List.mem_replicate.mp padding).2
    subst instruction
    rfl
  · exact safe instruction actual

theorem kernelLocated_step_live_mono (origin : ℕ) (input : List Cell) (before after : State)
    (actual : step (locatedBlock origin (kernel origin)) input before=some after) : before.live⊆after.live := by
  have predicates : (fun instruction : Instruction => match instruction with
      | .release _ => false | _ => true)=PDROC.CalibrationRow.noRelease := by
    funext instruction
    cases instruction <;> rfl
  have all := located_nonreleasing origin (kernel origin) (kernel_nonreleasing origin)
  rw [←predicates] at all
  exact step_live_mono_of_all (locatedBlock origin (kernel origin)) input before after all actual

/-- Real full-callee record space for arbitrary old live caller memory.
The complete actual trace is bounded by its genuine returned footprint,
then by the caller's old record count plus the real write/output region.
No whole-world freshness or pre-supplied final resource bound is assumed. -/
theorem callee_with_records (P : Parameters) (origin base endpoints returnPC : ℕ) (input : List Cell) (before : State)
    (arguments : CallArguments P base endpoints returnPC before)
    (endpointHeap : HeapList before endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (separate : ∀ offset<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+offset∉workspace base P.certificate.M)
    (position : before.pc=labelAddress origin .enter) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun a b => step (locatedBlock origin (kernel origin)) input a=some b) ∧
      time (locatedBlock origin (kernel origin)) trace≤30000*(P.certificate.Q+1)*(P.certificate.M+1)^2 ∧
      Return P base returnPC before after ∧
      peakCells trace≤workingCells before+workspaceSize P.certificate.M+rowWidth P.certificate.M := by
  obtain ⟨after,actual,returned⟩ := callee P origin base endpoints returnPC input before arguments endpointHeap separate position
  obtain ⟨trace,head,last,chain,cost⟩ := actual
  have contract := returned
  obtain ⟨_pc,_fresh,_old,_address,_index,_cache,output,frame⟩ := returned
  have peak := chain_peakCells_le_final (locatedBlock origin (kernel origin)) input
    (kernelLocated_step_live_mono origin input) trace after chain last
  have finalBound := frame.workingCells_le
    (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList) output
  rw [encodeCalibrationCache_length] at finalBound
  exact ⟨trace,after,head,last,chain,cost,contract,peak.trans finalBound⟩

end PDLower.CalibrationCompute
