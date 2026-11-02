module

public import Paid.PDLower_CalibrationCompute_BootstrapLoader_069
public import Paid.PDLower_CalibrationCompute_Callee_080
public import Paid.PDLower_CalibrationCompute_CallerEmbedding_073
public import Paid.PDLower_CalibrationCompute_CalibrateSpace_066
public import Paid.PDLower_CalibrationCompute_CalleeRecords_083

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem standalone_cost_bound (Q M : ℕ) :
    1000*(M+1)+(30000*(Q+1)*(M+1)^2+15)≤32000*(Q+1)*(M+1)^2 := by
  have square : M+1≤(M+1)^2 := by nlinarith
  have product : (M+1)^2≤(Q+1)*(M+1)^2 := by
    simpa only [one_mul] using Nat.mul_le_mul_right ((M+1)^2) (by omega : 1≤Q+1)
  have lower := square.trans product
  have first := Nat.mul_le_mul_left 1000 lower
  have reserve : 15≤1000*((Q+1)*(M+1)^2) := by omega
  calc
    _ = 30000*((Q+1)*(M+1)^2)+(1000*(M+1)+15) := by ring
    _ ≤ 30000*((Q+1)*(M+1)^2)+(1000*((Q+1)*(M+1)^2)+1000*((Q+1)*(M+1)^2)) :=
      Nat.add_le_add_left (Nat.add_le_add first reserve) _
    _ = _ := by ring

theorem runs_of_actual_chain (program : Program) (input : List Cell) (trace : List State) (final : State)
    (head : trace.head?=some initial)
    (chain : trace.IsChain (fun first later => step program input first=some later))
    (last : trace.getLast?=some final) (halt : program[final.pc]?=some .halt) : Runs program input trace final := by
  refine ⟨head,chain,last,halt,StateTransition.mem_eval.mpr ⟨?_,?_⟩⟩
  · have nonempty : trace≠[] := by intro empty; rw [empty] at head; cases head
    have reached := List.relationReflTransGen_of_exists_isChain trace chain nonempty
    have first : trace.head nonempty=initial := by
      have actual := List.head?_eq_some_head nonempty
      rw [head] at actual
      exact (Option.some.inj actual).symm
    have finalState : trace.getLast nonempty=final := by
      have actual := List.getLast?_eq_getLast_of_ne_nil nonempty
      rw [last] at actual
      exact (Option.some.inj actual).symm
    simpa only [StateTransition.Reaches,first,finalState,Option.mem_def] using reached
  · simp [step,halt,Instruction.execute]

/-- Original fixed standalone program, actual input loads and complete
callee, true fetched HALT, original output, actual primitive time and
ALL-prefix record space. Operand bits remain a distinct obligation. -/
theorem standalone (P : Parameters) :
    ∃ (trace : List State) (final : State),Runs calibrate (calibrationInput P) trace final ∧
      final.output=encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList ∧
      time calibrate trace≤32000*(P.certificate.Q+1)*(P.certificate.M+1)^2 ∧
      peakCells trace≤38*(P.certificate.M+1) := by
  obtain ⟨entered,loader,entryPC,entry,loaderOutput,loaderLive⟩ := bootstrapLoader P initial rfl rfl
  have position : entered.pc=labelAddress 1 .enter := by change entered.pc=1; exact entryPC
  obtain ⟨final,run,returned⟩ := callee_of_entry P 1 (rowWidth P.certificate.M) 0 (mainStart+27)
    (calibrationInput P) entered entry position
  have complete := loader.trans (run.inStandalone (rightInput:=calibrationInput P))
  obtain ⟨trace,head,last,chain,cost⟩ := complete
  obtain ⟨pc,_fresh,_old,_address,_index,_cache,output,frame⟩ := returned
  have halted : calibrate[final.pc]?=some .halt := by rw [pc]; exact calibrate_halt_fetch
  have records : workingCells entered≤registers.length+rowWidth P.certificate.M := by
    simp only [workingCells,loaderLive,Finset.card_range,loaderOutput,initial,List.length_nil]
    omega
  have peak := calibrate_standalone_record_bound (calibrationInput P) trace entered final
    (rowWidth P.certificate.M) P.certificate.M
    (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList)
    chain last frame output records (Nat.le_of_eq (encodeCalibrationCache_length P))
  refine ⟨trace,final,runs_of_actual_chain calibrate (calibrationInput P) trace final head chain last halted,?_,?_,peak⟩
  · simpa only [loaderOutput,initial,List.nil_append] using output
  · exact cost.trans (standalone_cost_bound P.certificate.Q P.certificate.M)

/-- Match the ORIGINAL target's Q factor, using positivity derived from
the original public certificate ceil; no Q-positive premise is added. -/
theorem standalone_original_time (P : Parameters) :
    ∃ (trace : List State) (final : State),Runs calibrate (calibrationInput P) trace final ∧
      final.output=encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList ∧
      time calibrate trace≤64000*P.certificate.Q*(P.certificate.M+1)^2 ∧
      peakCells trace≤38*(P.certificate.M+1) := by
  obtain ⟨trace,final,actual,output,time,records⟩ := standalone P
  have positive := original_Q_positive P
  have factor : P.certificate.Q+1≤2*P.certificate.Q := by
    simpa only [two_mul] using Nat.add_le_add_left (Nat.succ_le_of_lt positive) P.certificate.Q
  have scaled := Nat.mul_le_mul_right ((P.certificate.M+1)^2) (Nat.mul_le_mul_left 32000 factor)
  have bound : 32000*(P.certificate.Q+1)*(P.certificate.M+1)^2≤64000*P.certificate.Q*(P.certificate.M+1)^2 := by
    calc
      _ ≤ 32000*(2*P.certificate.Q)*(P.certificate.M+1)^2 := scaled
      _ = _ := by ring
  exact ⟨trace,final,actual,output,time.trans bound,records⟩

end PDLower.CalibrationCompute
