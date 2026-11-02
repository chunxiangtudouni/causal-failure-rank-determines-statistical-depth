module

public import Paid.PDLower_CalibrationCompute_Standalone_081
public import Paid.PDLower_CalibrationCompute_CalleeResources_119
public import Paid.PDLower_CalibrationCompute_LoaderBits_128

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

def calibrationProgramBitConstant : ℕ := 4096+16*natBits (mainStart+27)

/-- Abstract the fixed program PC before arithmetic normalization, so
the proof never unfolds the original large literal kernel. -/
theorem standalone_budget_scale_arithmetic (scale term programPC : ℕ)
    (positive : 1≤scale) (bounded : term≤scale) :
    16*(4+16*scale+programPC+64)+1024*term+1+64≤(4096+16*programPC)*scale := by
  have fixed := Nat.mul_le_mul_left (16*programPC+1153) positive
  have scaled := Nat.mul_le_mul_left 1024 bounded
  have main : 16*(4+16*scale+programPC+64)+1024*term+1+64≤
      1280*scale+(16*programPC+1153)*scale := by omega
  calc
    _ ≤ 1280*scale+(16*programPC+1153)*scale := main
    _ = (2433+16*programPC)*scale := by ring
    _ ≤ (4096+16*programPC)*scale := Nat.mul_le_mul_right scale (by omega)

theorem standalone_callee_budget (P : Parameters) (fee : ℚ) :
    calleeOperandBudget P 1 (standaloneLoaderBudget P fee 4) (ratEncodingBits P.certificate.gamma)≤
      calibrationProgramBitConstant*calibrationBitScale P fee := by
  have qScale := calibrationBitScale_Q P fee
  have positive : 1≤calibrationBitScale P fee := by omega
  have tBound : (P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)≤calibrationBitScale P fee := by
    unfold calibrationBitScale
    omega
  have smallPC : natBits 1=1 := by decide
  have actual := standalone_budget_scale_arithmetic (calibrationBitScale P fee)
    ((P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)) (natBits (mainStart+27)) positive tBound
  simpa only [calleeOperandBudget,standaloneLoaderBudget,calibrationProgramBitConstant,Nat.mul_assoc,smallPC] using actual

theorem StandaloneBitSegment.budget_mono {input : List Cell} {before after : State} {timeBudget first later : ℕ}
    (actual : StandaloneBitSegment input before after timeBudget first) (bounded : first≤later) :
    StandaloneBitSegment input before after timeBudget later := by
  obtain ⟨trace,head,last,chain,cost,states⟩ := actual
  exact ⟨trace,head,last,chain,cost,fun state member bits occurrence => (states state member bits occurrence).trans bounded⟩

/-- The actual original fixed calibrate program, original readonly
calibrationInput, all loader prefixes and all M+1 full Q-row outer levels.
One genuine initial-to-HALT run simultaneously carries original output,
time, record space and original-parameter operand-bit bounds. Constants
depend only on the fixed program; no P/fee-specific program is supplied. -/
theorem standalone_resources (P : Parameters) (fee : ℚ) :
    ∃ (trace : List State) (final : State),Runs calibrate (calibrationInput P) trace final ∧
      final.output=encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList ∧
      time calibrate trace≤64000*P.certificate.Q*(P.certificate.M+1)^2 ∧
      peakCells trace≤38*(P.certificate.M+1) ∧
      peakOperandBits trace≤calibrationProgramBitConstant*calibrationBitScale P fee := by
  let incoming := standaloneLoaderBudget P fee 4
  let budget := calleeOperandBudget P 1 incoming (ratEncodingBits P.certificate.gamma)
  obtain ⟨entered,loader,entryPC,entry,loaderOutput,loaderLive⟩ :=
    bootstrapLoader_bits P fee 4 initial rfl rfl calibration_initial_safe
  obtain ⟨fresh,old,address,total,index,value,endpointHeap,disjoint⟩ := entry
  have arguments : CallArguments P (rowWidth P.certificate.M) 0 (mainStart+27) entered :=
    ⟨fresh,old,address,total,index,value⟩
  have separate (offset : ℕ) (inside : offset<(encodeList encodeEndpoint P.endpointCache.toList).length) :
      0+offset∉workspace (rowWidth P.certificate.M) P.certificate.M := by
    intro inWorkspace
    exact Finset.disjoint_left.mp disjoint (endpointHeap.1 offset inside) inWorkspace
  have position : entered.pc=labelAddress 1 .enter := by change entered.pc=1;exact entryPC
  obtain ⟨final,callee,returned⟩ := callee_bits P 1 (rowWidth P.certificate.M) 0 (mainStart+27) incoming
    (ratEncodingBits P.certificate.gamma) (calibrationInput P) entered arguments loader.final (le_refl _) endpointHeap separate position
  have growth (initial intrinsic counter : ℕ) : initial≤16*initial+1024*intrinsic+counter+64 := by omega
  have loaderBudget : incoming≤budget := by
    simpa only [budget,calleeOperandBudget,Nat.mul_assoc] using
      growth incoming ((P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)) (natBits 1)
  have embedded : StandaloneBitSegment (calibrationInput P) entered final
      (30000*(P.certificate.Q+1)*(P.certificate.M+1)^2+15) budget := callee.inStandalone
  have complete := (loader.budget_mono loaderBudget).trans embedded
  obtain ⟨trace,head,last,chain,cost,states⟩ := complete
  obtain ⟨pc,_fresh,_old,_address,_index,_cache,output,frame⟩ := returned
  have halted : calibrate[final.pc]?=some .halt := by rw [pc];exact calibrate_halt_fetch
  have records : workingCells entered≤registers.length+rowWidth P.certificate.M := by
    simp only [workingCells,loaderLive,Finset.card_range,loaderOutput,initial,List.length_nil]
    omega
  have peak := calibrate_standalone_record_bound (calibrationInput P) trace entered final
    (rowWidth P.certificate.M) P.certificate.M (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList)
    chain last frame output records (Nat.le_of_eq (encodeCalibrationCache_length P))
  have operands := PDROC.D27Prepare.Resources.peakOperandBits_le_of_states trace budget states
  have timeBound := cost.trans (standalone_cost_bound P.certificate.Q P.certificate.M)
  have positive := original_Q_positive P
  have factor : P.certificate.Q+1≤2*P.certificate.Q := by omega
  have originalTime : 32000*(P.certificate.Q+1)*(P.certificate.M+1)^2≤64000*P.certificate.Q*(P.certificate.M+1)^2 := by
    calc
      _ ≤ 32000*(2*P.certificate.Q)*(P.certificate.M+1)^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 32000 factor)
      _ = _ := by ring
  exact ⟨trace,final,runs_of_actual_chain calibrate (calibrationInput P) trace final head chain last halted,
    by simpa only [loaderOutput,initial,List.nil_append] using output,timeBound.trans originalTime,peak,
    operands.trans (standalone_callee_budget P fee)⟩

/-- The calibration conjunct in the original uniform specification,
with fixed program and positive constants chosen BEFORE every P/fee. -/
theorem original_calibration_resources :
    ∃ (program : Program) (Ctime Cspace Cbits : ℕ),0<Ctime ∧ 0<Cspace ∧ 0<Cbits ∧
      ∀ (P : Parameters) (fee : ℚ),∃ (trace : List State) (final : State),
        Runs program (calibrationInput P) trace final ∧
        final.output=encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList ∧
        time program trace≤Ctime*P.certificate.Q*(P.certificate.M+1)^2 ∧
        peakCells trace≤Cspace*(P.certificate.M+1) ∧
        peakOperandBits trace≤Cbits*((P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)+maximumMenuBits P fee+1) := by
  refine ⟨calibrate,64000,38,calibrationProgramBitConstant,by decide,by decide,?_,?_⟩
  · unfold calibrationProgramBitConstant
    exact (by decide : 0<(4096 : ℕ)).trans_le (Nat.le_add_right _ _)
  · intro P fee
    exact standalone_resources P fee

end PDLower.CalibrationCompute
