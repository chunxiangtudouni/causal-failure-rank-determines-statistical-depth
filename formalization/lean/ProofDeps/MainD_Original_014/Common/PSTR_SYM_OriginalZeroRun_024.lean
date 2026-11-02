module

public import Common.PSTR_SYM_ZeroEmit_023

/-! ONE fixed finite Bool code before every input, in the original local
stageCount=0 case. The original input is really parsed and cleared, its own
q+2 count is retained and contracted, and the exact original Expr/tree Bool
output is really written. An actual all-input N0/positive branch is separate;
this local case does not establish SymbolicCompilationClaims or RawP. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicZeroTail

open PaperProofs.Common Turing PSTRTMSeq005
open PSTRSymbolicLocator (naturalPrefix outerLeft zeroPrefix zeroSuffix)

abbrev bodyCap : Nat := 23 + emitCap + 1

def bodyMachine : Machine bodyCap := seqMachine cursorTailMachine emitMachine

def bodyTrace (count dataBits : Nat) (bit : Bool) (earlier : List Bool) : List (MachineState bodyCap) :=
  (cursorTailTrace (dataBits + 1) (bit :: PSTRTMRawNat010.leftBlocks earlier)).map (leftCfg (b := emitCap)) ++
    (emitTrace count).map (rightCfg (a := 23))

def bodyFinal (count : Nat) : MachineState bodyCap := rightCfg (a := 23) (emitFinal count)

theorem body_runsFrom (count dataBits : Nat) (bit : Bool) (earlier : List Bool)
    (shape : (PSTRTMNatValue017.rawPayload count).reverse = bit :: earlier) :
    RunsFrom bodyMachine
      ⟨0, Tape.mk₂ (List.replicate dataBits false ++ outerLeft [] count) [true]⟩
      (bodyTrace count dataBits bit earlier) (bodyFinal count) := by
  apply seq_runsFrom cursorTailMachine emitMachine
    ⟨0, Tape.mk₂ (List.replicate dataBits false ++ outerLeft [] count) [true]⟩
    (cursorTailFinal (bit :: PSTRTMRawNat010.leftBlocks earlier)) (emitFinal count)
    (cursorTailTrace (dataBits + 1) (bit :: PSTRTMRawNat010.leftBlocks earlier)) (emitTrace count)
  · rw [cursor_input_layout count dataBits bit earlier shape]
    exact cursorTail_runsFrom (dataBits + 1) (bit :: PSTRTMRawNat010.leftBlocks earlier)
  · rw [cursorTail_final_tape, cursor_output_layout count bit earlier shape]
    exact emit_runsFrom count

theorem body_final_tape (count : Nat) :
    (bodyFinal count).Tape = Tape.mk₂ [] (zeroPrefix ++ encodeNat count ++ zeroSuffix) :=
  emit_final_tape count

theorem body_time_le (count dataBits : Nat) (bit : Bool) (earlier : List Bool) :
    (bodyTrace count dataBits bit earlier).length ≤ dataBits + 25 + 128 * (natBits count + 1)^2 := by
  have cursor := cursorTail_length (dataBits + 1) (bit :: PSTRTMRawNat010.leftBlocks earlier)
  have emitter := emit_time_le count
  simp only [bodyTrace, List.length_append, List.length_map]
  omega

/-- This is a constant program, not a machine selected by N, q, a price,
an Expr or the proof of the local case. All data are on original Bool input. -/
def zeroSymbolicMachine : Machine (46 + bodyCap + 1) :=
  seqMachine PSTRSymbolicHeaderErase.headerEraseMachine bodyMachine

theorem zeroSymbolicMachine_labels : (46 + bodyCap + 1) + 1 = 174 := by decide

/-- Actual original output, same real trace for Runs/eval and both resource
bounds. This theorem supplies only the original N0 CASE of the full goal. -/
theorem original_zero_computes {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (zero : I.stageCount = 0) :
    computes zeroSymbolicMachine (CompactPrice.symbolicInput input available)
      (CompactPrice.symbolicOutput input available)
      (4096 * ((CompactPrice.symbolicInput input available).length + 1)^2)
      (4096 * ((CompactPrice.symbolicInput input available).length + 1)^2) := by
  obtain ⟨headerTrace, headerFinal, headerRun, headerTape, headerTime, _headerSpace⟩ :=
    PSTRSymbolicZeroErase.original_zero_erase input available zero
  let count := I.toolCount + 2
  let dataBits := (naturalPrefix (PSTRSymbolicZeroErase.zeroNumbers available)).length
  obtain ⟨bit, earlier, shape⟩ := count_reverse_cons count
  let middleTrace := bodyTrace count dataBits bit earlier
  let middleFinal := bodyFinal count
  have next : RunsFrom bodyMachine ⟨0, headerFinal.Tape⟩ middleTrace middleFinal := by
    rw [headerTape]
    exact body_runsFrom count dataBits bit earlier shape
  let trace := headerTrace.map (leftCfg (b := bodyCap)) ++ middleTrace.map (rightCfg (a := 46))
  let final := rightCfg (a := 46) middleFinal
  have actual : Runs zeroSymbolicMachine (CompactPrice.symbolicInput input available) trace final :=
    seq_runs PSTRSymbolicHeaderErase.headerEraseMachine bodyMachine
      (CompactPrice.symbolicInput input available) headerFinal middleFinal headerTrace middleTrace headerRun next
  have bits := PSTRSymbolicZeroErase.zero_input_bits input available zero
  have inputLength : (CompactPrice.symbolicInput input available).length =
      2 * natBits count + 1 + dataBits + 1 := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      PSTRTMLength004.encodeNat_length, Nat.add_assoc] using congrArg List.length bits
  have dataRoom : dataBits ≤ (CompactPrice.symbolicInput input available).length := by omega
  have widthRoom : natBits count + 1 ≤ (CompactPrice.symbolicInput input available).length + 1 := by omega
  have square := Nat.pow_le_pow_left widthRoom 2
  have widened := Nat.mul_le_mul_left 128 square
  have middleTime := body_time_le count dataBits bit earlier
  have extraRoom : (CompactPrice.symbolicInput input available).length + 25 ≤
      128 * ((CompactPrice.symbolicInput input available).length + 1)^2 := by nlinarith
  have wholeTime : trace.length ≤ 512 * ((CompactPrice.symbolicInput input available).length + 1)^2 := by
    simp only [trace, List.length_append, List.length_map]
    change headerTrace.length + (bodyTrace count dataBits bit earlier).length ≤ _
    omega
  have inputRoom : (CompactPrice.symbolicInput input available).length + 1 ≤
      ((CompactPrice.symbolicInput input available).length + 1)^2 := by nlinarith
  have cells := PSTRTMTrace002.visitedSpace_le zeroSymbolicMachine
    (CompactPrice.symbolicInput input available).length trace
  have output : CompactPrice.symbolicOutput input available = zeroPrefix ++ encodeNat count ++ zeroSuffix :=
    (PSTRSymbolicLocator.original_zero_output input available zero).trans
      (PSTRSymbolicLocator.zeroOutput_shape I.toolCount)
  have finalTape : final.Tape = Tape.mk₂ [] (CompactPrice.symbolicOutput input available) := by
    change (bodyFinal count).Tape = _
    rw [body_final_tape, output]
  refine ⟨trace, final, actual, ?_, ?_, ?_⟩
  · rw [finalTape]
    simp [Tape.mk₂]
  · omega
  · omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicZeroTail
