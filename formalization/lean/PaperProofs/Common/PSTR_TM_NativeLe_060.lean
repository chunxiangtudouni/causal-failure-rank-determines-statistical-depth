module
public import PaperProofs.Common.PSTR_TM_CompareRun_059
public import PaperProofs.Common.PSTR_TM_RawPack_045

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeLe060
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036 PSTRTMNatValue017

def pairs (a b : Nat) : List (Bool × Bool) := digitPairs (rawPayload a) (rawPayload b)

/-- ONE fixed398-label Bool program. It parses/aligns the ORIGINAL two raw
Nat fields, reads their actual bits, erases the real operands and writes the
canonical original Nat encoding of the computed comparison truth value. -/
def nativeLeMachine : Machine 397 :=
  PSTRTMSeq005.seqMachine PSTRTMRawPack045.rawPackMachine PSTRTMCompareFinishCode057.resultMachine

def nativeTrace (a b : Nat) : List (MachineState 397) :=
  (PSTRTMRawPack045.rawPackTrace (rawPayload a) (rawPayload b)).map (PSTRTMSeq005.leftCfg (b := 52)) ++
    (PSTRTMCompareRun059.resultTrace (pairs a b)).map (PSTRTMSeq005.rightCfg (a := 344))

def nativeFinal (a b : Nat) : MachineState 397 :=
  PSTRTMSeq005.rightCfg (a := 344) (PSTRTMCompareRun059.resultFinal (pairs a b))

private theorem payload_length (a : Nat) : (rawPayload a).length = natBits a := by
  simp only [rawPayload, List.length_ofFn]

theorem encodeNat_bool (bit : Bool) : encodeNat (if bit then 1 else 0) = [true,false,bit] := by
  cases bit <;> rfl

theorem native_runs (a b : Nat) :
    Runs nativeLeMachine (encodeNat a ++ encodeNat b) (nativeTrace a b) (nativeFinal a b) := by
  apply PSTRTMSeq005.seq_runs PSTRTMRawPack045.rawPackMachine PSTRTMCompareFinishCode057.resultMachine
    (encodeNat a ++ encodeNat b) (PSTRTMRawPack045.rawPackFinal (rawPayload a) (rawPayload b))
    (PSTRTMCompareRun059.resultFinal (pairs a b))
    (PSTRTMRawPack045.rawPackTrace (rawPayload a) (rawPayload b)) (PSTRTMCompareRun059.resultTrace (pairs a b))
  · simpa only [PSTRTMTwoRawOperands029.rawInput, rawPayload, List.length_ofFn,
      encodeNat, List.append_assoc, List.singleton_append] using
      PSTRTMRawPack045.rawPack_runs (rawPayload a) (rawPayload b)
  · have hr := PSTRTMCompareRun059.result_runs (pairs a b)
    rw [PSTRTMRawPack045.rawPack_final_tape]
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

theorem outputWord_original (a b : Nat) :
    PSTRTMCompareFinishCode057.outputWord (PSTRTMCompareCode054.resultRelation 0 (pairs a b)) =
      encodeNat (if decide (a ≤ b) then 1 else 0) := by
  simp only [PSTRTMCompareFinishCode057.outputWord, pairs, PSTRTMCompareValue056.original_resultLe,
    encodeNat_bool]

theorem native_final_tape_canonical (a b : Nat) :
    (nativeFinal a b).Tape = Turing.Tape.mk₁ (encodeNat (if decide (a ≤ b) then 1 else 0)) := by
  change (PSTRTMCompareRun059.resultFinal (pairs a b)).Tape = _
  rw [PSTRTMCompareRun059.result_final_tape, outputWord_original]

theorem pairs_length_le (a b : Nat) : (pairs a b).length ≤ natBits a + natBits b := by
  simp only [pairs, digitPairs_length, payload_length]
  exact max_le (by omega) (by omega)

theorem native_length_le (a b : Nat) :
    (nativeTrace a b).length ≤ 4096 * (natBits a + natBits b + 1)^2 := by
  have hr := PSTRTMRawPack045.rawPack_length_le (rawPayload a) (rawPayload b)
  simp only [payload_length] at hr
  have hp := pairs_length_le a b
  simp only [nativeTrace, List.length_append, List.length_map, PSTRTMCompareRun059.result_length]
  nlinarith

theorem native_visitedSpace_le (a b : Nat) :
    visitedSpace nativeLeMachine (encodeNat a ++ encodeNat b).length (nativeTrace a b) ≤
      16384 * (natBits a + natBits b + 1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le nativeLeMachine (encodeNat a ++ encodeNat b).length (nativeTrace a b)
  have ht := native_length_le a b
  simp only [List.length_append, PSTRTMLength004.encodeNat_length] at hs ⊢
  nlinarith

/-- Complete original raw two-Nat non-strict comparison. The answer, width,
alignment, padding, endpoint and cost are NOT additional input fields. -/
theorem encodeNat_le_computes (a b : Nat) :
    computes nativeLeMachine (encodeNat a ++ encodeNat b)
      (encodeNat (if decide (a ≤ b) then 1 else 0))
      (4096 * (natBits a + natBits b + 1)^2) (16384 * (natBits a + natBits b + 1)^2) := by
  refine ⟨nativeTrace a b, nativeFinal a b, native_runs a b, ?_, native_length_le a b, native_visitedSpace_le a b⟩
  rw [native_final_tape_canonical]
  simp [Turing.Tape.mk₁, Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeLe060
