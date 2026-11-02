module
public import Common.PSTR_TM_CompactRun_051
public import Common.PSTR_TM_AddCanonical_052

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeAdd053
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036 PSTRTMNatValue017

def pairs (a b : Nat) : List (Bool × Bool) := digitPairs (rawPayload a) (rawPayload b)
def sumBits (a b : Nat) : List Bool := PSTRTMBinaryAdd024.sumDigits false (pairs a b)

private theorem payload_length (a : Nat) : (rawPayload a).length = natBits a := by
  simp only [rawPayload, List.length_ofFn]

def packedAddMachine : Machine 394 := PSTRTMSeq005.seqMachine PSTRTMRawPack045.rawPackMachine PSTRTMBinaryAdd024.addMachine
def blocksAddMachine : Machine 449 := PSTRTMSeq005.seqMachine packedAddMachine PSTRTMCompactCode046.compactMachine
/-- ONE fixed470-label real Bool program. Original raw two-Nat input,
actual zero extension/carry/result compaction/inverse codec, canonical output. -/
def nativeAddMachine : Machine 469 := PSTRTMSeq005.seqMachine blocksAddMachine PSTRTMUnblock018.unblockMachine

def packedTrace (a b : Nat) : List (MachineState 394) :=
  (PSTRTMRawPack045.rawPackTrace (rawPayload a) (rawPayload b)).map (PSTRTMSeq005.leftCfg (b := 49)) ++
    (PSTRTMAddRun026.addTrace false [] (pairs a b)).map (PSTRTMSeq005.rightCfg (a := 344))

def packedFinal (a b : Nat) : MachineState 394 := PSTRTMSeq005.rightCfg (a := 344)
  (PSTRTMBinaryAdd024.state 43 [false] (PSTRTMBinaryAdd024.resultColumns (sumBits a b) ++ [false]))

def blocksTrace (a b : Nat) : List (MachineState 449) :=
  (packedTrace a b).map (PSTRTMSeq005.leftCfg (b := 54)) ++
    (PSTRTMCompactRun051.compactTrace (sumBits a b)).map (PSTRTMSeq005.rightCfg (a := 394))

def blocksFinal (a b : Nat) : MachineState 449 := PSTRTMSeq005.rightCfg (a := 394)
  (PSTRTMCompactCode046.state 54 [false] (PSTRTMIncrement009.blocks (sumBits a b) ++ [false,false]))

def nativeTrace (a b : Nat) : List (MachineState 469) :=
  (blocksTrace a b).map (PSTRTMSeq005.leftCfg (b := 19)) ++
    (PSTRTMUnblockTrace019.unblockTrace (sumBits a b)).map (PSTRTMSeq005.rightCfg (a := 449))

def nativeFinal (a b : Nat) : MachineState 469 := PSTRTMSeq005.rightCfg (a := 449)
  (PSTRTMUnblock018.state 19 [false] (PSTRTMUnblockTrace019.rawWord (sumBits a b)))

theorem raw_runs (a b : Nat) :
    Runs PSTRTMRawPack045.rawPackMachine (encodeNat a ++ encodeNat b)
      (PSTRTMRawPack045.rawPackTrace (rawPayload a) (rawPayload b))
      (PSTRTMRawPack045.rawPackFinal (rawPayload a) (rawPayload b)) := by
  simpa only [PSTRTMTwoRawOperands029.rawInput, rawPayload, List.length_ofFn,
    encodeNat, List.append_assoc, List.singleton_append] using
    PSTRTMRawPack045.rawPack_runs (rawPayload a) (rawPayload b)

theorem packed_runs (a b : Nat) :
    Runs packedAddMachine (encodeNat a ++ encodeNat b) (packedTrace a b) (packedFinal a b) := by
  apply PSTRTMSeq005.seq_runs PSTRTMRawPack045.rawPackMachine PSTRTMBinaryAdd024.addMachine
    (encodeNat a ++ encodeNat b) (PSTRTMRawPack045.rawPackFinal (rawPayload a) (rawPayload b))
    (PSTRTMBinaryAdd024.state 43 [false] (PSTRTMBinaryAdd024.resultColumns (sumBits a b) ++ [false]))
    (PSTRTMRawPack045.rawPackTrace (rawPayload a) (rawPayload b)) (PSTRTMAddRun026.addTrace false [] (pairs a b))
    (raw_runs a b)
  have hr := PSTRTMAddRun026.add_runs (pairs a b)
  rw [PSTRTMRawPack045.rawPack_final_tape]
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

theorem packed_final_tape (a b : Nat) :
    (packedFinal a b).Tape = Turing.Tape.mk₁ (PSTRTMBinaryAdd024.resultColumns (sumBits a b)) := by
  simp only [packedFinal, PSTRTMSeq005.rightCfg, PSTRTMBinaryAdd024.state, Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false, PSTRTMRawNat010.blank_append_false]

theorem blocks_runs (a b : Nat) :
    Runs blocksAddMachine (encodeNat a ++ encodeNat b) (blocksTrace a b) (blocksFinal a b) := by
  apply PSTRTMSeq005.seq_runs packedAddMachine PSTRTMCompactCode046.compactMachine
    (encodeNat a ++ encodeNat b) (packedFinal a b)
    (PSTRTMCompactCode046.state 54 [false] (PSTRTMIncrement009.blocks (sumBits a b) ++ [false,false]))
    (packedTrace a b) (PSTRTMCompactRun051.compactTrace (sumBits a b)) (packed_runs a b)
  have hr := PSTRTMCompactRun051.compact_runs (sumBits a b)
  rw [packed_final_tape]
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

theorem blocks_final_tape (a b : Nat) :
    (blocksFinal a b).Tape = Turing.Tape.mk₁ (PSTRTMIncrement009.blocks (sumBits a b)) := by
  simpa only [blocksFinal, PSTRTMSeq005.rightCfg] using PSTRTMCompactRun051.compact_final_tape (sumBits a b)

theorem native_runs (a b : Nat) :
    Runs nativeAddMachine (encodeNat a ++ encodeNat b) (nativeTrace a b) (nativeFinal a b) := by
  apply PSTRTMSeq005.seq_runs blocksAddMachine PSTRTMUnblock018.unblockMachine
    (encodeNat a ++ encodeNat b) (blocksFinal a b)
    (PSTRTMUnblock018.state 19 [false] (PSTRTMUnblockTrace019.rawWord (sumBits a b)))
    (blocksTrace a b) (PSTRTMUnblockTrace019.unblockTrace (sumBits a b)) (blocks_runs a b)
  have hr := PSTRTMUnblockTrace019.unblock_runs (sumBits a b)
  rw [blocks_final_tape]
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

theorem native_final_tape (a b : Nat) :
    (nativeFinal a b).Tape = Turing.Tape.mk₁ (PSTRTMUnblockTrace019.rawWord (sumBits a b)) := by
  simp only [nativeFinal, PSTRTMSeq005.rightCfg, PSTRTMUnblock018.state, Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]

theorem native_final_tape_canonical (a b : Nat) :
    (nativeFinal a b).Tape = Turing.Tape.mk₁ (encodeNat (a + b)) := by
  rw [native_final_tape]
  have he := PSTRTMAddCanonical052.rawWord_sum_eq a b
  change PSTRTMUnblockTrace019.rawWord (sumBits a b) = encodeNat (a + b) at he
  rw [he]

theorem pairs_length_le (a b : Nat) : (pairs a b).length ≤ natBits a + natBits b := by
  simp only [pairs, digitPairs_length, rawPayload, List.length_ofFn]
  exact max_le (by omega) (by omega)

theorem sumBits_length_le (a b : Nat) : (sumBits a b).length ≤ natBits a + natBits b + 1 := by
  have hl := PSTRTMAddCanonical052.sumDigits_length_bounds false (pairs a b)
  have hp := pairs_length_le a b
  change (pairs a b).length ≤ (sumBits a b).length ∧ (sumBits a b).length ≤ (pairs a b).length + 1 at hl
  omega

theorem native_length_le (a b : Nat) :
    (nativeTrace a b).length ≤ 4096 * (natBits a + natBits b + 1)^2 := by
  have hr := PSTRTMRawPack045.rawPack_length_le (rawPayload a) (rawPayload b)
  simp only [payload_length] at hr
  have ha := PSTRTMAddRun026.add_length_le false [] (pairs a b)
  simp only [List.length_nil] at ha
  have hp := pairs_length_le a b
  have hs := sumBits_length_le a b
  have hsq := Nat.pow_le_pow_left hs 2
  simp only [nativeTrace, blocksTrace, packedTrace, List.length_append, List.length_map,
    PSTRTMCompactRun051.compact_length, PSTRTMUnblockTrace019.unblock_length]
  nlinarith

theorem native_visitedSpace_le (a b : Nat) :
    visitedSpace nativeAddMachine (encodeNat a ++ encodeNat b).length (nativeTrace a b) ≤
      16384 * (natBits a + natBits b + 1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le nativeAddMachine (encodeNat a ++ encodeNat b).length (nativeTrace a b)
  have ht := native_length_le a b
  simp only [List.length_append, PSTRTMLength004.encodeNat_length] at hs ⊢
  nlinarith

/-- Complete original raw two-Nat binary addition. No aligned columns,
padding, answer, runtime endpoint or cost fields are assumed in the input. -/
theorem encodeNat_add_computes (a b : Nat) :
    computes nativeAddMachine (encodeNat a ++ encodeNat b) (encodeNat (a + b))
      (4096 * (natBits a + natBits b + 1)^2) (16384 * (natBits a + natBits b + 1)^2) := by
  refine ⟨nativeTrace a b, nativeFinal a b, native_runs a b, ?_, native_length_le a b, native_visitedSpace_le a b⟩
  rw [native_final_tape_canonical]
  simp [Turing.Tape.mk₁, Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeAdd053
