module
public import PaperProofs.Common.PSTR_TM_DoubleTrace_062
public import PaperProofs.Common.PSTR_TM_Length_004

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeDouble063
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMNatValue017 PSTRTMDoubleCode061

def blocksDoubleMachine : Machine 30 := PSTRTMSeq005.seqMachine PSTRTMRawNat010.rawNatMachine doubleMachine
def nativeDoubleMachine : Machine 50 := PSTRTMSeq005.seqMachine blocksDoubleMachine PSTRTMUnblock018.unblockMachine

def blocksTrace (value : Nat) : List (MachineState 30) :=
  (PSTRTMRawNat010.rawTrace [] (rawPayload value) []).map (PSTRTMSeq005.leftCfg (b := 13)) ++
    (PSTRTMDoubleTrace062.doubleTrace (rawPayload value)).map (PSTRTMSeq005.rightCfg (a := 16))

def blocksFinal (value : Nat) : MachineState 30 := PSTRTMSeq005.rightCfg (a := 16)
  (PSTRTMDoubleCode061.state 10 [] (PSTRTMIncrement009.blocks (doubleDigits (rawPayload value))))

def nativeTrace (value : Nat) : List (MachineState 50) :=
  (blocksTrace value).map (PSTRTMSeq005.leftCfg (b := 19)) ++
    (PSTRTMUnblockTrace019.unblockTrace (doubleDigits (rawPayload value))).map (PSTRTMSeq005.rightCfg (a := 30))

def nativeFinal (value : Nat) : MachineState 50 := PSTRTMSeq005.rightCfg (a := 30)
  (PSTRTMUnblock018.state 19 [false] (PSTRTMUnblockTrace019.rawWord (doubleDigits (rawPayload value))))

private theorem payload_length (value : Nat) : (rawPayload value).length = natBits value := by
  simp only [rawPayload, List.length_ofFn]

theorem blocks_runs (value : Nat) :
    Runs blocksDoubleMachine (encodeNat value) (blocksTrace value) (blocksFinal value) := by
  apply PSTRTMSeq005.seq_runs PSTRTMRawNat010.rawNatMachine doubleMachine (encodeNat value)
    (PSTRTMRawNat010.state 16 [false] (PSTRTMIncrement009.blocks (rawPayload value) ++ [false]))
    (PSTRTMDoubleCode061.state 10 [] (PSTRTMIncrement009.blocks (doubleDigits (rawPayload value))))
    (PSTRTMRawNat010.rawTrace [] (rawPayload value) []) (PSTRTMDoubleTrace062.doubleTrace (rawPayload value))
  · simpa only [List.append_nil, rawPayload, List.length_ofFn, encodeNat, List.append_assoc, List.singleton_append] using
      PSTRTMRawNat010.raw_runs (rawPayload value) []
  · have hr := PSTRTMDoubleTrace062.double_runs (rawPayload value) (rawPayload_ne_nil value)
    rw [PSTRTMRawNat010.isolated_final_tape]
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

theorem blocks_final_tape (value : Nat) :
    (blocksFinal value).Tape = Turing.Tape.mk₁ (PSTRTMIncrement009.blocks (doubleDigits (rawPayload value))) := rfl

theorem native_runs (value : Nat) :
    Runs nativeDoubleMachine (encodeNat value) (nativeTrace value) (nativeFinal value) := by
  apply PSTRTMSeq005.seq_runs blocksDoubleMachine PSTRTMUnblock018.unblockMachine (encodeNat value)
    (blocksFinal value)
    (PSTRTMUnblock018.state 19 [false] (PSTRTMUnblockTrace019.rawWord (doubleDigits (rawPayload value))))
    (blocksTrace value) (PSTRTMUnblockTrace019.unblockTrace (doubleDigits (rawPayload value))) (blocks_runs value)
  have hr := PSTRTMUnblockTrace019.unblock_runs (doubleDigits (rawPayload value))
  rw [blocks_final_tape]
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

theorem rawWord_double (value : Nat) :
    PSTRTMUnblockTrace019.rawWord (doubleDigits (rawPayload value)) = encodeNat (2 * value) := by
  rw [doubleDigits_rawPayload]
  simp [PSTRTMUnblockTrace019.rawWord, rawPayload, encodeNat]

theorem native_final_tape_canonical (value : Nat) :
    (nativeFinal value).Tape = Turing.Tape.mk₁ (encodeNat (2 * value)) := by
  have ht : (nativeFinal value).Tape = Turing.Tape.mk₁
      (PSTRTMUnblockTrace019.rawWord (doubleDigits (rawPayload value))) := by
    simp only [nativeFinal, PSTRTMSeq005.rightCfg, PSTRTMUnblock018.state, Turing.Tape.mk₁, Turing.Tape.mk₂]
    rw [PSTRTMRawNat010.blank_single_false]
  rw [ht, rawWord_double]

theorem native_length_le (value : Nat) : (nativeTrace value).length ≤ 128 * (natBits value + 1)^2 := by
  have hd := PSTRTMDoubleTrace062.double_length_le (rawPayload value)
  have hl := doubleDigits_length_le (rawPayload value)
  simp only [payload_length] at hl
  have hsq := Nat.pow_le_pow_left hl 2
  simp only [nativeTrace, blocksTrace, List.length_append, List.length_map,
    PSTRTMRawNat010.raw_length, PSTRTMUnblockTrace019.unblock_length, List.length_nil, payload_length]
  nlinarith

theorem native_visitedSpace_le (value : Nat) :
    visitedSpace nativeDoubleMachine (encodeNat value).length (nativeTrace value) ≤ 512 * (natBits value + 1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le nativeDoubleMachine (encodeNat value).length (nativeTrace value)
  have ht := native_length_le value
  simp only [PSTRTMLength004.encodeNat_length] at hs ⊢
  nlinarith

/-- One fixed51-label program, canonical original input/output including0.
All actual parsing, guard, allocation, inverse codec and rewind costs count. -/
theorem encodeNat_double_computes (value : Nat) :
    computes nativeDoubleMachine (encodeNat value) (encodeNat (2 * value))
      (128 * (natBits value + 1)^2) (512 * (natBits value + 1)^2) := by
  refine ⟨nativeTrace value, nativeFinal value, native_runs value, ?_, native_length_le value, native_visitedSpace_le value⟩
  rw [native_final_tape_canonical]
  simp [Turing.Tape.mk₁, Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeDouble063
