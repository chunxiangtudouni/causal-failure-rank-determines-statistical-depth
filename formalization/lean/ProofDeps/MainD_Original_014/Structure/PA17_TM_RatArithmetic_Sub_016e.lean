module
public import Structure.PA17_TM_RatArithmetic_Sub_016d

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016

def decodedTrace (pairs : List Pair) : List (MachineState 251) :=
  (branchTrace pairs).map (PSTRTMSeq005.leftCfg (b := 103)) ++
    (PA17TMDivisionCodec003.isolatedOutputTrace (saturatedPairs pairs)).map (PSTRTMSeq005.rightCfg (a := 147))

def decodedFinal (pairs : List Pair) : MachineState 251 :=
  PSTRTMSeq005.rightCfg (a := 147) (PA17TMDivisionCodec003.isolatedOutputFinal (saturatedPairs pairs))

theorem branch_runs (pairs : List Pair) :
    Runs branchMachine (PSTRTMBinaryAdd024.operandColumns pairs) (branchTrace pairs) (branchFinal pairs) := by
  have hr := branch_runsFrom pairs
  rw [branch_initial_tape] at hr
  apply PSTRTMTrace002.runs_of_chain
  · simpa only [Turing.TM0.init,Fin.default_eq_zero] using hr.1
  · exact hr.2.1
  · exact hr.2.2.1
  · exact hr.2.2.2

theorem decoded_runs (pairs : List Pair) :
    Runs decodedMachine (PSTRTMBinaryAdd024.operandColumns pairs) (decodedTrace pairs) (decodedFinal pairs) := by
  apply PSTRTMSeq005.seq_runs branchMachine PA17TMDivisionCodec003.isolatedOutputMachine
    (PSTRTMBinaryAdd024.operandColumns pairs) (branchFinal pairs)
    (PA17TMDivisionCodec003.isolatedOutputFinal (saturatedPairs pairs))
    (branchTrace pairs) (PA17TMDivisionCodec003.isolatedOutputTrace (saturatedPairs pairs)) (branch_runs pairs)
  rw [branch_final_tape]
  exact PA17TMDivisionCodec003.isolatedOutput_runsFrom (saturatedPairs pairs)

theorem decoded_final_tape (pairs : List Pair) :
    (decodedFinal pairs).Tape = Turing.Tape.mk₁
      (encodeNat (PSTRTMBinaryAdd024.firstValue pairs-PSTRTMBinaryAdd024.secondValue pairs)) := by
  change (PA17TMDivisionCodec003.isolatedOutputFinal (saturatedPairs pairs)).Tape = _
  rw [PA17TMDivisionCodec003.isolatedOutput_final_tape,saturated_value]

def pairs (a b : Nat) : List Pair := PSTRTMNativeAdd053.pairs a b

def nativeTrace (a b : Nat) : List (MachineState 596) :=
  (PSTRTMRawPack045.rawPackTrace (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)).map
    (PSTRTMSeq005.leftCfg (b := 251)) ++
  (decodedTrace (pairs a b)).map (PSTRTMSeq005.rightCfg (a := 344))

def nativeFinal (a b : Nat) : MachineState 596 :=
  PSTRTMSeq005.rightCfg (a := 344) (decodedFinal (pairs a b))

theorem pairs_values (a b : Nat) :
    PSTRTMBinaryAdd024.firstValue (pairs a b) = a ∧ PSTRTMBinaryAdd024.secondValue (pairs a b) = b := by
  have hv := PSTRTMAddCanonical052.digitPairs_values (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)
  rw [PSTRTMNatValue017.valueDigits_rawPayload,PSTRTMNatValue017.valueDigits_rawPayload] at hv
  exact hv

theorem pairs_length_le (a b : Nat) : (pairs a b).length ≤ natBits a+natBits b :=
  PSTRTMNativeAdd053.pairs_length_le a b

/-- Entire original raw double-Nat input, including a<b and either zero.
The raw aligner and every borrow branch/zero write/codec step are real code. -/
theorem native_runs (a b : Nat) :
    Runs nativeSubMachine (encodeNat a++encodeNat b) (nativeTrace a b) (nativeFinal a b) := by
  apply PSTRTMSeq005.seq_runs PSTRTMRawPack045.rawPackMachine decodedMachine (encodeNat a++encodeNat b)
    (PSTRTMRawPack045.rawPackFinal (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b))
    (decodedFinal (pairs a b))
    (PSTRTMRawPack045.rawPackTrace (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b))
    (decodedTrace (pairs a b)) (PSTRTMNativeAdd053.raw_runs a b)
  rw [PSTRTMRawPack045.rawPack_final_tape]
  have hr := decoded_runs (pairs a b)
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem native_final_tape (a b : Nat) :
    (nativeFinal a b).Tape = Turing.Tape.mk₁ (encodeNat (a-b)) := by
  change (decodedFinal (pairs a b)).Tape = _
  rw [decoded_final_tape,(pairs_values a b).1,(pairs_values a b).2]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016
