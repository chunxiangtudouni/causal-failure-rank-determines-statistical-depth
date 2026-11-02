module
public import Common.PSTR_TM_PackRun_044
public import Common.PSTR_TM_OperandStart_033
public import Common.PSTR_TM_NatValue_017

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMRawPack045
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036 PSTRTMPackLoop043 PSTRTMPackRun044 PSTRTMOperandStart033

/-- The original raw double-field front end and actual isolated aligner
share the SAME whole tape, with one real head-preserving transfer step. -/
def rawPackMachine : Machine 344 := PSTRTMSeq005.seqMachine operandStartMachine packMachine

def rawPackTrace (first second : List Bool) : List (MachineState 344) :=
  (operandStartTrace first second []).map (PSTRTMSeq005.leftCfg (b := 193)) ++
    (packTrace [] first second).map (PSTRTMSeq005.rightCfg (a := 150))

def rawPackFinal (first second : List Bool) : MachineState 344 :=
  PSTRTMSeq005.rightCfg (a := 150) (PSTRTMPackRun044.final [] first second)

theorem rawPack_runs (first second : List Bool) :
    Runs rawPackMachine (PSTRTMTwoRawOperands029.rawInput first ++ PSTRTMTwoRawOperands029.rawInput second)
      (rawPackTrace first second) (rawPackFinal first second) := by
  apply PSTRTMSeq005.seq_runs operandStartMachine packMachine
    (PSTRTMTwoRawOperands029.rawInput first ++ PSTRTMTwoRawOperands029.rawInput second)
    (operandStartFinal first second []) (PSTRTMPackRun044.final [] first second)
    (operandStartTrace first second []) (packTrace [] first second)
  · simpa only [List.append_nil] using operandStart_runs first second []
  · have hr := pack_runs first second
    rw [isolated_final_tape]
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

theorem rawPack_final_tape (first second : List Bool) :
    (rawPackFinal first second).Tape = Turing.Tape.mk₁ (PSTRTMBinaryAdd024.operandColumns (digitPairs first second)) :=
  pack_final_tape first second

theorem rawPack_length_le (first second : List Bool) :
    (rawPackTrace first second).length ≤ 2048 * (first.length + second.length + 1)^2 := by
  have hp := pack_length_le [] first second
  simp only [List.length_nil] at hp
  simp only [rawPackTrace, List.length_append, List.length_map, operandStart_length]
  nlinarith [Nat.zero_le (first.length * second.length)]

theorem rawPack_computes (first second : List Bool) :
    computes rawPackMachine (PSTRTMTwoRawOperands029.rawInput first ++ PSTRTMTwoRawOperands029.rawInput second)
      (PSTRTMBinaryAdd024.operandColumns (digitPairs first second))
      (2048 * (first.length + second.length + 1)^2) (4096 * (first.length + second.length + 1)^2) := by
  refine ⟨rawPackTrace first second, rawPackFinal first second, rawPack_runs first second, ?_,
    rawPack_length_le first second, ?_⟩
  · rw [rawPack_final_tape]
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
  · have hs := PSTRTMTrace002.visitedSpace_le rawPackMachine
      (PSTRTMTwoRawOperands029.rawInput first ++ PSTRTMTwoRawOperands029.rawInput second).length
      (rawPackTrace first second)
    have ht := rawPack_length_le first second
    simp only [PSTRTMTwoRawOperands029.rawInput, List.length_append, List.length_replicate,
      List.length_cons] at hs ⊢
    have hp := pack_length_le [] first second
    simp only [List.length_nil] at hp
    simp only [rawPackTrace, List.length_append, List.length_map, operandStart_length] at hs ⊢
    nlinarith [Nat.zero_le (first.length * second.length)]

theorem encodeNat_rawPack_computes (a b : Nat) :
    computes rawPackMachine (encodeNat a ++ encodeNat b)
      (PSTRTMBinaryAdd024.operandColumns
        (digitPairs (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)))
      (2048 * (natBits a + natBits b + 1)^2) (4096 * (natBits a + natBits b + 1)^2) := by
  simpa only [PSTRTMTwoRawOperands029.rawInput, PSTRTMNatValue017.rawPayload,
    List.length_ofFn, encodeNat, List.append_assoc, List.singleton_append] using
    rawPack_computes (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMRawPack045
