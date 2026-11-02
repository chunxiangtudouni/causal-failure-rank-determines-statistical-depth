module
public import Common.PSTR_TM_ContextRaw_028

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTwoRawOperands029
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMOperandCursor027 PSTRTMContextRaw028 PSTRTMTrace002

def rawInput (digits : List Bool) : List Bool :=
  List.replicate digits.length true ++ false :: digits

def keptContext (first : List Bool) : List Bool :=
  true :: false :: false :: PSTRTMRawNat010.leftBlocks first.reverse

/-- Uniform129-label program actually decodes TWO original raw fields.
The first operand and real00+10 separator survive in the left tape; the
second raw decoder uses its actual false guard, not an external frame law. -/
def twoOperandMachine : Machine 128 :=
  PSTRTMSeq005.seqMachine firstOperandMachine PSTRTMRawNat010.rawNatMachine

def twoOperandTrace (first second suffix : List Bool) : List (MachineState 128) :=
  (firstOperandTrace first (rawInput second ++ suffix)).map (PSTRTMSeq005.leftCfg (b := 16)) ++
    (contextTrace (keptContext first) [] second suffix).map (PSTRTMSeq005.rightCfg (a := 111))

def twoOperandFinal (first second suffix : List Bool) : MachineState 128 :=
  PSTRTMSeq005.rightCfg (a := 111)
    (PSTRTMRawNat010.state 16 (false :: keptContext first) (PSTRTMIncrement009.blocks second ++ false :: suffix))

theorem twoOperand_runs (first second suffix : List Bool) :
    Runs twoOperandMachine (rawInput first ++ rawInput second ++ suffix)
      (twoOperandTrace first second suffix) (twoOperandFinal first second suffix) := by
  apply PSTRTMSeq005.seq_runs firstOperandMachine PSTRTMRawNat010.rawNatMachine
    (rawInput first ++ rawInput second ++ suffix)
    (firstOperandFinal first (rawInput second ++ suffix))
    (PSTRTMRawNat010.state 16 (false :: keptContext first) (PSTRTMIncrement009.blocks second ++ false :: suffix))
    (firstOperandTrace first (rawInput second ++ suffix))
    (contextTrace (keptContext first) [] second suffix)
  · simpa [rawInput, List.append_assoc] using firstOperand_runs first (rawInput second ++ suffix)
  · have h := context_runsFrom (keptContext first) second suffix
    rw [firstOperand_final_tape]
    simpa [PSTRTMRawNat010.state, keptContext, rawInput, List.append_assoc] using h

theorem twoOperand_final_tape (first second suffix : List Bool) :
    (twoOperandFinal first second suffix).Tape =
      Turing.Tape.mk₂ (false :: true :: false :: false :: PSTRTMRawNat010.leftBlocks first.reverse)
        (PSTRTMIncrement009.blocks second ++ false :: suffix) := rfl

theorem twoOperand_length (first second suffix : List Bool) :
    (twoOperandTrace first second suffix).length = first.length^2 + second.length^2 +
      27 * first.length + 11 * second.length + 35 := by
  simp only [twoOperandTrace, List.length_append, List.length_map,
    firstOperand_length, context_length, List.length_nil]
  ring

/-- Both costs are for this actual original-input trace. No width/cost
certificate or internal column layout is supplied in the original input. -/
theorem twoOperand_trace_cost (first second suffix : List Bool) :
    (twoOperandTrace first second suffix).length ≤ 512 * (first.length + second.length + 1)^2 ∧
      visitedSpace twoOperandMachine (rawInput first ++ rawInput second ++ suffix).length
        (twoOperandTrace first second suffix) ≤
          512 * (first.length + second.length + 1)^2 + suffix.length := by
  constructor
  · rw [twoOperand_length]
    nlinarith [Nat.zero_le (first.length * second.length)]
  · have hs := visitedSpace_le twoOperandMachine
      (rawInput first ++ rawInput second ++ suffix).length (twoOperandTrace first second suffix)
    rw [twoOperand_length] at hs
    simp only [rawInput, List.length_append, List.length_replicate, List.length_cons] at hs ⊢
    nlinarith [Nat.zero_le (first.length * second.length)]

/-- Original encodeNat at BOTH operand positions. This only proves real
transport to separated internal operands; actual alignment and arithmetic
composition remain obligations, so no original B23 arithmetic is assumed. -/
theorem encodeNat_twoOperand_runs (a b : Nat) (suffix : List Bool) :
    let first := List.ofFn (fun i : Fin (natBits a) => a.testBit i.val)
    let second := List.ofFn (fun i : Fin (natBits b) => b.testBit i.val)
    Runs twoOperandMachine (encodeNat a ++ encodeNat b ++ suffix)
      (twoOperandTrace first second suffix) (twoOperandFinal first second suffix) := by
  dsimp only
  simpa [encodeNat, rawInput] using twoOperand_runs
    (List.ofFn (fun i : Fin (natBits a) => a.testBit i.val))
    (List.ofFn (fun i : Fin (natBits b) => b.testBit i.val)) suffix

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTwoRawOperands029
