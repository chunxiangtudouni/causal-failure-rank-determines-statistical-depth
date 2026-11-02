module
public import Common.PSTR_TM_TwoRawOperands_029

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMOperandStart033
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTwoRawOperands029 PSTRTMTrace002

/-- Four actual owned separator cells precede the second-operand head.
Move onto their first pad cell; no original operand width is supplied. -/
def leftFourMachine : Machine 4 := fun q _ =>
  if h : q.val < 4 then some (⟨q.val + 1, by omega⟩, .move .left) else none

def leftState (q : Fin 5) (left right : List Bool) : MachineState 4 := ⟨q, Turing.Tape.mk₂ left right⟩

def leftTrace (first second suffix : List Bool) : List (MachineState 4) :=
  let old := PSTRTMRawNat010.leftBlocks first.reverse
  let right := PSTRTMIncrement009.blocks second ++ false :: suffix
  [leftState 0 (false :: true :: false :: false :: old) right,
    leftState 1 (true :: false :: false :: old) (false :: right),
    leftState 2 (false :: false :: old) (true :: false :: right),
    leftState 3 (false :: old) (false :: true :: false :: right),
    leftState 4 old (false :: false :: true :: false :: right)]

theorem left_runsFrom (first second suffix : List Bool) :
    PSTRTMSeq005.RunsFrom leftFourMachine
      ⟨0, (twoOperandFinal first second suffix).Tape⟩ (leftTrace first second suffix)
      (leftState 4 (PSTRTMRawNat010.leftBlocks first.reverse)
        (false :: false :: true :: false :: (PSTRTMIncrement009.blocks second ++ false :: suffix))) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [leftTrace, List.isChain_cons_cons, Turing.TM0.step, leftFourMachine, leftState, Turing.Tape.mk₂]
  · simp [Turing.TM0.step, leftFourMachine, leftState]

def backSuffix (second suffix : List Bool) : List Bool :=
  false :: true :: false :: (PSTRTMIncrement009.blocks second ++ false :: suffix)

def backMachine : Machine 21 := PSTRTMSeq005.seqMachine leftFourMachine PSTRTMRawNat010.rawNatMachine

def backTrace (first second suffix : List Bool) : List (MachineState 21) :=
  (leftTrace first second suffix).map (PSTRTMSeq005.leftCfg (b := 16)) ++
    (PSTRTMRawNat010.doneTrace first.reverse (backSuffix second suffix)).map (PSTRTMSeq005.rightCfg (a := 4))

def internalWord (first second suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks first ++ false :: false :: true :: false ::
    (PSTRTMIncrement009.blocks second ++ false :: suffix)

def backFinal (first second suffix : List Bool) : MachineState 21 :=
  PSTRTMSeq005.rightCfg (a := 4) (PSTRTMRawNat010.state 16 [false] (internalWord first second suffix))

/-- Reuse EXACT frozen010 code on the actual pad0. Its q0false branch only
rewinds the true first-operand flag cells, retaining the second operand. -/
theorem back_runsFrom (first second suffix : List Bool) :
    PSTRTMSeq005.RunsFrom backMachine ⟨0, (twoOperandFinal first second suffix).Tape⟩
      (backTrace first second suffix) (backFinal first second suffix) := by
  apply PSTRTMSeq005.seq_runsFrom leftFourMachine PSTRTMRawNat010.rawNatMachine
    ⟨0, (twoOperandFinal first second suffix).Tape⟩
    (leftState 4 (PSTRTMRawNat010.leftBlocks first.reverse)
      (false :: false :: true :: false :: (PSTRTMIncrement009.blocks second ++ false :: suffix)))
    (PSTRTMRawNat010.state 16 [false] (internalWord first second suffix))
    (leftTrace first second suffix) (PSTRTMRawNat010.doneTrace first.reverse (backSuffix second suffix))
  · exact left_runsFrom first second suffix
  · refine ⟨rfl, PSTRTMRawNat010.done_chain _ _, ?_, PSTRTMRawNat010.rawNat_halt _ _⟩
    simpa [internalWord, backSuffix] using PSTRTMRawNat010.done_last first.reverse (backSuffix second suffix)

theorem back_length (first second suffix : List Bool) :
    (backTrace first second suffix).length = 2 * first.length + 8 := by
  simp only [backTrace, List.length_append, List.length_map, leftTrace,
    List.length_cons, List.length_nil, PSTRTMRawNat010.done_length, List.length_reverse]
  omega

/-- Uniform151-label original-two-field front end, now returning the real
head to the first internal operand for the actual alignment program. -/
def operandStartMachine : Machine 150 := PSTRTMSeq005.seqMachine twoOperandMachine backMachine

def operandStartTrace (first second suffix : List Bool) : List (MachineState 150) :=
  (twoOperandTrace first second suffix).map (PSTRTMSeq005.leftCfg (b := 21)) ++
    (backTrace first second suffix).map (PSTRTMSeq005.rightCfg (a := 128))

def operandStartFinal (first second suffix : List Bool) : MachineState 150 :=
  PSTRTMSeq005.rightCfg (a := 128) (backFinal first second suffix)

theorem operandStart_runs (first second suffix : List Bool) :
    Runs operandStartMachine (rawInput first ++ rawInput second ++ suffix)
      (operandStartTrace first second suffix) (operandStartFinal first second suffix) := by
  exact PSTRTMSeq005.seq_runs twoOperandMachine backMachine
    (rawInput first ++ rawInput second ++ suffix)
    (twoOperandFinal first second suffix) (backFinal first second suffix)
    (twoOperandTrace first second suffix) (backTrace first second suffix)
    (twoOperand_runs first second suffix) (back_runsFrom first second suffix)

theorem operandStart_length (first second suffix : List Bool) :
    (operandStartTrace first second suffix).length = first.length^2 + second.length^2 +
      29 * first.length + 11 * second.length + 43 := by
  simp only [operandStartTrace, List.length_append, List.length_map, twoOperand_length, back_length]
  ring

theorem operandStart_final_tape (first second suffix : List Bool) :
    (operandStartFinal first second suffix).Tape = Turing.Tape.mk₁ (internalWord first second suffix) := by
  simp only [operandStartFinal, backFinal, PSTRTMSeq005.rightCfg, PSTRTMRawNat010.state,
    Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]

theorem operandStart_computes (first second suffix : List Bool) :
    computes operandStartMachine (rawInput first ++ rawInput second ++ suffix) (internalWord first second suffix)
      (1024 * (first.length + second.length + 1)^2)
      (1024 * (first.length + second.length + 1)^2 + suffix.length) := by
  refine ⟨operandStartTrace first second suffix, operandStartFinal first second suffix,
    operandStart_runs first second suffix, ?_, ?_, ?_⟩
  · rw [operandStart_final_tape]
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
  · rw [operandStart_length]
    nlinarith [Nat.zero_le (first.length * second.length)]
  · have hs := visitedSpace_le operandStartMachine (rawInput first ++ rawInput second ++ suffix).length
      (operandStartTrace first second suffix)
    rw [operandStart_length] at hs
    simp only [rawInput, List.length_append, List.length_replicate, List.length_cons] at hs ⊢
    nlinarith [Nat.zero_le (first.length * second.length)]

/-- EMPTY suffix gives an actual isolated whole tape. This establishes
infinite blank EOF for B; it does not confuse a single written0 with two
owned cells when an arbitrary suffix is present. -/
theorem isolated_final_tape (first second : List Bool) :
    (operandStartFinal first second []).Tape =
      Turing.Tape.mk₁ (PSTRTMIncrement009.blocks first ++ [false,false,true,false] ++ PSTRTMIncrement009.blocks second) := by
  rw [operandStart_final_tape]
  have hw : internalWord first second [] =
      (PSTRTMIncrement009.blocks first ++ [false,false,true,false] ++ PSTRTMIncrement009.blocks second) ++ [false] := by
    simp [internalWord, List.append_assoc]
  rw [hw]
  simp only [Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_append_false]

theorem encodeNat_operandStart_computes (a b : Nat) :
    let first := List.ofFn (fun i : Fin (natBits a) => a.testBit i.val)
    let second := List.ofFn (fun i : Fin (natBits b) => b.testBit i.val)
    computes operandStartMachine (encodeNat a ++ encodeNat b)
      (PSTRTMIncrement009.blocks first ++ [false,false,true,false] ++ PSTRTMIncrement009.blocks second)
      (1024 * (natBits a + natBits b + 1)^2) (1024 * (natBits a + natBits b + 1)^2) := by
  dsimp only
  let first := List.ofFn (fun i : Fin (natBits a) => a.testBit i.val)
  let second := List.ofFn (fun i : Fin (natBits b) => b.testBit i.val)
  refine ⟨operandStartTrace first second [], operandStartFinal first second [], ?_, ?_, ?_, ?_⟩
  · simpa [rawInput, encodeNat, first, second] using operandStart_runs first second []
  · rw [isolated_final_tape]
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂, first, second]
  · have h := operandStart_length first second []
    simp only [first, second, List.length_ofFn] at h
    nlinarith [Nat.zero_le (natBits a * natBits b)]
  · have hs := visitedSpace_le operandStartMachine (encodeNat a ++ encodeNat b).length
      (operandStartTrace first second [])
    have ht := operandStart_length first second []
    simp only [encodeNat, first, second, List.length_append, List.length_replicate,
      List.length_singleton, List.length_ofFn] at hs ht ⊢
    nlinarith [Nat.zero_le (natBits a * natBits b)]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMOperandStart033
