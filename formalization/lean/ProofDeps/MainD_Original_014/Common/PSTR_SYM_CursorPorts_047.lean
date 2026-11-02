module

public import Common.PSTR_SYM_MarkedReturn_046
public import Common.PSTR_SYM_CounterRound_031
public import Common.PSTR_SYM_ZeroPorts_021

/-! Actual existing-code ports for the cursor/counter join: six RIGHTs,
one RIGHT, genuine header rewind, and borrow/zero with all three saved
bits. Entry at labels13/18 of the frozen19-RIGHT code must itself be
established by a charged control transfer in the future whole program. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorPorts

open Turing PSTRTMSeq005 PA17TMRatArithmeticParse002
open PSTRSymbolicZeroTail PSTRSymbolicCarry PSTRSymbolicCounter

def rightSixTrace (tape : Tape Bool) : List (MachineState 19) := rightTrace 13 6 (by decide) tape
def rightOneTrace (tape : Tape Bool) : List (MachineState 19) := rightTrace 18 1 (by decide) tape

theorem right_six_runsFrom (tape : Tape Bool) :
    RunsFrom right19Machine (rightState 13 (by decide) tape) (rightSixTrace tape)
      (rightState 19 (by decide) ((Tape.move .right)^[6] tape)) := by
  refine ⟨rightTrace_head 13 6 (by decide) tape, rightTrace_chain 13 6 (by decide) tape,
    rightTrace_last 13 6 (by decide) tape, ?_⟩
  simp [TM0.step, right19Machine, rightState]

theorem right_one_runsFrom (tape : Tape Bool) :
    RunsFrom right19Machine (rightState 18 (by decide) tape) (rightOneTrace tape)
      (rightState 19 (by decide) (tape.move .right)) := by
  refine ⟨rightTrace_head 18 1 (by decide) tape, rightTrace_chain 18 1 (by decide) tape,
    rightTrace_last 18 1 (by decide) tape, ?_⟩
  simp [TM0.step, right19Machine, rightState]

theorem right_six_length (tape : Tape Bool) : (rightSixTrace tape).length = 7 :=
  rightTrace_length 13 6 (by decide) tape

theorem right_one_length (tape : Tape Bool) : (rightOneTrace tape).length = 2 :=
  rightTrace_length 18 1 (by decide) tape

theorem six_moves_tape (left suffix : List Bool) (a b c d e f : Bool) :
    (Tape.move .right)^[6] (Tape.mk₂ left (a :: b :: c :: d :: e :: f :: suffix)) =
      Tape.mk₂ (f :: e :: d :: c :: b :: a :: left) suffix := by
  simp [Function.iterate_succ_apply, Tape.mk₂]

theorem carried_field_back (carry : Fin 8) (archive digits suffix : List Bool) :
    RunsFrom (carryMachine fieldBackMachine)
      (carryCfg carry ⟨0,Tape.mk₂ (false :: (PSTRTMRawNat010.leftBlocks digits.reverse ++ false :: archive)) suffix⟩)
      ((fieldBackTrace archive digits suffix).map (carryCfg carry))
      (carryCfg carry (fieldBackFinal archive digits suffix)) :=
  carry_runsFrom fieldBackMachine carry _ _ _ (fieldBack_runsFrom archive digits suffix)

theorem carried_field_back_tape (carry : Fin 8) (archive digits suffix : List Bool) :
    (carryCfg carry (fieldBackFinal archive digits suffix)).Tape =
      Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks digits ++ false :: suffix) :=
  fieldBack_final_tape archive digits suffix

theorem carried_field_back_length (carry : Fin 8) (archive digits suffix : List Bool) :
    ((fieldBackTrace archive digits suffix).map (carryCfg carry)).length = 2 * digits.length + 5 := by
  rw [List.length_map, fieldBackTrace_length]

theorem carried_counter_round (carry : Fin 8) (archive digits suffix : List Bool)
    (positive : true ∈ digits) :
    RunsFrom (carryMachine counterRoundMachine)
      (carryCfg carry ⟨0,Tape.mk₂ (false :: archive)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: suffix)⟩)
      ((counterRoundTrace archive digits suffix).map (carryCfg carry))
      (carryCfg carry (counterRoundFinal archive digits suffix)) :=
  carry_runsFrom counterRoundMachine carry _ _ _ (counterRound_runsFrom archive digits suffix positive)

/-- The real counter callee ends on END00. Reaching N's tag subsequently
requires one actual RIGHT operation, with no reset to the first digit. -/
theorem carried_counter_end_tape (carry : Fin 8) (archive digits suffix : List Bool) :
    (carryCfg carry (counterRoundFinal archive digits suffix)).Tape =
      Tape.mk₂ (PSTRTMRawNat010.leftBlocks (PSTRTMThresholdCountdownCode164.predDigits digits).reverse ++ false :: archive)
        (false :: false :: suffix) := counterRound_final_tape archive digits suffix

theorem carried_counter_zero_port (carry : Fin 8) (archive digits suffix : List Bool)
    (positive : true ∈ digits) :
    (originalLabel (carryCfg carry (counterRoundFinal archive digits suffix)).q).val = 15 ↔
      PSTRTMIncrement009.valueDigits digits = 1 := by
  change (originalLabel (carryLabel (counterRoundFinal archive digits suffix).q carry)).val = 15 ↔ _
  rw [original_carry]
  exact counterRound_zero_port archive digits suffix positive

theorem carried_counter_saved (carry : Fin 8) (archive digits suffix : List Bool) :
    savedLabel (carryCfg carry (counterRoundFinal archive digits suffix)).q = carry :=
  carry_saved carry _

theorem carried_counter_time (carry : Fin 8) (archive digits suffix : List Bool)
    (positive : true ∈ digits) :
    ((counterRoundTrace archive digits suffix).map (carryCfg carry)).length ≤ 8 * (digits.length + 1) := by
  rw [List.length_map]
  exact counterRound_time_le archive digits suffix positive

theorem carried_counter_prefix_space (carry : Fin 8) (archive digits suffix : List Bool)
    (positive : true ∈ digits) (inputLength clock : Nat) :
    visitedSpace (carryMachine counterRoundMachine) inputLength
      (((counterRoundTrace archive digits suffix).map (carryCfg carry)).take clock) ≤
        inputLength + 16 * (digits.length + 1) + 1 := by
  rw [← List.map_take, carry_space]
  exact counterRound_prefix_space archive digits suffix positive inputLength clock

theorem right_six_prefix_space (tape : Tape Bool) (inputLength clock : Nat) :
    visitedSpace right19Machine inputLength ((rightSixTrace tape).take clock) ≤ inputLength + 15 := by
  have cells := PSTRTMTrace002.visitedSpace_le right19Machine inputLength ((rightSixTrace tape).take clock)
  have count : ((rightSixTrace tape).take clock).length ≤ 7 := by
    simp only [List.length_take, right_six_length]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorPorts
