module

public import Common.PSTR_TM_Prepend_022

/-! The SAME frozen literal-prepend machine on a genuine retained tape.
It really consumes the nearest left cells: the protected remainder is
left.drop fragment.length. There is no cursor reset or archive-copy oracle.
The literal fragment is fixed program code before all runtime tapes. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLiteral

open Turing PSTRTMTrace002 PSTRTMSeq005 PSTRTMPrepend022

def bitFrame (label : Fin 3) (left right : List Bool) : MachineState 2 :=
  ⟨label, Tape.mk₂ left right⟩

def bitFrameTrace (bit : Bool) (left right : List Bool) : List (MachineState 2) :=
  [bitFrame 0 left right,
    bitFrame 1 left.tail (left.headI :: right),
    bitFrame 2 left.tail (bit :: right)]

theorem bit_runsFrom (bit : Bool) (left right : List Bool) :
    RunsFrom (bitMachine bit) (bitFrame 0 left right)
      (bitFrameTrace bit left right) (bitFrame 2 left.tail (bit :: right)) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · cases left <;> cases right <;>
      simp [bitFrameTrace, List.isChain_cons_cons, bitFrame, TM0.step,
        bitMachine, Tape.mk₂]
  · simp [bitFrame, TM0.step, bitMachine]

def prefixFrameTrace : (fragment : List Bool) → List Bool → List Bool →
    List (MachineState (prefixStates fragment))
  | [], left, right => [⟨0, Tape.mk₂ left right⟩]
  | bit :: later, left, right =>
    (prefixFrameTrace later left right).map (leftCfg (b := 2)) ++
      (bitFrameTrace bit (left.drop later.length) (later ++ right)).map
        (rightCfg (a := prefixStates later))

def prefixFrameFinal : (fragment : List Bool) → List Bool → List Bool →
    MachineState (prefixStates fragment)
  | [], left, right => ⟨0, Tape.mk₂ left right⟩
  | bit :: later, left, right =>
    rightCfg (a := prefixStates later)
      (bitFrame 2 (left.drop later.length).tail (bit :: (later ++ right)))

theorem prefixFrame_final_tape (fragment left right : List Bool) :
    (prefixFrameFinal fragment left right).Tape =
      Tape.mk₂ (left.drop fragment.length) (fragment ++ right) := by
  cases fragment with
  | nil => rfl
  | cons bit later =>
    simp only [prefixFrameFinal, rightCfg, bitFrame, List.length_cons, List.tail_drop]
    rfl

theorem prefixFrame_length (fragment left right : List Bool) :
    (prefixFrameTrace fragment left right).length = 3 * fragment.length + 1 := by
  induction fragment with
  | nil => rfl
  | cons bit later ih =>
    change ((prefixFrameTrace later left right).map (leftCfg (b := 2)) ++
      (bitFrameTrace bit (left.drop later.length) (later ++ right)).map
        (rightCfg (a := prefixStates later))).length = 3 * (bit :: later).length + 1
    rw [List.length_append, List.length_map, List.length_map, ih]
    simp only [bitFrameTrace, List.length_cons, List.length_nil]
    omega

theorem prefix_runsFrom (fragment left right : List Bool) :
    RunsFrom (prefixMachine fragment) ⟨0, Tape.mk₂ left right⟩
      (prefixFrameTrace fragment left right) (prefixFrameFinal fragment left right) := by
  induction fragment with
  | nil => exact ⟨rfl, .singleton _, rfl, rfl⟩
  | cons bit later ih =>
    have second : RunsFrom (bitMachine bit)
        ⟨0, (prefixFrameFinal later left right).Tape⟩
        (bitFrameTrace bit (left.drop later.length) (later ++ right))
        (bitFrame 2 (left.drop later.length).tail (bit :: (later ++ right))) := by
      rw [prefixFrame_final_tape]
      exact bit_runsFrom bit (left.drop later.length) (later ++ right)
    apply seq_runsFrom (prefixMachine later) (bitMachine bit)
      ⟨0, Tape.mk₂ left right⟩ (prefixFrameFinal later left right)
      (bitFrame 2 (left.drop later.length).tail (bit :: (later ++ right)))
      (prefixFrameTrace later left right)
      (bitFrameTrace bit (left.drop later.length) (later ++ right))
    · exact ih
    · exact second

/-- Original visitedSpace, charged with the caller's full input length.
The left side is overwritten, rather than assumed to be blank or preserved. -/
theorem prefixFrame_space (fragment left right : List Bool) (inputLength : Nat) :
    visitedSpace (prefixMachine fragment) inputLength (prefixFrameTrace fragment left right) ≤
      inputLength + 6 * fragment.length + 3 := by
  have bound := visitedSpace_le (prefixMachine fragment) inputLength
    (prefixFrameTrace fragment left right)
  rw [prefixFrame_length] at bound
  omega

/-- An actually supplied reserve protects the archive exactly. Its existence
or production is not part of this literal-writing component. -/
theorem prefixFrame_reserved (fragment reserve archive right : List Bool)
    (room : reserve.length = fragment.length) :
    (prefixFrameFinal fragment (reserve ++ archive) right).Tape =
      Tape.mk₂ archive (fragment ++ right) := by
  rw [prefixFrame_final_tape, ← room, List.drop_left]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLiteral
