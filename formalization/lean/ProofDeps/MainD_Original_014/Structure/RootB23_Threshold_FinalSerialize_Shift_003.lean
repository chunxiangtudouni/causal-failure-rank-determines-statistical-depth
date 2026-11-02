module
public import Structure.RootB23_Threshold_FinalSerialize_Pass_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.FinalSerialize.Shift
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open RootB23.Threshold.Window.MarshalSerialize

def firstCode : Machine 48 := PSTRTMSeq005.seqMachine
  (PSTRTMSeq005.seqMachine Shift4.code SlideY.markerCode) Uncapped.Steps.fourRightCode

theorem first_bounded (base head next : List Bool) (later : List (List Bool)) (tail : List Bool) :
    BoundedRun firstCode (Tape.mk₂ (markerLeft base) (word head (next :: later) tail)) 48
      (Tape.mk₂ (markerLeft (markerLeft (PSTRTMRawNat010.leftBlocks head.reverse ++ base)))
        (word next later tail)) (14*head.length+31) := by
  let passed := PSTRTMRawNat010.leftBlocks head.reverse ++ base
  have moved : BoundedRun Shift4.code
      (Tape.mk₂ (markerLeft base) (word head (next :: later) tail)) 34
      (Tape.mk₂ passed (false :: false :: false :: false :: false :: false :: true :: false :: word next later tail))
      (14*head.length+17) :=
    ⟨Shift4.actualTrace base [] false true false false (true :: false :: word next later tail) head,
      Shift4.shift_runsFrom _ _ _ _ _ _ _,by rw [Shift4.actual_length]⟩
  have marked := SlideY.marker_bounded passed (false :: false :: true :: false :: word next later tail)
  have entered : BoundedRun Uncapped.Steps.fourRightCode
      (Tape.mk₂ (markerLeft passed) (marker (word next later tail))) 4
      (Tape.mk₂ (markerLeft (markerLeft passed)) (word next later tail)) 5 :=
    ⟨Uncapped.Steps.fourRightTrace (markerLeft passed) false false true false _,
      Uncapped.Steps.fourRight_runsFrom _ _ _ _ _ _,by rfl⟩
  have actual := (moved.seq marked).seq entered
  have port : PSTRTMSeq005.rightLabel (a := 43) (4 : Fin 5) = (48 : Fin 49) := by decide
  rw [port] at actual
  exact actual.mono (by omega)

def passCap : Nat → Nat
  | 0 => 34
  | n+1 => 48 + passCap n + 1

def passCode : (n : Nat) → Machine (passCap n)
  | 0 => Shift4.code
  | n+1 => PSTRTMSeq005.seqMachine firstCode (passCode n)

theorem pass_port (n : Nat) : PSTRTMSeq005.rightLabel (a := 48) (maxLabel (passCap n)) =
    maxLabel (passCap (n+1)) := by
  apply Fin.ext
  change 48+1+passCap n = 48+passCap n+1
  omega

theorem pass_bounded (base head : List Bool) (rest : List (List Bool)) (tail : List Bool) :
    BoundedRun (passCode rest.length) (Tape.mk₂ (markerLeft base) (word head rest tail))
      (maxLabel (passCap rest.length))
      (Tape.mk₂ (endLeft base head rest) (false :: false :: false :: false :: false :: false :: tail))
      (16*width head rest+32*(rest.length+1)) := by
  induction rest generalizing base head with
  | nil =>
    have moved : BoundedRun Shift4.code (Tape.mk₂ (markerLeft base) (word head [] tail)) 34
        (Tape.mk₂ (endLeft base head []) (false :: false :: false :: false :: false :: false :: tail))
        (14*head.length+17) :=
      ⟨Shift4.actualTrace base [] false true false false tail head,
        Shift4.shift_runsFrom _ _ _ _ _ _ _,by rw [Shift4.actual_length]⟩
    exact moved.mono (by rw [width_nil];simp only [List.length_nil];omega)
  | cons next later ih =>
    have first := first_bounded base head next later tail
    have after := ih (markerLeft (PSTRTMRawNat010.leftBlocks head.reverse ++ base)) next
    have joined := first.seq after
    rw [pass_port] at joined
    exact joined.mono (by rw [width_cons];simp only [List.length_cons];omega)

def moveCap (n : Nat) : Nat := 7+passCap n+1
def cap (n : Nat) : Nat := moveCap n+Pass.backCap n+1

def code (n : Nat) : Machine (cap n) := PSTRTMSeq005.seqMachine (a := moveCap n) (b := Pass.backCap n)
  (PSTRTMSeq005.seqMachine (a := 7) (b := passCap n) SlideY.sixRightCode (passCode n)) (Pass.backCode n)

theorem final_port (n : Nat) : PSTRTMSeq005.rightLabel (a := 7+passCap n+1) (maxLabel (Pass.backCap n)) =
    maxLabel (cap n) := by
  apply Fin.ext
  change (7+passCap n+1)+1+Pass.backCap n = (7+passCap n+1)+Pass.backCap n+1
  omega

/-- The whole remaining finite field bank, including every0010 marker,
really moves LEFT4. All four stale trailing cells become paid FALSEs in
front of the arbitrary untouched suffix. No internal gap is folded. -/
theorem bounded (archive head : List Bool) (rest : List (List Bool)) (tail : List Bool) :
    BoundedRun (code rest.length)
      (Tape.mk₂ archive (false :: false :: false :: false :: true :: false :: word head rest tail))
      (maxLabel (cap rest.length))
      (Tape.mk₂ (false :: false :: archive)
        (word head rest (false :: false :: false :: false :: tail)))
      (18*width head rest+42*(rest.length+1)+8) := by
  have entered := SlideY.sixRight_bounded archive (word head rest tail)
  have moved := pass_bounded (false :: false :: archive) head rest tail
  have backed := Pass.back_bounded (false :: archive) head rest (false :: false :: false :: false :: tail)
  have actual := (entered.seq moved).seq backed
  rw [final_port] at actual
  exact actual.mono (by omega)

end RootB23.Threshold.FinalSerialize.Shift
