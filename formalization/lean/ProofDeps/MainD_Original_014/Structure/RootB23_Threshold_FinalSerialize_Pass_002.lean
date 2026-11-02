module
public import Structure.RootB23_Threshold_FinalSerialize_Schema_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.FinalSerialize.Pass
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open RootB23.Threshold.Window.MarshalSerialize

theorem walk_one (left head tail : List Bool) :
    BoundedRun Uncapped.Walk.code (Tape.mk₂ left (word head [] tail)) 2
      (Tape.mk₂ (PSTRTMRawNat010.leftBlocks head.reverse ++ left) (false :: false :: tail))
      (2*head.length+3) :=
  ⟨Uncapped.Walk.actualTrace left head tail,Uncapped.Walk.field_runsFrom left head tail,
    by rw [Uncapped.Walk.actual_length]⟩

def nextCode : Machine 7 := Uncapped.Serialize.locateCode

theorem next_bounded (left head next : List Bool) (later : List (List Bool)) (tail : List Bool) :
    BoundedRun nextCode (Tape.mk₂ left (word head (next :: later) tail)) 7
      (Tape.mk₂ (markerLeft (PSTRTMRawNat010.leftBlocks head.reverse ++ left)) (word next later tail))
      (2*head.length+8) := by
  have walked := walk_one left head (true :: false :: word next later tail)
  have moved : BoundedRun Uncapped.Steps.fourRightCode
      (Tape.mk₂ (PSTRTMRawNat010.leftBlocks head.reverse ++ left) (marker (word next later tail))) 4
      (Tape.mk₂ (markerLeft (PSTRTMRawNat010.leftBlocks head.reverse ++ left)) (word next later tail)) 5 :=
    ⟨Uncapped.Steps.fourRightTrace _ false false true false _,
      Uncapped.Steps.fourRight_runsFrom _ _ _ _ _ _,by rfl⟩
  exact (walked.seq moved).mono (by omega)

def walkCap : Nat → Nat
  | 0 => 2
  | n+1 => 7 + walkCap n + 1

def walkCode : (n : Nat) → Machine (walkCap n)
  | 0 => Uncapped.Walk.code
  | n+1 => PSTRTMSeq005.seqMachine nextCode (walkCode n)

theorem walk_port (n : Nat) : PSTRTMSeq005.rightLabel (a := 7) (maxLabel (walkCap n)) =
    maxLabel (walkCap (n+1)) := by
  apply Fin.ext
  change 7+1+walkCap n = 7+walkCap n+1
  omega

theorem walk_bounded (left head : List Bool) (rest : List (List Bool)) (tail : List Bool) :
    BoundedRun (walkCode rest.length) (Tape.mk₂ left (word head rest tail)) (maxLabel (walkCap rest.length))
      (Tape.mk₂ (endLeft left head rest) (false :: false :: tail))
      (2*width head rest+8*(rest.length+1)) := by
  induction rest generalizing left head with
  | nil =>
    exact (walk_one left head tail).mono (by rw [width_nil];simp only [List.length_nil];omega)
  | cons next later ih =>
    have first := next_bounded left head next later tail
    have after := ih (markerLeft (PSTRTMRawNat010.leftBlocks head.reverse ++ left)) next
    have joined := first.seq after
    rw [walk_port] at joined
    exact joined.mono (by rw [width_cons];simp only [List.length_cons];omega)

theorem rewind_one (archive head tail : List Bool) :
    BoundedRun PSTRTMMulRewind085.rewindMachine
      (Tape.mk₂ (PSTRTMRawNat010.leftBlocks head.reverse ++ false :: archive) tail) 3
      (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks head ++ tail)) (2*head.length+3) :=
    ⟨PSTRTMPairRewind105.fullTrace archive head.reverse tail,
      PSTRTMPairRewind105.rewind_runsFrom archive head tail,
      by rw [PSTRTMPairRewind105.full_length,List.length_reverse]⟩

def backCap : Nat → Nat
  | 0 => 3
  | n+1 => (backCap n+5+1)+3+1

def backCode : (n : Nat) → Machine (backCap n)
  | 0 => PSTRTMMulRewind085.rewindMachine
  | n+1 => PSTRTMSeq005.seqMachine (a := backCap n+5+1) (b := 3)
      (PSTRTMSeq005.seqMachine (a := backCap n) (b := 5) (backCode n) SlideY.fourLeftCode)
      PSTRTMMulRewind085.rewindMachine

theorem back_port (n : Nat) :
    PSTRTMSeq005.rightLabel (a := backCap n+5+1) (3 : Fin 4) = maxLabel (backCap (n+1)) := by
  apply Fin.ext
  change (backCap n+5+1)+1+(3 : Fin 4).val = (backCap n+5+1)+3+1
  simp only [show (3 : Fin 4).val = 3 by decide]

theorem back_bounded (archive head : List Bool) (rest : List (List Bool)) (tail : List Bool) :
    BoundedRun (backCode rest.length)
      (Tape.mk₂ (endLeft (false :: archive) head rest) (false :: false :: tail))
      (maxLabel (backCap rest.length)) (Tape.mk₂ (false :: archive) (word head rest tail))
      (2*width head rest+10*(rest.length+1)) := by
  induction rest generalizing archive head with
  | nil =>
    exact (rewind_one archive head (false :: false :: tail)).mono
      (by rw [width_nil];simp only [List.length_nil];omega)
  | cons next later ih =>
    let passed := PSTRTMRawNat010.leftBlocks head.reverse ++ false :: archive
    have after := ih (true :: false :: false :: passed) next
    have crossed := SlideY.fourLeft_bounded passed (word next later tail)
    have returned := rewind_one archive head (marker (word next later tail))
    have joined := (after.seq crossed).seq returned
    rw [back_port] at joined
    have fee : 2*width next later+10*(later.length+1)+6+(2*head.length+3) ≤
        2*width head (next :: later)+10*((next :: later).length+1) := by
      rw [width_cons]
      simp only [List.length_cons]
      omega
    exact joined.mono fee

end RootB23.Threshold.FinalSerialize.Pass
