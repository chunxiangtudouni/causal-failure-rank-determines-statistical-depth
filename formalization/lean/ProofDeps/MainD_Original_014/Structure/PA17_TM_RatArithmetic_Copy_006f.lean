module
public import Structure.PA17_TM_RatArithmetic_Copy_006e
public import Structure.PA17_TM_RatArithmetic_Unblock_004d

/-! Compose the physical field copy with the frozen inverse encoder. Every
HALT transfer is a real charged write-self step; the original footer is
clamped for the inverse call and physically restored afterwards. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006

def clampMachine : Machine 2 := fun q _ =>
  match q.val with
  | 0 => some (1,.write false)
  | 1 => some (2,.move .right)
  | _ => none

def restoreMachine : Machine 3 := fun q _ =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.write true)
  | 2 => some (3,.move .right)
  | _ => none

def clampTrace (left digits : List Bool) : List (MachineState 2) :=
  [⟨0,Turing.Tape.mk₂ left (true::workspace digits)⟩,
   ⟨1,Turing.Tape.mk₂ left (false::workspace digits)⟩,
   ⟨2,Turing.Tape.mk₂ (false::left) (workspace digits)⟩]

def restoreTrace (left word : List Bool) : List (MachineState 3) :=
  [⟨0,Turing.Tape.mk₂ (false::left) word⟩,
   ⟨1,Turing.Tape.mk₂ left (false::word)⟩,
   ⟨2,Turing.Tape.mk₂ left (true::word)⟩,
   ⟨3,Turing.Tape.mk₂ (true::left) word⟩]

theorem clamp_runsFrom (left digits : List Bool) :
    PSTRTMSeq005.RunsFrom clampMachine ⟨0,Turing.Tape.mk₂ left (true::workspace digits)⟩
      (clampTrace left digits) ⟨2,Turing.Tape.mk₂ (false::left) (workspace digits)⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [clampTrace,List.isChain_cons_cons,Turing.TM0.step,clampMachine,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,clampMachine]

theorem restore_runsFrom (left word : List Bool) :
    PSTRTMSeq005.RunsFrom restoreMachine ⟨0,Turing.Tape.mk₂ (false::left) word⟩
      (restoreTrace left word) ⟨3,Turing.Tape.mk₂ (true::left) word⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [restoreTrace,List.isChain_cons_cons,Turing.TM0.step,restoreMachine,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,restoreMachine]

def decodeRestoreMachine : Machine 23 :=
  PSTRTMSeq005.seqMachine PA17TMRatArithmeticUnblock004.markerMachine restoreMachine

def decodeRestoreTrace (left digits : List Bool) : List (MachineState 23) :=
  (PA17TMRatArithmeticUnblock004.markerTrace left digits []).map (PSTRTMSeq005.leftCfg (b := 3)) ++
  (restoreTrace left (PSTRTMUnblockTrace019.rawWord digits ++ [true])).map (PSTRTMSeq005.rightCfg (a := 19))

def decodeRestoreFinal (left digits : List Bool) : MachineState 23 :=
  ⟨23,Turing.Tape.mk₂ (true::left) (PSTRTMUnblockTrace019.rawWord digits ++ [true])⟩

theorem decodeRestore_runsFrom (left digits : List Bool) :
    PSTRTMSeq005.RunsFrom decodeRestoreMachine ⟨0,Turing.Tape.mk₂ (false::left) (workspace digits)⟩
      (decodeRestoreTrace left digits) (decodeRestoreFinal left digits) := by
  have h := PSTRTMSeq005.seq_runsFrom PA17TMRatArithmeticUnblock004.markerMachine restoreMachine
    (PSTRTMUnblock018.state 0 (false::left) (workspace digits))
    (PSTRTMUnblock018.state 19 (false::left) (PSTRTMUnblockTrace019.rawWord digits ++ [true]))
    ⟨3,Turing.Tape.mk₂ (true::left) (PSTRTMUnblockTrace019.rawWord digits ++ [true])⟩
    (PA17TMRatArithmeticUnblock004.markerTrace left digits [])
    (restoreTrace left (PSTRTMUnblockTrace019.rawWord digits ++ [true]))
    (PA17TMRatArithmeticUnblock004.marker_runsFrom left digits [])
    (restore_runsFrom left (PSTRTMUnblockTrace019.rawWord digits ++ [true]))
  exact h

theorem decodeRestore_length (left digits : List Bool) :
    (decodeRestoreTrace left digits).length = digits.length^2+11*digits.length+10 := by
  simp only [decodeRestoreTrace,List.length_append,List.length_map,
    PA17TMRatArithmeticUnblock004.marker_length]
  change digits.length^2+11*digits.length+6+4 = _
  omega

def encodeCopyMachine : Machine 26 := PSTRTMSeq005.seqMachine clampMachine decodeRestoreMachine

def encodeCopyTrace (left digits : List Bool) : List (MachineState 26) :=
  (clampTrace left digits).map (PSTRTMSeq005.leftCfg (b := 23)) ++
  (decodeRestoreTrace left digits).map (PSTRTMSeq005.rightCfg (a := 2))

def encodeCopyFinal (left digits : List Bool) : MachineState 26 :=
  ⟨26,Turing.Tape.mk₂ (true::left) (PSTRTMUnblockTrace019.rawWord digits ++ [true])⟩

theorem encodeCopy_runsFrom (left digits : List Bool) :
    PSTRTMSeq005.RunsFrom encodeCopyMachine ⟨0,Turing.Tape.mk₂ left (true::workspace digits)⟩
      (encodeCopyTrace left digits) (encodeCopyFinal left digits) := by
  have h := PSTRTMSeq005.seq_runsFrom clampMachine decodeRestoreMachine
    ⟨0,Turing.Tape.mk₂ left (true::workspace digits)⟩ ⟨2,Turing.Tape.mk₂ (false::left) (workspace digits)⟩
    (decodeRestoreFinal left digits) (clampTrace left digits) (decodeRestoreTrace left digits)
    (clamp_runsFrom left digits) (decodeRestore_runsFrom left digits)
  exact h

theorem encodeCopy_length (left digits : List Bool) :
    (encodeCopyTrace left digits).length = digits.length^2+11*digits.length+13 := by
  simp only [encodeCopyTrace,List.length_append,List.length_map,decodeRestore_length]
  change 3+(digits.length^2+11*digits.length+10) = _
  omega

def rawCopyMachine : Machine 69 := PSTRTMSeq005.seqMachine copyMachine encodeCopyMachine

def rawCopyTrace (archive digits : List Bool) : List (MachineState 69) :=
  (copyTrace archive digits).map (PSTRTMSeq005.leftCfg (b := 26)) ++
  (encodeCopyTrace (sourceLeft archive digits) digits).map (PSTRTMSeq005.rightCfg (a := 42))

def rawCopyFinal (archive digits : List Bool) : MachineState 69 :=
  ⟨69,Turing.Tape.mk₂ (true::sourceLeft archive digits) (PSTRTMUnblockTrace019.rawWord digits ++ [true])⟩

theorem rawCopy_runsFrom (archive digits : List Bool) :
    PSTRTMSeq005.RunsFrom rawCopyMachine ⟨0,Turing.Tape.mk₂ (sourceLeft archive digits) [true]⟩
      (rawCopyTrace archive digits) (rawCopyFinal archive digits) := by
  have h := PSTRTMSeq005.seq_runsFrom copyMachine encodeCopyMachine
    (state 0 (sourceLeft archive digits) [true]) (state 42 (sourceLeft archive digits) (true::workspace digits))
    (encodeCopyFinal (sourceLeft archive digits) digits) (copyTrace archive digits)
    (encodeCopyTrace (sourceLeft archive digits) digits) (copy_runsFrom archive digits)
    (encodeCopy_runsFrom (sourceLeft archive digits) digits)
  exact h

theorem rawCopy_length (archive digits : List Bool) :
    (rawCopyTrace archive digits).length = 5*digits.length^2+31*digits.length+26 := by
  simp only [rawCopyTrace,List.length_append,List.length_map,copy_length,encodeCopy_length]
  ring

theorem rawCopy_time_le (archive digits : List Bool) :
    (rawCopyTrace archive digits).length ≤ 128*(digits.length+1)^2 := by
  rw [rawCopy_length]
  nlinarith

theorem rawCopy_visitedSpace_le (archive digits : List Bool) (inputLength : Nat) :
    visitedSpace rawCopyMachine inputLength (rawCopyTrace archive digits) ≤ inputLength+256*(digits.length+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le rawCopyMachine inputLength (rawCopyTrace archive digits)
  rw [rawCopy_length] at hs
  nlinarith

theorem rawCopy_originalNat_runsFrom (n : Nat) (archive : List Bool) :
    PSTRTMSeq005.RunsFrom rawCopyMachine
      ⟨0,Turing.Tape.mk₂ (sourceLeft archive (PSTRTMNatValue017.rawPayload n)) [true]⟩
      (rawCopyTrace archive (PSTRTMNatValue017.rawPayload n))
      ⟨69,Turing.Tape.mk₂ (true::sourceLeft archive (PSTRTMNatValue017.rawPayload n)) (encodeNat n ++ [true])⟩ := by
  rw [← PA17TMRatArithmeticUnblock004.rawWord_payload]
  exact rawCopy_runsFrom archive (PSTRTMNatValue017.rawPayload n)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006
