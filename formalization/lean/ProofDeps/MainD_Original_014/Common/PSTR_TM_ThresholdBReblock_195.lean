module
public import Common.PSTR_TM_ThresholdBBackupBound_193
public import Common.PSTR_TM_ReblockFrame_194

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBReblock195
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMReblockFrame194 PA17TMRatArithmeticParse002

def parseMachine : Machine 24 := PSTRTMSeq005.seqMachine streamMachine clearRewindMachine

def parseTrace (left digits : List Bool) : List (MachineState 24) :=
  (streamTrace (false::left) [] digits [true]).map (PSTRTMSeq005.leftCfg (b := 6)) ++
    (clearRewindTrace left digits).map (PSTRTMSeq005.rightCfg (a := 17))

def parseFinal (left digits : List Bool) : MachineState 24 :=
  PSTRTMSeq005.rightCfg (a := 17) (clearRewindFinal left digits)

theorem parse_runsFrom (left digits : List Bool) :
    PSTRTMSeq005.RunsFrom parseMachine
      ⟨0,(streamInitial (false::left) digits [true]).Tape⟩ (parseTrace left digits) (parseFinal left digits) := by
  apply PSTRTMSeq005.seq_runsFrom streamMachine clearRewindMachine
    (streamInitial (false::left) digits [true]) (streamFinal (false::left) digits [true])
    (clearRewindFinal left digits) (streamTrace (false::left) [] digits [true])
    (clearRewindTrace left digits) (stream_runsFrom _ _ _)
  exact clearRewind_runsFrom left digits

/-- Only the known TRUE footer is changed. Stream parsing consumes the
actual width header; clearing its final TRUE and rewinding are real steps.
In particular the adjacent01 cells are NEVER treated as an OWN00 region. -/
def reblockMachine : Machine 28 := PSTRTMSeq005.seqMachine guardMachine parseMachine

def reblockTrace (left digits : List Bool) : List (MachineState 28) :=
  (guardTrace left (rawField digits ++ [true])).map (PSTRTMSeq005.leftCfg (b := 24)) ++
    (parseTrace left digits).map (PSTRTMSeq005.rightCfg (a := 3))

def reblockFinal (left digits : List Bool) : MachineState 28 :=
  PSTRTMSeq005.rightCfg (a := 3) (parseFinal left digits)

theorem reblock_runsFrom (left digits : List Bool) :
    PSTRTMSeq005.RunsFrom reblockMachine
      ⟨0,Turing.Tape.mk₂ (true::left) (rawField digits ++ [true])⟩
      (reblockTrace left digits) (reblockFinal left digits) := by
  apply PSTRTMSeq005.seq_runsFrom guardMachine parseMachine
    ⟨0,Turing.Tape.mk₂ (true::left) (rawField digits ++ [true])⟩
    ⟨3,Turing.Tape.mk₂ (false::left) (rawField digits ++ [true])⟩
    (parseFinal left digits) (guardTrace left (rawField digits ++ [true]))
    (parseTrace left digits) (guard_runsFrom _ _) (parse_runsFrom _ _)

theorem reblock_final_tape (left digits : List Bool) :
    (reblockFinal left digits).Tape = Turing.Tape.mk₂ (false::left)
      (PSTRTMIncrement009.blocks digits ++ [false,false]) := rfl

private theorem blank_two (bits : List Bool) :
    Turing.ListBlank.mk (bits ++ [false,false]) = Turing.ListBlank.mk bits := by
  calc
    Turing.ListBlank.mk (bits ++ [false,false]) =
        Turing.ListBlank.mk ((bits ++ [false]) ++ [false]) := by rw [List.append_assoc]; rfl
    _ = Turing.ListBlank.mk (bits ++ [false]) := PSTRTMRawNat010.blank_append_false _
    _ = Turing.ListBlank.mk bits := PSTRTMRawNat010.blank_append_false _

theorem reblock_final_blank (left digits : List Bool) :
    (reblockFinal left digits).Tape = Turing.Tape.mk₂ (false::left)
      (PSTRTMIncrement009.blocks digits) := by
  rw [reblock_final_tape]
  simp only [Turing.Tape.mk₂,blank_two]

theorem reblock_length (left digits : List Bool) :
    (reblockTrace left digits).length = digits.length^2 + 11*digits.length + 12 := by
  simp only [reblockTrace,parseTrace,List.length_append,List.length_map,
    streamTrace_length,clearRewind_length,guardTrace,List.length_cons,List.length_nil]
  omega

open PSTRTMThresholdBBackupEntry188 PA17TMRatArithmeticCopy006

def savedLeft (risk : Rat) (depth : Nat) : List Bool :=
  sourceLeft (sourceArchive risk depth)
    (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))

/-- Fixed1292 labels: original risk/depth to two physical canonical B
fields. One B remains archived, the fresh B is under the actual head,
and its right side is blank only AFTER real footer erasure. -/
def savedMachine : Machine 1291 :=
  PSTRTMSeq005.seqMachine PSTRTMThresholdBBackup192.backupMachine reblockMachine

def savedTrace (risk : Rat) (depth : Nat) : List (MachineState 1291) :=
  (PSTRTMThresholdBBackup192.backupTrace risk depth).map (PSTRTMSeq005.leftCfg (b := 28)) ++
    (reblockTrace (savedLeft risk depth)
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))).map
      (PSTRTMSeq005.rightCfg (a := 1262))

def savedFinal (risk : Rat) (depth : Nat) : MachineState 1291 :=
  PSTRTMSeq005.rightCfg (a := 1262) (reblockFinal (savedLeft risk depth)
    (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)))

theorem saved_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    Runs savedMachine (encode [.rational risk,.natural depth])
      (savedTrace risk depth) (savedFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs PSTRTMThresholdBBackup192.backupMachine reblockMachine
    (encode [.rational risk,.natural depth]) (PSTRTMThresholdBBackup192.backupFinal risk depth)
    (reblockFinal (savedLeft risk depth)
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)))
    (PSTRTMThresholdBBackup192.backupTrace risk depth)
    (reblockTrace (savedLeft risk depth)
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)))
    (PSTRTMThresholdBBackup192.backup_runs risk depth hr hd)
  rw [PSTRTMThresholdBBackup192.backup_final_tape,encodeNat_rawField]
  exact reblock_runsFrom _ _

theorem saved_final_tape (risk : Rat) (depth : Nat) :
    (savedFinal risk depth).Tape = Turing.Tape.mk₂ (false::savedLeft risk depth)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload
        (PaperProofs.Statistics.controllerB risk depth))) := by
  change (reblockFinal _ _).Tape = _
  exact reblock_final_blank _ _

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBReblock195
