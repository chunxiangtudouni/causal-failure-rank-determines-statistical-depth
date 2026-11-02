module
public import Common.PSTR_TM_ThresholdBBackupCost_189
public import Structure.PA17_TM_RatArithmetic_Copy_006f

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBBackup192
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBBackupEntry188 PA17TMRatArithmeticCopy006

/-- The actual footer prepared by188 is exactly the existing frozen
nearest-field copy entry. Its right side is genuinely blank after TRUE. -/
theorem entry_copy_input (risk : Rat) (depth : Nat) :
    (entryFinal risk depth).Tape = Turing.Tape.mk₂
      (sourceLeft (sourceArchive risk depth)
        (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))) [true] := rfl

/-- Fixed1263 labels: original risk/depth evaluation, real footer
preparation, and the frozen70-label preserving source copy/codec.
The result has a genuine TRUE end marker for the next parser/caller;
the original canonical flagged B remains in its actual left archive. -/
def backupMachine : Machine 1262 := PSTRTMSeq005.seqMachine entryMachine rawCopyMachine

def backupTrace (risk : Rat) (depth : Nat) : List (MachineState 1262) :=
  (entryTrace risk depth).map (PSTRTMSeq005.leftCfg (b := 69)) ++
    (rawCopyTrace (sourceArchive risk depth)
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))).map
      (PSTRTMSeq005.rightCfg (a := 1192))

def backupFinal (risk : Rat) (depth : Nat) : MachineState 1262 :=
  PSTRTMSeq005.rightCfg (a := 1192) (b := 69)
    ⟨69,Turing.Tape.mk₂
      (true :: sourceLeft (sourceArchive risk depth)
        (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)))
      (encodeNat (PaperProofs.Statistics.controllerB risk depth) ++ [true])⟩

theorem backup_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    Runs backupMachine (encode [.rational risk,.natural depth])
      (backupTrace risk depth) (backupFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs entryMachine rawCopyMachine
    (encode [.rational risk,.natural depth]) (entryFinal risk depth)
    ⟨69,Turing.Tape.mk₂
      (true :: sourceLeft (sourceArchive risk depth)
        (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)))
      (encodeNat (PaperProofs.Statistics.controllerB risk depth) ++ [true])⟩
    (entryTrace risk depth)
    (rawCopyTrace (sourceArchive risk depth)
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)))
    (entry_runs risk depth hr hd)
  rw [entry_copy_input]
  exact rawCopy_originalNat_runsFrom _ _

theorem backup_final_tape (risk : Rat) (depth : Nat) :
    (backupFinal risk depth).Tape = Turing.Tape.mk₂
      (true :: sourceLeft (sourceArchive risk depth)
        (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)))
      (encodeNat (PaperProofs.Statistics.controllerB risk depth) ++ [true]) := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBBackup192
