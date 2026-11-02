module
public import Common.PSTR_TM_ThresholdBBackup_192

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBBackupBound193
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBBackup192

private theorem scale_cube (input depth : Nat) : input + 1 ≤ (input + depth + 1)^3 := by
  have hp : 1 ≤ input + depth + 1 := by omega
  have hp2 : input + depth + 1 ≤ (input + depth + 1)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (input + depth + 1) hp
  have hp3 : (input + depth + 1)^2 ≤ (input + depth + 1)^3 :=
    Nat.pow_le_pow_right hp (by decide : 2 ≤ 3)
  omega

private theorem arithmetic_time (input depth width main copy : Nat)
    (hm : main ≤ 4194304*(input + depth + 1)^3)
    (hc : copy ≤ 128*(width + 1)^2) (hw : width ≤ input + 4) :
    main + copy ≤ 8388608*(input + depth + 1)^3 := by
  let scale := input + depth + 1
  have hp : 1 ≤ scale := by dsimp only [scale]; omega
  have hwidth : width + 1 ≤ 5*scale := by dsimp only [scale]; omega
  have hw2 := Nat.pow_le_pow_left hwidth 2
  have hc2 : copy ≤ 3200*scale^2 := by nlinarith
  have hp3 : scale^2 ≤ scale^3 := Nat.pow_le_pow_right hp (by decide : 2 ≤ 3)
  have hc3 := hc2.trans (Nat.mul_le_mul_left 3200 hp3)
  change main + copy ≤ 8388608*scale^3
  have hm' : main ≤ 4194304*scale^3 := hm
  omega

theorem backup_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (backupTrace risk depth).length ≤
      8388608*((encode [.rational risk,.natural depth]).length + depth + 1)^3 := by
  have hm := PSTRTMThresholdBBackupCost189.entry_length_le risk depth hr hd
  have hc := PA17TMRatArithmeticCopy006.rawCopy_time_le
    (PSTRTMThresholdBBackupEntry188.sourceArchive risk depth)
    (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))
  have hl : (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)).length =
      natBits (PaperProofs.Statistics.controllerB risk depth) := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  rw [hl] at hc
  have hw := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  simp only [backupTrace,List.length_append,List.length_map]
  exact arithmetic_time _ _ _ _ _ hm hc hw

theorem backup_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    visitedSpace backupMachine (encode [.rational risk,.natural depth]).length (backupTrace risk depth) ≤
      33554432*((encode [.rational risk,.natural depth]).length + depth + 1)^3 := by
  have ht := backup_length_le risk depth hr hd
  have hs := PSTRTMTrace002.visitedSpace_le backupMachine
    (encode [.rational risk,.natural depth]).length (backupTrace risk depth)
  have hp := scale_cube (encode [.rational risk,.natural depth]).length depth
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBBackupBound193
