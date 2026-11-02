module
public import Common.PSTR_TM_ThresholdRiskReturn_228

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBadSource229
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBadFactor226 PSTRTMThresholdBackupReturn227

/-! An actual ORIGINAL-input caller, not an assumed resident frame.
The retained B is under the head and the newly computed bad-risk integer
factor remains to the right beyond TWO real FALSE separator cells. All
source risk/cleared gap/exhausted DEPTH cells remain in sourceArchive. -/

def sourceMachine : Machine 1337 := PSTRTMSeq005.seqMachine factorMachine returnMachine

def sourceTrace (risk : Rat) (depth : Nat) : List (MachineState 1337) :=
  (factorTrace risk depth).map (PSTRTMSeq005.leftCfg (b := 6)) ++
    (returnTrace (PSTRTMThresholdBBackupEntry188.sourceArchive risk depth)
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (factor risk depth)))).map
      (PSTRTMSeq005.rightCfg (a := 1330))

def sourceFinal (risk : Rat) (depth : Nat) : MachineState 1337 :=
  PSTRTMSeq005.rightCfg (a := 1330)
    (returnFinal (PSTRTMThresholdBBackupEntry188.sourceArchive risk depth)
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (factor risk depth))))

theorem source_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    Runs sourceMachine (encode [.rational risk,.natural depth])
      (sourceTrace risk depth) (sourceFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs factorMachine returnMachine
    (encode [.rational risk,.natural depth]) (factorFinal risk depth)
    (returnFinal (PSTRTMThresholdBBackupEntry188.sourceArchive risk depth)
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (factor risk depth))))
    (factorTrace risk depth)
    (returnTrace (PSTRTMThresholdBBackupEntry188.sourceArchive risk depth)
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (factor risk depth))))
    (factor_runs risk depth hr hd)
  rw [original_factor_entry]
  exact return_runsFrom _ _ _

def sourceRight (risk : Rat) (depth : Nat) : List Bool :=
  PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)) ++
    false::false::PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (factor risk depth))

theorem source_final_tape (risk : Rat) (depth : Nat) :
    (sourceFinal risk depth).Tape = Turing.Tape.mk₂
      (false::PSTRTMThresholdBBackupEntry188.sourceArchive risk depth) (sourceRight risk depth) := rfl

theorem source_time_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (sourceTrace risk depth).length ≤
      67108864*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have ht := factor_time_le risk depth hr hd
  have hrtn := return_length (PSTRTMThresholdBBackupEntry188.sourceArchive risk depth)
    (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))
    (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (factor risk depth)))
  have hraw (value : Nat) : (PSTRTMNatValue017.rawPayload value).length = natBits value := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  rw [hraw] at hrtn
  have hb := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  have hc : (encode [.rational risk,.natural depth]).length+1 ≤
      ((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
    have hp : 1 ≤ (encode [.rational risk,.natural depth]).length+depth+1 := by omega
    have he := Nat.pow_le_pow_right hp (by decide : 1 ≤ 3)
    simp only [pow_one] at he
    omega
  simp only [sourceTrace,List.length_append,List.length_map]
  omega

theorem source_prefix_space_le (risk : Rat) (depth clock : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    visitedSpace sourceMachine (encode [.rational risk,.natural depth]).length
      ((sourceTrace risk depth).take clock) ≤
      268435456*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have ht := source_time_le risk depth hr hd
  have hs := PSTRTMTrace002.visitedSpace_le sourceMachine
    (encode [.rational risk,.natural depth]).length ((sourceTrace risk depth).take clock)
  have hl : ((sourceTrace risk depth).take clock).length ≤ (sourceTrace risk depth).length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hc : (encode [.rational risk,.natural depth]).length+1 ≤
      ((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
    have hp : 1 ≤ (encode [.rational risk,.natural depth]).length+depth+1 := by omega
    have he := Nat.pow_le_pow_right hp (by decide : 1 ≤ 3)
    simp only [pow_one] at he
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBadSource229
