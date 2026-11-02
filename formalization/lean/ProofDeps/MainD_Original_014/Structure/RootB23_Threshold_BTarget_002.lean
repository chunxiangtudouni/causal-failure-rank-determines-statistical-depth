module
public import Structure.RootB23_Threshold_NatSplice_001
public import Common.PSTR_TM_ThresholdTargetDatum_222
public import Common.PSTR_TM_ThresholdBackupReturn_227

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.BTarget
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def targetTail (risk : Rat) (depth : ℕ) : List Bool :=
  false::(encodeNat 1++encodeNat (4*(PaperProofs.Statistics.controllerB risk depth+1)))

theorem target_true (risk : Rat) (depth : ℕ) :
    encodeDatum (.rational (PaperProofs.Statistics.controllerTarget risk depth))=true::targetTail risk depth := by
  rw [PSTRTMThresholdDenominatorRaw202.target_datum_bits]
  rfl

def fields (risk : Rat) (depth : ℕ) : List Bool :=
  encodeDatum (.natural (PaperProofs.Statistics.controllerB risk depth))++
    encodeDatum (.rational (PaperProofs.Statistics.controllerTarget risk depth))

/-- Consume the actual archived B after222, then splice it before the
ACTUAL target, preserving source risk/depth on the whole Tape. -/
def tailMachine : Machine 45 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdBackupReturn227.returnMachine NatSplice.spliceMachine

theorem tail_bounded (risk : Rat) (depth : ℕ) :
    BoundedRun tailMachine (PSTRTMThresholdTargetDatum222.targetFinal risk depth).Tape 45
      (Tape.mk₂ (false::PSTRTMThresholdBBackupEntry188.sourceArchive risk depth) (fields risk depth))
      (128*(natBits (PaperProofs.Statistics.controllerB risk depth)+1)^2) := by
  let n:=PaperProofs.Statistics.controllerB risk depth
  let digits:=PSTRTMNatValue017.rawPayload n
  let archive:=PSTRTMThresholdBBackupEntry188.sourceArchive risk depth
  have entry : (PSTRTMThresholdTargetDatum222.targetFinal risk depth).Tape=
      Tape.mk₂ (false::false::PSTRTMThresholdBackupReturn227.sourceLeft archive digits)
        (true::targetTail risk depth) := by
    rw [PSTRTMThresholdTargetDatum222.target_final_tape,target_true]
    rfl
  have returned : BoundedRun PSTRTMThresholdBackupReturn227.returnMachine
      (PSTRTMThresholdTargetDatum222.targetFinal risk depth).Tape 6
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++false::false::true::targetTail risk depth))
      (2*digits.length+6) := by
    refine ⟨PSTRTMThresholdBackupReturn227.returnTrace archive digits (true::targetTail risk depth),?_,?_⟩
    · rw [entry]
      exact PSTRTMThresholdBackupReturn227.return_runsFrom archive digits (true::targetTail risk depth)
    · rw [PSTRTMThresholdBackupReturn227.return_length]
  have spliced:=NatSplice.splice_bounded n (false::archive) (targetTail risk depth)
  have actual:=returned.seq spliced
  have width : digits.length=natBits n := by simp only [digits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have cost : (2*digits.length+6)+64*(natBits n+1)^2 ≤ 128*(natBits n+1)^2 := by
    rw [width]
    nlinarith [Nat.zero_le ((natBits n)^2)]
  have result:=actual.mono cost
  rw [←target_true] at result
  exact result

/-- Fixed1975 labels, independent of risk/depth. This is the first TWO
contiguous original fields, not the complete original FIVE-Datum target. -/
def machine : Machine 1974 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdTargetDatum222.targetMachine tailMachine

private theorem joined_time (input depth width first later : ℕ) (hd : 1 ≤ depth)
    (firstBound : first ≤ 100663296*(input+depth+1)^3)
    (laterBound : later ≤ 128*(width+1)^2) (widthBound : width ≤ input+4) :
    first+later ≤ 134217728*(input+depth+1)^3 := by
  let scale:=input+depth+1
  have positive : 1 ≤ scale := by dsimp only [scale];omega
  have width : width+1 ≤ 5*scale := by dsimp only [scale];omega
  have square:=Nat.pow_le_pow_left width 2
  have cost : later ≤ 3200*scale^2 := by nlinarith
  have cube : scale^2 ≤ scale^3 := Nat.pow_le_pow_right positive (by decide : 2 ≤ 3)
  have laterCube:=cost.trans (Nat.mul_le_mul_left 3200 cube)
  change first+later ≤ 134217728*scale^3
  have firstCube : first ≤ 100663296*scale^3 := firstBound
  omega

theorem original_two_fields_actual (risk : Rat) (depth : ℕ) (hr : 0<risk) (hd : 1 ≤ depth) :
    ∃ trace final, Runs machine (encode [.rational risk,.natural depth]) trace final ∧
      final.Tape=Tape.mk₂ (false::PSTRTMThresholdBBackupEntry188.sourceArchive risk depth) (fields risk depth) ∧
      trace.length ≤ 134217728*((encode [.rational risk,.natural depth]).length+depth+1)^3 ∧
      ∀ clock, visitedSpace machine (encode [.rational risk,.natural depth]).length (trace.take clock) ≤ 
        536870912*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  obtain ⟨front,first,firstTime,_firstSpace⟩:=
    PSTRTMThresholdTargetDatum222.original_targetDatum_contract risk depth hr hd
  obtain ⟨part,callee,calleeTime⟩:=tail_bounded risk depth
  let final : MachineState 1974 := PSTRTMSeq005.rightCfg (a:=1928)
    (⟨45,Tape.mk₂ (false::PSTRTMThresholdBBackupEntry188.sourceArchive risk depth) (fields risk depth)⟩ : MachineState 45)
  let trace:=(front.map (PSTRTMSeq005.leftCfg (b:=45)))++part.map (PSTRTMSeq005.rightCfg (a:=1928))
  have actual : Runs machine (encode [.rational risk,.natural depth]) trace final :=
    PSTRTMSeq005.seq_runs PSTRTMThresholdTargetDatum222.targetMachine tailMachine
      (encode [.rational risk,.natural depth]) (PSTRTMThresholdTargetDatum222.targetFinal risk depth)
      ⟨45,Tape.mk₂ (false::PSTRTMThresholdBBackupEntry188.sourceArchive risk depth) (fields risk depth)⟩
      front part first callee
  have time : trace.length ≤ 134217728*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
    have width:=PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
    simp only [trace,List.length_append,List.length_map]
    exact joined_time _ _ _ _ _ hd firstTime calleeTime width
  refine ⟨trace,final,actual,rfl,time,?_⟩
  intro clock
  have space:=PSTRTMTrace002.visitedSpace_le machine (encode [.rational risk,.natural depth]).length (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  have scale : (encode [.rational risk,.natural depth]).length+1 ≤ 
      ((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
    have positive : 1 ≤ (encode [.rational risk,.natural depth]).length+depth+1 := by omega
    have power:=Nat.pow_le_pow_right positive (by decide : 1 ≤ 3)
    simp only [pow_one] at power
    omega
  omega

end RootB23.Threshold.BTarget
