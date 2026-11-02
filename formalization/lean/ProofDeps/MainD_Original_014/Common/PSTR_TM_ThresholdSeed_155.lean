module
public import Common.PSTR_TM_ThresholdPairCopies_154
public import Common.PSTR_TM_ThresholdB1Prepared_153
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdSeed155
open PaperProofs.Common.Native.RationalControllerComputation

theorem numerator_pos (risk : Rat) (hr : 0 < risk) : 0 < risk.num.natAbs :=
  Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hr))

theorem positive_ratio (risk : Rat) (hr : 0 < risk) :
    risk=(risk.num.natAbs : Rat)/risk.den := by
  have hn : 0 < risk.num := Rat.num_pos.mpr hr
  have ha : (risk.num.natAbs : Int)=risk.num := Int.natAbs_of_nonneg hn.le
  have hc : (risk.num.natAbs : Rat)=(risk.num : Rat) := by
    simpa only [Int.cast_natCast] using congrArg (fun value : Int => (value : Rat)) ha
  calc
    risk=(risk.num : Rat)/risk.den := (Rat.num_div_den risk).symm
    _=(risk.num.natAbs : Rat)/risk.den := by rw [hc]

/-- Fixed802 labels, original two-Datum input, real source backup,
real whole-tape framing, and genuine B1 evaluation. This is the seed at
index ONE, with original depth retained; it is not the depth recurrence
or the five-Datum original threshold output. -/
def seedMachine : Machine 801 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdPairCopies154.copiesMachine PSTRTMThresholdB1Prepared153.preparedMachine

def seedTrace (risk : Rat) (depth : Nat) : List (MachineState 801) :=
  (PSTRTMThresholdPairCopies154.copiesTrace risk depth).map (PSTRTMSeq005.leftCfg (b:=316)) ++
    (PSTRTMThresholdB1Prepared153.preparedTrace [] risk.num.natAbs risk.den
      (PSTRTMThresholdBackup139.depthDigits depth)).map (PSTRTMSeq005.rightCfg (a:=484))

def seedFinal (risk : Rat) (depth : Nat) : MachineState 801 :=
  PSTRTMSeq005.rightCfg (a:=484)
    (PSTRTMThresholdB1Prepared153.preparedFinal [] risk.num.natAbs risk.den
      (PSTRTMThresholdBackup139.depthDigits depth))

def retainedArchive (risk : Rat) (depth : Nat) : List Bool :=
  PSTRTMThresholdB1Prepared153.retainedArchive [] risk.num.natAbs risk.den
    (PSTRTMThresholdBackup139.depthDigits depth)

theorem seed_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    Runs seedMachine (encode [.rational risk,.natural depth]) (seedTrace risk depth) (seedFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs PSTRTMThresholdPairCopies154.copiesMachine PSTRTMThresholdB1Prepared153.preparedMachine
    (encode [.rational risk,.natural depth]) (PSTRTMThresholdPairCopies154.copiesFinal risk depth)
    (PSTRTMThresholdB1Prepared153.preparedFinal [] risk.num.natAbs risk.den (PSTRTMThresholdBackup139.depthDigits depth))
    (PSTRTMThresholdPairCopies154.copiesTrace risk depth)
    (PSTRTMThresholdB1Prepared153.preparedTrace [] risk.num.natAbs risk.den (PSTRTMThresholdBackup139.depthDigits depth))
    (PSTRTMThresholdPairCopies154.copies_runs risk depth hr)
  exact PSTRTMThresholdB1Prepared153.prepared_runsFrom [] _ _ _ (numerator_pos risk hr)

theorem seed_final_tape (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    (seedFinal risk depth).Tape=Turing.Tape.mk₂
      (List.replicate (4*PSTRTMB1RunFrame122.width risk.num.natAbs risk.den+5) false++retainedArchive risk depth)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk 1))) := by
  have hb : PaperProofs.Statistics.controllerB risk 1=PSTRTMB1Value068.exponent risk.num.natAbs risk.den := by
    conv_lhs => rw [positive_ratio risk hr]
    exact PSTRTMB1Value068.controllerB_one_ratio _ _
  rw [hb]
  exact PSTRTMThresholdB1Prepared153.prepared_final_tape [] _ _ _

private theorem arithmetic_length_bound (input width first second : Nat)
    (hf : first≤16384*(input+1)^2) (hs : second≤1024*(width+1)^2) (hw : width ≤ input+1) :
    first+second≤32768*(input+1)^2 := by
  have h : width+1≤2*(input+1) := by omega
  have h2 := Nat.pow_le_pow_left h 2
  nlinarith

theorem seed_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    (seedTrace risk depth).length≤32768*((encode [.rational risk,.natural depth]).length+1)^2 := by
  have hf := PSTRTMThresholdPairCopies154.copies_length_le risk depth hr
  have hs := PSTRTMThresholdB1Prepared153.prepared_length_le [] risk.num.natAbs risk.den
    (PSTRTMThresholdBackup139.depthDigits depth) (numerator_pos risk hr)
  have hw := PSTRTMThresholdRisk114.original_widths_le risk depth hr
  simp only [seedTrace,List.length_append,List.length_map]
  exact arithmetic_length_bound _ _ _ _ hf hs hw

private theorem arithmetic_space_bound (input time space : Nat)
    (ht : time≤32768*(input+1)^2) (hs : space ≤ input+2*time+1) :
    space≤131072*(input+1)^2 := by nlinarith

theorem seed_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    visitedSpace seedMachine (encode [.rational risk,.natural depth]).length (seedTrace risk depth)≤
      131072*((encode [.rational risk,.natural depth]).length+1)^2 :=
  arithmetic_space_bound _ _ _ (seed_length_le risk depth hr)
    (PSTRTMTrace002.visitedSpace_le seedMachine (encode [.rational risk,.natural depth]).length (seedTrace risk depth))

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdSeed155
