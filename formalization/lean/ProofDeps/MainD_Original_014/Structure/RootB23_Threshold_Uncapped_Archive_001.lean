module
public import Common.PSTR_TM_ThresholdDynamicCap_245
public import Common.PSTR_TM_ThresholdRiskReturn_228

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace RootB23.Threshold.Uncapped.BReturn
open PaperProofs.Common.Native.RationalControllerComputation

/-! The first real uncapped-q archive recovery step. A natural Datum tag
is really crossed RIGHT, creating the second near FALSE required by227;
its actual two LEFT moves and105 rewind then return to the archived B.
The scratch raw B and every right suffix cell remain behind that source.
No FALSE guard is assumed to reappear merely because the tag was parsed. -/

def tagTrace (left right : List Bool) : List (MachineState 1) :=
  [⟨0,Turing.Tape.mk₂ left (false::right)⟩,
   ⟨1,Turing.Tape.mk₂ (false::left) right⟩]

theorem tag_runsFrom (left right : List Bool) :
    PSTRTMSeq005.RunsFrom PSTRTMThresholdRiskReturn228.rightMachine
      ⟨0,Turing.Tape.mk₂ left (false::right)⟩ (tagTrace left right)
      ⟨1,Turing.Tape.mk₂ (false::left) right⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [tagTrace,List.isChain_cons_cons,Turing.TM0.step,
      PSTRTMThresholdRiskReturn228.rightMachine,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,PSTRTMThresholdRiskReturn228.rightMachine]

def returnMachine : Machine 8 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdRiskReturn228.rightMachine PSTRTMThresholdBackupReturn227.returnMachine

def returnTrace (archive digits right : List Bool) : List (MachineState 8) :=
  (tagTrace (PA17TMRatArithmeticCopy006.sourceLeft archive digits) right).map
    (PSTRTMSeq005.leftCfg (b := 6)) ++
  (PSTRTMThresholdBackupReturn227.returnTrace archive digits right).map
    (PSTRTMSeq005.rightCfg (a := 1))

def final (archive digits right : List Bool) : MachineState 8 :=
  PSTRTMSeq005.rightCfg (a := 1) (PSTRTMThresholdBackupReturn227.returnFinal archive digits right)

theorem return_runsFrom (archive digits right : List Bool) :
    PSTRTMSeq005.RunsFrom returnMachine
      ⟨0,Turing.Tape.mk₂ (PA17TMRatArithmeticCopy006.sourceLeft archive digits) (false::right)⟩
      (returnTrace archive digits right) (final archive digits right) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMThresholdRiskReturn228.rightMachine
    PSTRTMThresholdBackupReturn227.returnMachine
    ⟨0,Turing.Tape.mk₂ (PA17TMRatArithmeticCopy006.sourceLeft archive digits) (false::right)⟩
    ⟨1,Turing.Tape.mk₂ (false::PA17TMRatArithmeticCopy006.sourceLeft archive digits) right⟩
    (PSTRTMThresholdBackupReturn227.returnFinal archive digits right)
    (tagTrace (PA17TMRatArithmeticCopy006.sourceLeft archive digits) right)
    (PSTRTMThresholdBackupReturn227.returnTrace archive digits right) (tag_runsFrom _ _)
  exact PSTRTMThresholdBackupReturn227.return_runsFrom archive digits right

theorem final_tape (archive digits right : List Bool) :
    (final archive digits right).Tape = Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks digits++false::false::right) := rfl

theorem return_length (archive digits right : List Bool) :
    (returnTrace archive digits right).length = 2*digits.length+8 := by
  simp only [returnTrace,List.length_append,List.length_map,tagTrace,List.length_cons,List.length_nil,
    PSTRTMThresholdBackupReturn227.return_length]
  omega

end RootB23.Threshold.Uncapped.BReturn

namespace RootB23.Threshold.Uncapped.Source
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBBackupEntry188

/-! A branch-specific original[q,1] caller begins actual uncapped q
recovery. The B work Datum is crossed and its archived source is really
rewound. q itself remains in its actual original NUM/DEN archive; it is
NOT yet reconstructed or returned as a rational Datum. -/

def locatorMachine : Machine 1374 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdDynamicCap245.dynamicMachine RootB23.Threshold.Uncapped.BReturn.returnMachine

def digits (q : Rat) : List Bool := PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB q 1)

def sourceRight (q : Rat) : List Bool :=
  PSTRTMIncrement009.blocks (digits q)++false::false::encodeNat (PaperProofs.Statistics.controllerB q 1)

def final (q : Rat) : MachineState 1374 := PSTRTMSeq005.rightCfg (a := 1365)
  (RootB23.Threshold.Uncapped.BReturn.final (sourceArchive q 1) (digits q)
    (encodeNat (PaperProofs.Statistics.controllerB q 1)))

theorem final_tape (q : Rat) : (final q).Tape =
    Turing.Tape.mk₂ (false::sourceArchive q 1) (sourceRight q) := rfl

theorem archive_entry (q : Rat) : false::sourceArchive q 1 =
    List.replicate (2*(result q 1).gap+2) false++
      (PSTRTMRawNat010.leftBlocks (result q 1).depth.reverse++false::PSTRTMThresholdDepthSource184.riskArchive q) := by
  have reserve : List.replicate (2*(result q 1).gap+2) false =
      false::false::PSTRTMThresholdCounterSeek169.gaps (result q 1).gap := by
    rw [PSTRTMThresholdCounterSeek169.gaps_replicate]
    rw [show 2*(result q 1).gap+2 = 2+2*(result q 1).gap by omega,List.replicate_add]
    rfl
  simp only [reserve,sourceArchive,List.cons_append]

private theorem clock_bound (input width earlier : Nat)
    (hw : width ≤ input+4) (ht : earlier ≤ 67108864*(input+2)^3) :
    earlier+(2*width+8) ≤ 100663296*(input+2)^3 := by
  have hs : 1 ≤ input+2 := by omega
  have hc := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hc
  omega

private theorem scale_cube (input : Nat) : input+1 ≤ (input+2)^3 := by
  have hs : 1 ≤ input+2 := by omega
  have hc := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hc
  omega

theorem original_uncap_source_contract (q : Rat) (hq : 0 < q) (uncapped : q < 1/4) :
    ∃ trace,
      Runs locatorMachine (encode [.rational q,.natural 1]) trace (final q) ∧
      trace.length ≤ 100663296*((encode [.rational q,.natural 1]).length+2)^3 ∧
      ∀ clock, visitedSpace locatorMachine (encode [.rational q,.natural 1]).length (trace.take clock) ≤
        402653184*((encode [.rational q,.natural 1]).length+2)^3 := by
  obtain ⟨front,actual,time,_space⟩ := PSTRTMThresholdDynamicCap245.original_dynamicCap_contract q hq
  let part := RootB23.Threshold.Uncapped.BReturn.returnTrace (sourceArchive q 1) (digits q)
    (encodeNat (PaperProofs.Statistics.controllerB q 1))
  have callee : PSTRTMSeq005.RunsFrom RootB23.Threshold.Uncapped.BReturn.returnMachine
      ⟨0,(PSTRTMThresholdDynamicCap245.final q).Tape⟩ part
      (RootB23.Threshold.Uncapped.BReturn.final (sourceArchive q 1) (digits q)
        (encodeNat (PaperProofs.Statistics.controllerB q 1))) := by
    rw [PSTRTMThresholdDynamicCap245.final_tape q hq]
    simp only [not_le.mpr uncapped,ite_false,encodeDatum]
    exact RootB23.Threshold.Uncapped.BReturn.return_runsFrom _ _ _
  let trace := front.map (PSTRTMSeq005.leftCfg (b := 8)) ++
    part.map (PSTRTMSeq005.rightCfg (a := 1365))
  have actualRun : Runs locatorMachine (encode [.rational q,.natural 1]) trace (final q) := by
    apply PSTRTMSeq005.seq_runs PSTRTMThresholdDynamicCap245.dynamicMachine
      RootB23.Threshold.Uncapped.BReturn.returnMachine (encode [.rational q,.natural 1])
      (PSTRTMThresholdDynamicCap245.final q)
      (RootB23.Threshold.Uncapped.BReturn.final (sourceArchive q 1) (digits q)
        (encodeNat (PaperProofs.Statistics.controllerB q 1))) front part actual callee
  have actualTime : trace.length ≤ 100663296*((encode [.rational q,.natural 1]).length+2)^3 := by
    have hw := PSTRTMThresholdBBackupCost189.controllerB_bits_le q 1 hq (by decide)
    have width : (digits q).length ≤ (encode [.rational q,.natural 1]).length+4 := by
      simpa only [digits,PSTRTMNatValue017.rawPayload,List.length_ofFn] using hw
    have count : part.length = 2*(digits q).length+8 := RootB23.Threshold.Uncapped.BReturn.return_length _ _ _
    simp only [trace,List.length_append,List.length_map,count]
    exact clock_bound _ _ _ width time
  refine ⟨trace,actualRun,actualTime,?_⟩
  intro clock
  have hs := PSTRTMTrace002.visitedSpace_le locatorMachine (encode [.rational q,.natural 1]).length (trace.take clock)
  have hl : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hc := scale_cube (encode [.rational q,.natural 1]).length
  omega

end RootB23.Threshold.Uncapped.Source
