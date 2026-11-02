module
public import Structure.RootB23_Threshold_Uncapped_Archive_001
public import Common.PSTR_TM_ThresholdRiskReturnBudget_230
public import Common.PSTR_TM_ThresholdRiskMarkers_232

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace RootB23.Threshold.Uncapped.Depth
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBBackupEntry188 PSTRTMThresholdRiskReturn228

/-! Actual uncapped recovery continues across the already cleared gap
and exhausted DEPTH, preserving B and its scratch raw field to the right.
The original TRUE flags delimit depth even when every data bit is FALSE.
The runtime scans those flags, rather than receiving a length parameter. -/

def locatorMachine : Machine 1383 := PSTRTMSeq005.seqMachine
  RootB23.Threshold.Uncapped.Source.locatorMachine depthMachine

def locatorRight (q : Rat) : List Bool := PSTRTMIncrement009.blocks (result q 1).depth++
  List.replicate (2*(result q 1).gap+2) false++RootB23.Threshold.Uncapped.Source.sourceRight q

private theorem clock_bound (input gap earlier main : Nat)
    (hm : main ≤ 100663296*(input+2)^3) (hg : gap ≤ 64*(input+2)^2) (he : earlier ≤ input+1) :
    main+(2*gap+2)+2*earlier+10 ≤ 134217728*(input+2)^3 := by
  have hs : 1 ≤ input+2 := by omega
  have hc : (input+2)^2 ≤ (input+2)^3 := Nat.pow_le_pow_right hs (by decide : 2 ≤ 3)
  have hi := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hi
  have hg' := hg.trans (Nat.mul_le_mul_left 64 hc)
  omega

private theorem scale_cube (input : Nat) : input+1 ≤ (input+2)^3 := by
  have hs : 1 ≤ input+2 := by omega
  have hc := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hc
  omega

theorem original_uncap_depth_contract (q : Rat) (hq : 0 < q) (uncapped : q < 1/4) :
    ∃ trace last,
      Runs locatorMachine (encode [.rational q,.natural 1]) trace last ∧
      last.Tape = Turing.Tape.mk₂ (false::PSTRTMThresholdDepthSource184.riskArchive q) (locatorRight q) ∧
      trace.length ≤ 134217728*((encode [.rational q,.natural 1]).length+2)^3 ∧
      ∀ clock, visitedSpace locatorMachine (encode [.rational q,.natural 1]).length (trace.take clock) ≤
        536870912*((encode [.rational q,.natural 1]).length+2)^3 := by
  obtain ⟨front,actual,time,_space⟩ := RootB23.Threshold.Uncapped.Source.original_uncap_source_contract q hq uncapped
  have nonempty := PSTRTMThresholdRiskReturnBudget230.result_depth_ne_nil q 1 (by decide)
  cases reversed : (result q 1).depth.reverse with
  | nil =>
    have same := congrArg List.reverse reversed
    simp only [List.reverse_reverse,List.reverse_nil] at same
    exact False.elim (nonempty same)
  | cons bit earlier =>
    have restored : (bit::earlier).reverse = (result q 1).depth := by
      rw [←reversed,List.reverse_reverse]
    let gap := 2*(result q 1).gap+2
    let part := depthTrace (PSTRTMThresholdDepthSource184.riskArchive q) bit earlier
      (RootB23.Threshold.Uncapped.Source.sourceRight q) gap
    let trace := front.map (PSTRTMSeq005.leftCfg (b := 8)) ++
      part.map (PSTRTMSeq005.rightCfg (a := 1374))
    let last := PSTRTMSeq005.rightCfg (a := 1374)
      (depthFinal (PSTRTMThresholdDepthSource184.riskArchive q) bit earlier
        (RootB23.Threshold.Uncapped.Source.sourceRight q) gap)
    have actualRun : Runs locatorMachine (encode [.rational q,.natural 1]) trace last := by
      apply PSTRTMSeq005.seq_runs RootB23.Threshold.Uncapped.Source.locatorMachine depthMachine
        (encode [.rational q,.natural 1]) (RootB23.Threshold.Uncapped.Source.final q)
        (depthFinal (PSTRTMThresholdDepthSource184.riskArchive q) bit earlier
          (RootB23.Threshold.Uncapped.Source.sourceRight q) gap) front part actual
      rw [RootB23.Threshold.Uncapped.Source.final_tape,RootB23.Threshold.Uncapped.Source.archive_entry,reversed]
      exact depth_runsFrom _ _ _ _ _
    have output : last.Tape = Turing.Tape.mk₂ (false::PSTRTMThresholdDepthSource184.riskArchive q)
        (locatorRight q) := by
      dsimp only [last,PSTRTMSeq005.rightCfg]
      rw [depth_final_tape,restored]
      rfl
    have actualTime : trace.length ≤ 134217728*((encode [.rational q,.natural 1]).length+2)^3 := by
      have hg := PSTRTMThresholdRiskReturnBudget230.result_gap_le q 1 hq (by decide)
      have hd := PSTRTMThresholdRiskReturnBudget230.result_depth_length q 1 (by decide)
      have hr := congrArg List.length reversed
      simp only [List.length_reverse,List.length_cons] at hr
      have hw := PSTRTMThresholdBackup139.original_width_le q 1 hq
      rw [PSTRTMThresholdDepthSource184.depth_length] at hw
      have earlierBound : earlier.length ≤ (encode [.rational q,.natural 1]).length+1 := by omega
      change (result q 1).gap ≤ 64*((encode [.rational q,.natural 1]).length+2)^2 at hg
      have total := clock_bound (encode [.rational q,.natural 1]).length (result q 1).gap
        earlier.length front.length time hg earlierBound
      simpa only [trace,part,List.length_append,List.length_map,depth_length,gap,Nat.add_assoc] using total
    refine ⟨trace,last,actualRun,output,actualTime,?_⟩
    intro clock
    have hs := PSTRTMTrace002.visitedSpace_le locatorMachine (encode [.rational q,.natural 1]).length (trace.take clock)
    have hl : (trace.take clock).length ≤ trace.length := by
      simp only [List.length_take]
      exact Nat.min_le_right _ _
    have hc := scale_cube (encode [.rational q,.natural 1]).length
    omega

end RootB23.Threshold.Uncapped.Depth

namespace RootB23.Threshold.Uncapped.Numerator
open PaperProofs.Common.Native.RationalControllerComputation
open RootB23.Threshold.Uncapped.Depth PSTRTMThresholdRiskMarkers232

/-! The uncapped q source is physically reached through BOTH original
0010 markers. The q NUM/DEN, exhausted depth, cleared gap and both B
fields stay literal on the same tape. This is the source for real q
serialization, not an assertion that q was already re-encoded for free. -/

def sourceMachine : Machine 1401 := PSTRTMSeq005.seqMachine locatorMachine riskFieldsMachine

def sourceRight (q : Rat) : List Bool :=
  PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload q.num.natAbs)++markerTail
    (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload q.den)++markerTail (locatorRight q))

private theorem clock_bound (input width main : Nat)
    (hm : main ≤ 134217728*(input+2)^3) (hw : width ≤ input+1) :
    main+2*width+16 ≤ 167772160*(input+2)^3 := by
  have hs : 1 ≤ input+2 := by omega
  have hc := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hc
  omega

private theorem scale_cube (input : Nat) : input+1 ≤ (input+2)^3 := by
  have hs : 1 ≤ input+2 := by omega
  have hc := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hc
  omega

theorem original_uncap_numerator_contract (q : Rat) (hq : 0 < q) (uncapped : q < 1/4) :
    ∃ trace last,
      Runs sourceMachine (encode [.rational q,.natural 1]) trace last ∧
      last.Tape = Turing.Tape.mk₂ [false] (sourceRight q) ∧
      trace.length ≤ 167772160*((encode [.rational q,.natural 1]).length+2)^3 ∧
      ∀ clock, visitedSpace sourceMachine (encode [.rational q,.natural 1]).length (trace.take clock) ≤
        671088640*((encode [.rational q,.natural 1]).length+2)^3 := by
  obtain ⟨front,before,actual,output,time,_space⟩ := original_uncap_depth_contract q hq uncapped
  let numerator := PSTRTMNatValue017.rawPayload q.num.natAbs
  let denominator := PSTRTMNatValue017.rawPayload q.den
  let part := riskFieldsTrace [] numerator denominator (locatorRight q)
  let trace := front.map (PSTRTMSeq005.leftCfg (b := 17)) ++
    part.map (PSTRTMSeq005.rightCfg (a := 1383))
  let last := PSTRTMSeq005.rightCfg (a := 1383) (riskFieldsFinal [] numerator denominator (locatorRight q))
  have actualRun : Runs sourceMachine (encode [.rational q,.natural 1]) trace last := by
    apply PSTRTMSeq005.seq_runs locatorMachine riskFieldsMachine (encode [.rational q,.natural 1]) before
      (riskFieldsFinal [] numerator denominator (locatorRight q)) front part actual
    rw [output]
    exact riskFields_runsFrom [] numerator denominator (locatorRight q)
  have finalTape : last.Tape = Turing.Tape.mk₂ [false] (sourceRight q) := by
    dsimp only [last,PSTRTMSeq005.rightCfg]
    rw [riskFields_final_tape]
    rfl
  have actualTime : trace.length ≤ 167772160*((encode [.rational q,.natural 1]).length+2)^3 := by
    have widths := PSTRTMThresholdRisk114.original_widths_le q 1 hq
    have rawWidth : numerator.length+denominator.length ≤ (encode [.rational q,.natural 1]).length+1 := by
      simpa only [numerator,denominator,PSTRTMNatValue017.rawPayload,List.length_ofFn] using widths
    have total := clock_bound (encode [.rational q,.natural 1]).length
      (numerator.length+denominator.length) front.length time rawWidth
    simpa only [trace,part,List.length_append,List.length_map,riskFields_length,Nat.add_assoc] using total
  refine ⟨trace,last,actualRun,finalTape,actualTime,?_⟩
  intro clock
  have hs := PSTRTMTrace002.visitedSpace_le sourceMachine (encode [.rational q,.natural 1]).length (trace.take clock)
  have hl : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hc := scale_cube (encode [.rational q,.natural 1]).length
  omega

end RootB23.Threshold.Uncapped.Numerator
