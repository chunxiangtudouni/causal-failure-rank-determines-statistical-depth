module
public import Common.PSTR_TM_ThresholdRiskReturnBudget_230

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRiskLocator231
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBadSource229 PSTRTMThresholdRiskReturn228
open PSTRTMThresholdBBackupEntry188 PSTRTMThresholdDepthSource184

/-! Real ORIGINAL input -> retained exhausted DEPTH first digit, with
the original risk still immediately beyond its actual left FALSE guard.
The computed factor and saved B stay to the right. No free head reset,
reloaded risk, supplied gap/width, or blank-right callee is asserted. -/

def locatorMachine : Machine 1346 := PSTRTMSeq005.seqMachine sourceMachine depthMachine

def locatorRight (risk : Rat) (depth : Nat) : List Bool :=
  PSTRTMIncrement009.blocks (result risk depth).depth ++
    List.replicate (2*(result risk depth).gap+2) false++sourceRight risk depth

theorem locator_entry (risk : Rat) (depth : Nat) :
    (sourceFinal risk depth).Tape = Turing.Tape.mk₂
      (List.replicate (2*(result risk depth).gap+2) false++
        (PSTRTMRawNat010.leftBlocks (result risk depth).depth.reverse++false::riskArchive risk))
      (sourceRight risk depth) := by
  rw [source_final_tape]
  have hz : List.replicate (2*(result risk depth).gap+2) false =
      false::false::PSTRTMThresholdCounterSeek169.gaps (result risk depth).gap := by
    rw [PSTRTMThresholdCounterSeek169.gaps_replicate]
    rw [show 2*(result risk depth).gap+2 = 2+2*(result risk depth).gap by omega,List.replicate_add]
    rfl
  simp only [hz,sourceArchive,List.cons_append]

private theorem arithmetic_time (input depth gap earlier main : Nat)
    (hm : main ≤ 67108864*(input+depth+1)^3)
    (hg : gap ≤ 64*(input+depth+1)^2) (he : earlier ≤ input+1) :
    main+(2*gap+2)+2*earlier+10 ≤ 100663296*(input+depth+1)^3 := by
  let scale := input+depth+1
  have hs : 1 ≤ scale := by dsimp only [scale]; omega
  have hc : scale^2 ≤ scale^3 := Nat.pow_le_pow_right hs (by decide : 2 ≤ 3)
  have hi : input+1 ≤ scale^3 := by
    have hp := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
    simp only [pow_one] at hp
    dsimp only [scale] at hp ⊢
    omega
  have hg' : gap ≤ 64*scale^3 := hg.trans (Nat.mul_le_mul_left _ hc)
  have he' := he.trans hi
  have hm' : main ≤ 67108864*scale^3 := hm
  change main+(2*gap+2)+2*earlier+10 ≤ 100663296*scale^3
  omega

private theorem scale_cube (input depth : Nat) : input+1 ≤ (input+depth+1)^3 := by
  have hs : 1 ≤ input+depth+1 := by omega
  have hp := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hp
  omega

/-- ONE fixed1347-label program and ONE genuine original-input run,
with the complete literal tape and EVERYprefix original visitedSpace.
The endpoint is an actual field-locator port, not badRisk or Full5. -/
theorem original_locator_contract (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    ∃ trace last, Runs locatorMachine (encode [.rational risk,.natural depth]) trace last ∧
      last.Tape = Turing.Tape.mk₂ (false::riskArchive risk) (locatorRight risk depth) ∧
      trace.length ≤ 100663296*((encode [.rational risk,.natural depth]).length+depth+1)^3 ∧
      ∀ clock, visitedSpace locatorMachine (encode [.rational risk,.natural depth]).length (trace.take clock) ≤
        402653184*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have hn := PSTRTMThresholdRiskReturnBudget230.result_depth_ne_nil risk depth hd
  cases hreversed : (result risk depth).depth.reverse with
  | nil =>
    have he := congrArg List.reverse hreversed
    simp only [List.reverse_reverse,List.reverse_nil] at he
    exact False.elim (hn he)
  | cons bit earlier =>
    have hback : (bit::earlier).reverse = (result risk depth).depth := by
      rw [←hreversed,List.reverse_reverse]
    let gap := 2*(result risk depth).gap+2
    let part := depthTrace (riskArchive risk) bit earlier (sourceRight risk depth) gap
    let trace := (sourceTrace risk depth).map (PSTRTMSeq005.leftCfg (b := 8)) ++
      part.map (PSTRTMSeq005.rightCfg (a := 1337))
    let last := PSTRTMSeq005.rightCfg (a := 1337)
      (depthFinal (riskArchive risk) bit earlier (sourceRight risk depth) gap)
    have hrun : Runs locatorMachine (encode [.rational risk,.natural depth]) trace last := by
      apply PSTRTMSeq005.seq_runs sourceMachine depthMachine
        (encode [.rational risk,.natural depth]) (sourceFinal risk depth)
        (depthFinal (riskArchive risk) bit earlier (sourceRight risk depth) gap)
        (sourceTrace risk depth) part (source_runs risk depth hr hd)
      rw [locator_entry,hreversed]
      exact depth_runsFrom _ _ _ _ _
    have htape : last.Tape = Turing.Tape.mk₂ (false::riskArchive risk) (locatorRight risk depth) := by
      dsimp only [last,PSTRTMSeq005.rightCfg]
      rw [depth_final_tape,hback]
      rfl
    have htime : trace.length ≤ 100663296*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
      have hm := source_time_le risk depth hr hd
      have hg := PSTRTMThresholdRiskReturnBudget230.result_gap_le risk depth hr hd
      have hdepth := PSTRTMThresholdRiskReturnBudget230.result_depth_length risk depth hd
      have hrev := congrArg List.length hreversed
      simp only [List.length_reverse,List.length_cons] at hrev
      have hw := PSTRTMThresholdBackup139.original_width_le risk depth hr
      rw [PSTRTMThresholdDepthSource184.depth_length] at hw
      have he : earlier.length ≤ (encode [.rational risk,.natural depth]).length+1 := by omega
      have hcost := arithmetic_time (encode [.rational risk,.natural depth]).length depth
        (result risk depth).gap earlier.length (sourceTrace risk depth).length hm hg he
      simpa only [trace,part,List.length_append,List.length_map,
        PSTRTMThresholdRiskReturn228.depth_length,gap,Nat.add_assoc] using hcost
    refine ⟨trace,last,hrun,htape,htime,?_⟩
    intro clock
    have hs := PSTRTMTrace002.visitedSpace_le locatorMachine
      (encode [.rational risk,.natural depth]).length (trace.take clock)
    have hl : (trace.take clock).length ≤ trace.length := by
      simp only [List.length_take]
      exact Nat.min_le_right _ _
    have hc := scale_cube (encode [.rational risk,.natural depth]).length depth
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRiskLocator231
