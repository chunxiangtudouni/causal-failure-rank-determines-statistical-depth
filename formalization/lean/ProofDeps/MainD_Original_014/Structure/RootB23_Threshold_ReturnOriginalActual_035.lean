module
public import Structure.RootB23_Threshold_ReturnOriginalCode_034
public import Structure.RootB23_Threshold_ReturnResources_033

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnOriginal
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PSTRTMSeq005
attribute [local implicit_reducible] rowCap cap OriginalBridge.cap

def timeCoefficient : ℕ := OriginalBridge.timeCoefficient+ReturnResources.pairCoefficient
def spaceCoefficient : ℕ := 2*timeCoefficient+2
private theorem charged_space (space charged count coefficient power : ℕ)
    (bound : space≤charged+2*count+1) (time : count≤coefficient*power) :
    space≤charged+2*(coefficient*power)+1 := by omega
private theorem original_space (space input count coefficient power : ℕ)
    (bound : space ≤ input+2*count+1) (time : count≤coefficient*power) (charged : input+1≤power) :
    space≤(2*coefficient+2)*power := by nlinarith only [bound,time,charged]

/-- ONE fixed original-input machine: genuine B/risk factor, real window,
the SAME multiplication/cap branch, actual B return, actual far B copy,
paid RIGHT8, and the actual first TWO original fields B/target. No output,
width, room or branch answer is an original input. -/
theorem actual (risk : Rat) (depth : ℕ) (hr : 0<risk) (hd : 1≤depth) :
    ∃ (left : ℕ) (trace : List (MachineState cap)),
      Runs code (encode [.rational risk,.natural depth]) trace
        ⟨finalPort (OriginalBridge.branch risk depth),ReturnPairReady.finalTape risk depth risk left⟩ ∧
      trace.length≤timeCoefficient*OriginalBridge.scale risk depth^10 ∧
      (∀ chargedLength clock, visitedSpace code chargedLength (trace.take clock)≤
        chargedLength+2*(timeCoefficient*OriginalBridge.scale risk depth^10)+1) ∧
      (∀ clock, visitedSpace code (encode [.rational risk,.natural depth]).length (trace.take clock)≤
        spaceCoefficient*OriginalBridge.scale risk depth^10) := by
  obtain ⟨left,right,before,beforeRun,_,_,sum,beforeTime,_⟩:=OriginalBridge.actual risk depth hr hd
  have positive:=OriginalBridge.product_positive risk depth hr
  obtain ⟨after,afterRun,afterTime⟩:=ReturnPairReady.actual_run risk depth risk left right positive
  have afterBound:=ReturnResources.original_pair_fee risk depth left right hr hd sum
  have beforeFrom : RunsFrom OriginalBridge.code
      ⟨0,Tape.mk₁ (encode [.rational risk,.natural depth])⟩ before
      ⟨OriginalBridge.finalPort (OriginalBridge.branch risk depth),ReturnActual.finalTape risk depth risk left right⟩ :=
    ⟨beforeRun.1,beforeRun.2.1,beforeRun.2.2.1,beforeRun.2.2.2.1⟩
  have paddedBefore:=pad_runsFrom before_le OriginalBridge.code _ _ _ beforeFrom
  have atStart : RunsFrom (rows (0 : Fin 2))
      (padCfg before_le ⟨0,Tape.mk₁ (encode [.rational risk,.natural depth])⟩)
      (before.map (padCfg before_le))
      (padCfg before_le ⟨OriginalBridge.finalPort (OriginalBridge.branch risk depth),ReturnActual.finalTape risk depth risk left right⟩) := by
    rw [rows_start]
    exact paddedBefore
  have startSegment:=block_segment rows ports (0 : Fin 2) _ _ _ atStart
  have transfer:=block_transfer rows ports (0 : Fin 2) _
    ((1 : Fin 2),padLabel after_le (ReturnPairReady.entry (OriginalBridge.branch risk depth)))
    atStart.2.2.2 (ports_observed _ _ (observed _))
  have paddedAfter:=pad_runsFrom after_le ReturnPairReady.code _ _ _ afterRun
  have atAfter : RunsFrom (rows (1 : Fin 2))
      (padCfg after_le ⟨ReturnPairReady.entry (OriginalBridge.branch risk depth),ReturnActual.finalTape risk depth risk left right⟩)
      (after.map (padCfg after_le))
      (padCfg after_le ⟨ReturnPairReady.exitPort (OriginalBridge.branch risk depth),ReturnPairReady.finalTape risk depth risk left⟩) := by
    rw [rows_after]
    exact paddedAfter
  have finishRun:=block_runsFrom rows ports (1 : Fin 2) _ _ _ atAfter (ports_after _)
  have fullSegment:=segment_append code _ _ _ _ _ _ startSegment
    ⟨finishRun.1,finishRun.2.1,finishRun.2.2.1⟩ transfer
  let trace:=(before.map (padCfg before_le)).map (blockCfg (p:=1) (0 : Fin 2))++
    (after.map (padCfg after_le)).map (blockCfg (p:=1) (1 : Fin 2))
  have run : Runs code (encode [.rational risk,.natural depth]) trace
      ⟨finalPort (OriginalBridge.branch risk depth),ReturnPairReady.finalTape risk depth risk left⟩ := by
    have joined:=segment_runsFrom code _ _ _ fullSegment finishRun.2.2.2
    have genuine : RunsFrom code ⟨0,Tape.mk₁ (encode [.rational risk,.natural depth])⟩ trace
        ⟨finalPort (OriginalBridge.branch risk depth),ReturnPairReady.finalTape risk depth risk left⟩ := by
      simpa only [trace,padCfg,padLabel,Fin.val_zero,Fin.mk_zero,finalPort,blockCfg,label,
        Nat.zero_mul,Nat.zero_add] using joined
    exact PSTRTMTrace002.runs_of_chain _ _ _ _ genuine.1 genuine.2.1 genuine.2.2.1 genuine.2.2.2
  have length : trace.length=before.length+after.length := by
    dsimp only [trace]
    rw [List.length_append,List.length_map,List.length_map,List.length_map,List.length_map]
  have beforePower : OriginalBridge.scale risk depth^8≤OriginalBridge.scale risk depth^10 :=
    Nat.pow_le_pow_right (OriginalBridge.scale_positive risk depth) (by decide : 8≤10)
  have prefixFee:=beforeTime.trans (Nat.mul_le_mul_left OriginalBridge.timeCoefficient beforePower)
  have time : trace.length≤timeCoefficient*OriginalBridge.scale risk depth^10 := by
    rw [length]
    have total:=Nat.add_le_add prefixFee (afterTime.trans afterBound)
    exact total.trans_eq (Nat.add_mul OriginalBridge.timeCoefficient ReturnResources.pairCoefficient
      (OriginalBridge.scale risk depth^10)).symm
  refine ⟨left,trace,run,time,?_,?_⟩
  · intro chargedLength clock
    have space:=PSTRTMTrace002.visitedSpace_le code chargedLength (trace.take clock)
    have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
    exact charged_space _ _ _ _ _ space (taken.trans time)
  · intro clock
    have space:=PSTRTMTrace002.visitedSpace_le code (encode [.rational risk,.natural depth]).length (trace.take clock)
    have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
    have input : (encode [.rational risk,.natural depth]).length+1≤OriginalBridge.scale risk depth := by
      unfold OriginalBridge.scale
      omega
    have power : OriginalBridge.scale risk depth≤OriginalBridge.scale risk depth^10 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (OriginalBridge.scale_positive risk depth) (by decide : 1≤10)
    exact original_space _ _ _ _ _ space (taken.trans time) (input.trans power)

end RootB23.Threshold.ReturnOriginal
