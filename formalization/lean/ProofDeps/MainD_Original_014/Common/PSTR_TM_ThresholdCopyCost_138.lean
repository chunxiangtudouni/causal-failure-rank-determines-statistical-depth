module
public import Common.PSTR_TM_ThresholdCopyLoop_137

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyCost138
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCopyCode126 PSTRTMThresholdCopySegments134 PSTRTMThresholdCopyLoop137

theorem loop_length_le (archive previous remaining denominator depth : List Bool) :
    (loopTrace archive previous remaining denominator depth).length ≤
      remaining.length*(4*(previous.length+remaining.length+denominator.length+depth.length)+54)+
        2*denominator.length+2*depth.length+16 := by
  induction remaining generalizing previous with
  | nil =>
    simp only [loopTrace,loopSegment,Segment.retarget_trace,List.length_nil,Nat.zero_mul,Nat.zero_add]
    exact PSTRTMThresholdCopyFinish136.finish_length_le _ _ _ _
  | cons bit later ih =>
    have hr := PSTRTMThresholdCopyRound135.round_length_le bit (sourceLeft archive previous) later denominator depth previous
    have ha := ih (previous++[bit])
    have hg := PSTRTMOverlap132.glue_length_le
      (PSTRTMThresholdCopyRound135.roundSegment bit (sourceLeft archive previous) later denominator depth previous).trace
      (loopSegment archive (previous++[bit]) denominator depth later).trace
    simp only [List.length_append,List.length_cons,List.length_nil] at ha
    simp only [loopTrace,loopSegment,Segment.retarget_trace,Segment.join]
    simp only [PSTRTMThresholdCopyRound135.roundTrace,loopTrace] at hr ha
    simp only [List.length_cons]
    nlinarith

private theorem arithmetic_length_bound (n d e first second total : Nat)
    (hf : first=4*(n+d+e)+29)
    (hs : second≤n*(4*(0+n+d+e)+54)+2*d+2*e+16)
    (ht : total≤first+second) : total≤256*(n+d+e+1)^2 := by
  have hn : n≤n+d+e := by omega
  have hm := Nat.mul_le_mul_right (n+d+e) hn
  nlinarith

theorem copy_length_le (archive numerator denominator depth : List Bool) :
    (copyTrace archive numerator denominator depth).length≤256*(numerator.length+denominator.length+depth.length+1)^2 := by
  have hi := PSTRTMThresholdCopyInit128.initialize_length archive numerator denominator depth
  have hl := loop_length_le archive [] numerator denominator depth
  have hg := PSTRTMOverlap132.glue_length_le
    (initializeSegment archive numerator denominator depth).trace
    (loopSegment archive [] denominator depth numerator).trace
  have ht : (copyTrace archive numerator denominator depth).length≤
      (PSTRTMThresholdCopyInit128.initializeTrace archive numerator denominator depth).length+
        (loopTrace archive [] numerator denominator depth).length := by
    simpa only [copyTrace,copySegment,Segment.join,Segment.retarget_trace,initializeSegment,loopTrace] using hg
  simp only [List.length_nil] at hl
  exact arithmetic_length_bound _ _ _ _ _ _ hi hl ht

theorem sourceWord_length (numerator denominator depth : List Bool) :
    (PSTRTMThresholdRewind124.sourceWord numerator denominator depth).length=
      2*(numerator.length+denominator.length+depth.length)+6 := by
  simp only [PSTRTMThresholdRewind124.sourceWord,List.length_append,PSTRTMIncrement009.blocks_length,
    List.length_cons,List.length_nil]
  omega

private theorem arithmetic_space_bound (archive width time space : Nat)
    (ht : time≤256*(width+1)^2) (hs : space≤archive+1+(2*width+6)+2*time+1) :
    space≤archive+1024*(width+1)^2 := by nlinarith

/-- ORIGINAL visitedSpace of the SAME actual copyTrace, including the
actual archived cells, all real source fields and every counted shuttle. -/
theorem copy_visitedSpace_le (archive numerator denominator depth : List Bool) :
    visitedSpace copyMachine
      (archive.length+1+(PSTRTMThresholdRewind124.sourceWord numerator denominator depth).length)
      (copyTrace archive numerator denominator depth) ≤
        archive.length+1024*(numerator.length+denominator.length+depth.length+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le copyMachine
    (archive.length+1+(PSTRTMThresholdRewind124.sourceWord numerator denominator depth).length)
    (copyTrace archive numerator denominator depth)
  rw [sourceWord_length] at hs ⊢
  exact arithmetic_space_bound _ _ _ _ (copy_length_le archive numerator denominator depth) hs

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyCost138
