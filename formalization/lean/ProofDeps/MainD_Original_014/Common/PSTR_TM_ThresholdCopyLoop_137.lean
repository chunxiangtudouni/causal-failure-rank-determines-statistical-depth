module
public import Common.PSTR_TM_ThresholdCopyFinish_136

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyLoop137
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCopyCode126 PSTRTMThresholdCopySegments134

def sourceLeft (archive previous : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks previous.reverse++false::archive

theorem sourceLeft_append (archive previous : List Bool) (bit : Bool) :
    sourceLeft archive (previous++[bit])=true::bit::sourceLeft archive previous := by
  simp [sourceLeft,List.reverse_append,PSTRTMRawNat010.leftBlocks]

def loopInitial (archive previous remaining denominator depth : List Bool) : MachineState 130 :=
  state 34 (sourceLeft archive previous)
    (PSTRTMIncrement009.blocks remaining++PSTRTMThresholdCopyRound135.middle denominator depth previous)

def loopFinal (archive numerator denominator depth : List Bool) : MachineState 130 :=
  PSTRTMThresholdCopyFinish136.finishFinal (sourceLeft archive numerator) denominator depth numerator

/-- Structural recursion supplies a trace witness only. Code126 reads
actual source flags and never reads this remaining list/length/fuel as an
extra input. At each round, actual flag restoration and whole-config
identity justify the recursive continuation on the same real tape. -/
def loopSegment (archive previous denominator depth : List Bool) : (remaining : List Bool) →
    Segment (loopInitial archive previous remaining denominator depth)
      (loopFinal archive (previous++remaining) denominator depth)
  | [] =>
    (PSTRTMThresholdCopyFinish136.finishSegment (sourceLeft archive previous) denominator depth previous).retarget
      (by simp only [PSTRTMThresholdCopyFinish136.finishInitial,loopInitial,PSTRTMIncrement009.blocks,List.flatMap_nil,List.nil_append])
      (by simp only [loopFinal,List.append_nil])
  | bit::later =>
    let before := PSTRTMThresholdCopyRound135.roundSegment bit (sourceLeft archive previous) later denominator depth previous
    let after := loopSegment archive (previous++[bit]) denominator depth later
    let after' := after.retarget
      (show loopInitial archive (previous++[bit]) later denominator depth =
        PSTRTMThresholdCopyRound135.roundFinal bit (sourceLeft archive previous) later denominator depth previous from by
          simp only [loopInitial,PSTRTMThresholdCopyRound135.roundFinal,sourceLeft_append])
      (show loopFinal archive ((previous++[bit])++later) denominator depth =
        loopFinal archive (previous++bit::later) denominator depth from by simp only [List.append_assoc,List.singleton_append])
    (before.join after').retarget
      (by simp only [PSTRTMThresholdCopyRound135.roundInitial,loopInitial,PSTRTMIncrement009.blocks,
        List.flatMap_cons,List.cons_append,List.nil_append]) rfl

def loopTrace (archive previous remaining denominator depth : List Bool) : List (MachineState 130) :=
  (loopSegment archive previous denominator depth remaining).trace

theorem loop_runsFrom (archive previous remaining denominator depth : List Bool) :
    PSTRTMSeq005.RunsFrom copyMachine (loopInitial archive previous remaining denominator depth)
      (loopTrace archive previous remaining denominator depth) (loopFinal archive (previous++remaining) denominator depth) := by
  refine ⟨(loopSegment archive previous denominator depth remaining).head,
    (loopSegment archive previous denominator depth remaining).chain,
    (loopSegment archive previous denominator depth remaining).last,?_⟩
  exact copy_halt _ _

def initializeSegment (archive numerator denominator depth : List Bool) :
    Segment (state 0 (false::archive) (PSTRTMThresholdRewind124.sourceWord numerator denominator depth))
      (PSTRTMThresholdCopyInit128.initializeFinal archive numerator denominator depth) where
  trace := PSTRTMThresholdCopyInit128.initializeTrace archive numerator denominator depth
  head := PSTRTMThresholdCopyInit128.initialize_head _ _ _ _
  chain := PSTRTMThresholdCopyInit128.initialize_chain _ _ _ _
  last := PSTRTMThresholdCopyInit128.initialize_last _ _ _ _

def copyInitial (archive numerator denominator depth : List Bool) : MachineState 130 :=
  state 0 (false::archive) (PSTRTMThresholdRewind124.sourceWord numerator denominator depth)

def copyFinal (archive numerator denominator depth : List Bool) : MachineState 130 :=
  loopFinal archive numerator denominator depth

def copySegment (archive numerator denominator depth : List Bool) :
    Segment (copyInitial archive numerator denominator depth) (copyFinal archive numerator denominator depth) := by
  let prepare := initializeSegment archive numerator denominator depth
  let run := (loopSegment archive [] denominator depth numerator).retarget
    (show loopInitial archive [] numerator denominator depth =
      PSTRTMThresholdCopyInit128.initializeFinal archive numerator denominator depth from by
        simp only [loopInitial,sourceLeft,PSTRTMRawNat010.leftBlocks,List.flatMap_nil,List.reverse_nil,List.nil_append,
          PSTRTMThresholdCopyInit128.initializeFinal,PSTRTMThresholdRewind124.sourceWord,
          PSTRTMThresholdCopyRound135.middle,PSTRTMIncrement009.blocks,List.append_assoc,List.cons_append,List.flatMap_nil,List.nil_append])
    (show loopFinal archive ([]++numerator) denominator depth=copyFinal archive numerator denominator depth from by simp only [List.nil_append,copyFinal])
  exact prepare.join run

def copyTrace (archive numerator denominator depth : List Bool) : List (MachineState 130) :=
  (copySegment archive numerator denominator depth).trace

/-- Genuine full131-label copier, including real initialization, all
source-bit rounds, the computed EOF branch, final transports and HALT. -/
theorem copy_runsFrom (archive numerator denominator depth : List Bool) :
    PSTRTMSeq005.RunsFrom copyMachine (copyInitial archive numerator denominator depth)
      (copyTrace archive numerator denominator depth) (copyFinal archive numerator denominator depth) :=
  ⟨(copySegment archive numerator denominator depth).head,(copySegment archive numerator denominator depth).chain,
    (copySegment archive numerator denominator depth).last,copy_halt _ _⟩

/-- ENTIRE final tape. All three source fields and every archive bit remain
in the explicit left data. The new flagged NUM copy has a real blank tail
and an actually read false guard for the next resident computation. -/
theorem copy_final_tape (archive numerator denominator depth : List Bool) :
    (copyFinal archive numerator denominator depth).Tape=Turing.Tape.mk₂
      (false::true::false::false::(PSTRTMRawNat010.leftBlocks depth.reverse++
        false::false::(PSTRTMRawNat010.leftBlocks denominator.reverse++
          false::true::false::false::(PSTRTMRawNat010.leftBlocks numerator.reverse++false::archive))))
      (PSTRTMIncrement009.blocks numerator) := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyLoop137
