module
public import Common.PSTR_TM_ThresholdCopySegments_134

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyRound135
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCopyCode126 PSTRTMThresholdCopyRoundLift129 PSTRTMThresholdCopyAppend130 PSTRTMThresholdCopySegments134

def cursorStart (entry : Fin 3) : Fin 40 := match entry.val with | 0 => 1 | 1 => 5 | _ => 7
def cursorEnd (entry : Fin 3) : Fin 40 := match entry.val with | 0 => 3 | 1 => 7 | _ => 9
def rewindStart (entry : Fin 3) : Fin 40 := match entry.val with | 0 => 17 | 1 => 24 | _ => 29
def rewindEnd (entry : Fin 3) : Fin 40 := match entry.val with | 0 => 20 | 1 => 27 | _ => 32

def cursorAt (bit : Bool) (entry : Fin 3) (left digits tail : List Bool) :
    Segment (savedState bit (cursorStart entry) left (PSTRTMIncrement009.blocks digits++false::false::tail))
      (savedState bit (cursorEnd entry) (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail) where
  trace := (PSTRTMThresholdCursor115.cursorTrace left digits tail).map (liftCursor bit entry)
  head := by
    fin_cases entry <;> simp only [List.head?_map,PSTRTMThresholdCursor115.cursor_head,Option.map_some,
      cursorStart,liftCursor,cursorLabel,PSTRTMThresholdCursor115.state,savedState,state,Fin.val_zero] <;> rfl
  chain := cursor_chain bit entry _ (PSTRTMThresholdCursor115.cursor_chain _ _ _)
  last := by
    fin_cases entry <;> simp only [List.getLast?_map,PSTRTMThresholdCursor115.cursor_last,Option.map_some,
      cursorEnd,liftCursor,cursorLabel,PSTRTMThresholdCursor115.state,savedState,state] <;> rfl

def rewindAt (bit : Bool) (entry : Fin 3) (archive digits tail : List Bool) :
    Segment (savedState bit (rewindStart entry) (PSTRTMRawNat010.leftBlocks digits.reverse++false::archive) tail)
      (savedState bit (rewindEnd entry) (false::archive) (PSTRTMIncrement009.blocks digits++tail)) where
  trace := (PSTRTMPairRewind105.fullTrace archive digits.reverse tail).map (liftRewind bit entry)
  head := by
    fin_cases entry <;> simp only [List.head?_map,PSTRTMPairRewind105.full_head,Option.map_some,
      rewindStart,liftRewind,rewindLabel,PSTRTMMulRewind085.state,savedState,state,Fin.val_zero]
  chain := rewind_chain bit entry _ (PSTRTMPairRewind105.full_chain _ _ _)
  last := by
    fin_cases entry <;> simp only [List.getLast?_map,PSTRTMPairRewind105.full_last,List.reverse_reverse,Option.map_some,
      rewindEnd,liftRewind,rewindLabel,PSTRTMMulRewind085.state,savedState,state]

def rewindBlankAt (bit : Bool) (archive digits : List Bool) :
    Segment (savedState bit 17 (PSTRTMRawNat010.leftBlocks digits.reverse++false::archive) [])
      (savedState bit 20 (false::archive) (PSTRTMIncrement009.blocks digits)) where
  trace := (PSTRTMPairRewind105.fullTrace archive digits.reverse []).map (liftRewind bit 0)
  head := (rewindAt bit 0 archive digits []).head
  chain := (rewindAt bit 0 archive digits []).chain
  last := by simpa only [rewindAt,rewindEnd,Fin.val_zero,List.append_nil] using (rewindAt bit 0 archive digits []).last

def middle (denominator depth copied : List Bool) : List Bool :=
  false::false::true::false::(PSTRTMIncrement009.blocks denominator++false::false::
    (PSTRTMIncrement009.blocks depth++false::false::true::false::PSTRTMIncrement009.blocks copied))

def sourceEndLeft (bit : Bool) (left later : List Bool) : List Bool :=
  false::false::(PSTRTMRawNat010.leftBlocks later.reverse++false::bit::left)

def denLeft (bit : Bool) (left later : List Bool) : List Bool := false::true::sourceEndLeft bit left later

def depthLeft (bit : Bool) (left later denominator : List Bool) : List Bool :=
  false::false::(PSTRTMRawNat010.leftBlocks denominator.reverse++denLeft bit left later)

def targetMarkerLeft (bit : Bool) (left later denominator depth : List Bool) : List Bool :=
  false::false::(PSTRTMRawNat010.leftBlocks depth.reverse++depthLeft bit left later denominator)

def targetLeft (bit : Bool) (left later denominator depth : List Bool) : List Bool :=
  false::true::targetMarkerLeft bit left later denominator depth

def roundInitial (bit : Bool) (left later denominator depth copied : List Bool) : MachineState 130 :=
  state 34 left (bit::true::(PSTRTMIncrement009.blocks later++middle denominator depth copied))

def roundFinal (bit : Bool) (left later denominator depth copied : List Bool) : MachineState 130 :=
  state 34 (true::bit::left) (PSTRTMIncrement009.blocks later++middle denominator depth (copied++[bit]))

/-- Every actual read, temporary flag write, forward shuttle, target
append, reverse shuttle, flag restore and final right move is in this
segment of SAME fixed code126. Adjacent pieces join only at an IDENTICAL
whole configuration; no free archive copy/cursor reset is assumed. -/
def roundSegment (bit : Bool) (left later denominator depth copied : List Bool) :
    Segment (roundInitial bit left later denominator depth copied) (roundFinal bit left later denominator depth copied) := by
  let denTail := PSTRTMIncrement009.blocks depth++false::false::true::false::PSTRTMIncrement009.blocks copied
  let denWord := PSTRTMIncrement009.blocks denominator++false::false::denTail
  let s0 := startSegment bit left (PSTRTMIncrement009.blocks later++middle denominator depth copied)
  let s1 := cursorAt bit ⟨0,by decide⟩ (false::bit::left) later (true::false::denWord)
  let s2 := markerSegment bit false (sourceEndLeft bit left later) denWord
  let s3 := cursorAt bit ⟨1,by decide⟩ (denLeft bit left later) denominator denTail
  let s4 := cursorAt bit ⟨2,by decide⟩ (depthLeft bit left later denominator) depth (true::false::PSTRTMIncrement009.blocks copied)
  let s5 := markerSegment bit true (targetMarkerLeft bit left later denominator depth) (PSTRTMIncrement009.blocks copied)
  let s6 := appendBlankSegment bit (targetLeft bit left later denominator depth) copied
  let s7 := rewindBlankAt bit (true::targetMarkerLeft bit left later denominator depth) (copied++[bit])
  let s8 := fourLeftSegment bit false (PSTRTMRawNat010.leftBlocks depth.reverse++depthLeft bit left later denominator)
    (PSTRTMIncrement009.blocks (copied++[bit]))
  let newDepthTail := PSTRTMIncrement009.blocks depth++false::false::true::false::PSTRTMIncrement009.blocks (copied++[bit])
  let s9 := rewindAt bit ⟨1,by decide⟩ (false::(PSTRTMRawNat010.leftBlocks denominator.reverse++denLeft bit left later)) depth
    (false::false::true::false::PSTRTMIncrement009.blocks (copied++[bit]))
  let s10 := twoLeftSegment bit (PSTRTMRawNat010.leftBlocks denominator.reverse++denLeft bit left later) newDepthTail
  let s11 := rewindAt bit ⟨2,by decide⟩ (true::sourceEndLeft bit left later) denominator (false::false::newDepthTail)
  let s12 := fourLeftSegment bit true (PSTRTMRawNat010.leftBlocks later.reverse++false::bit::left)
    (PSTRTMIncrement009.blocks denominator++false::false::newDepthTail)
  let s13 := restoreSegment bit (bit::left) later (middle denominator depth (copied++[bit]))
  exact ((((((((((((s0.join s1).join s2).join s3).join s4).join s5).join s6).join s7).join s8).join s9).join s10).join s11).join s12).join s13

def roundTrace (bit : Bool) (left later denominator depth copied : List Bool) : List (MachineState 130) :=
  (roundSegment bit left later denominator depth copied).trace

theorem round_head (bit : Bool) (left later denominator depth copied : List Bool) :
    (roundTrace bit left later denominator depth copied).head?=some (roundInitial bit left later denominator depth copied) :=
  (roundSegment bit left later denominator depth copied).head

theorem round_chain (bit : Bool) (left later denominator depth copied : List Bool) :
    (roundTrace bit left later denominator depth copied).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) :=
  (roundSegment bit left later denominator depth copied).chain

theorem round_last (bit : Bool) (left later denominator depth copied : List Bool) :
    (roundTrace bit left later denominator depth copied).getLast?=some (roundFinal bit left later denominator depth copied) :=
  (roundSegment bit left later denominator depth copied).last

theorem round_length_le (bit : Bool) (left later denominator depth copied : List Bool) :
    (roundTrace bit left later denominator depth copied).length ≤
      4*(later.length+denominator.length+depth.length+copied.length)+54 := by
  simp only [roundTrace,roundSegment,Segment.join,PSTRTMOverlap132.glue_length,
    cursorAt,rewindAt,rewindBlankAt,List.length_map,PSTRTMThresholdCursor115.cursor_length,PSTRTMPairRewind105.full_length,
    List.length_reverse,startSegment_length,markerSegment_length,appendBlankSegment_length,
    fourLeftSegment_length,twoLeftSegment_length,restoreSegment_length,List.length_append,List.length_cons,List.length_nil]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyRound135
