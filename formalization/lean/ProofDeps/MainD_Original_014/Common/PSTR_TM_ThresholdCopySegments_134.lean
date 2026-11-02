module
public import Common.PSTR_TM_ThresholdCopyBridges_133

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopySegments134
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCopyCode126 PSTRTMThresholdCopyRoundLift129 PSTRTMThresholdCopyAppend130

/-- Internal certificate of a concrete prefix of the ONE fixed131-label
copier. No resource/result field is added to its machine/input. The whole
initial/final configurations are types checked at every shared boundary. -/
structure Segment (initial final : MachineState 130) where
  trace : List (MachineState 130)
  head : trace.head?=some initial
  chain : trace.IsChain (fun before after => Turing.TM0.step copyMachine before=some after)
  last : trace.getLast?=some final

def Segment.join {initial shared final : MachineState 130}
    (before : Segment initial shared) (after : Segment shared final) : Segment initial final where
  trace := PSTRTMOverlap132.glue before.trace after.trace
  head := PSTRTMOverlap132.glue_head _ _ _ _ before.head before.last after.head
  chain := PSTRTMOverlap132.glue_chain copyMachine _ _ _ before.chain after.chain before.last after.head
  last := PSTRTMOverlap132.glue_last _ _ _ after.last

theorem Segment.join_length_le {initial shared final : MachineState 130}
    (before : Segment initial shared) (after : Segment shared final) :
    (before.join after).trace.length≤before.trace.length+after.trace.length :=
  PSTRTMOverlap132.glue_length_le _ _

def Segment.retarget {initial final initial' final' : MachineState 130}
    (segment : Segment initial final) (hi : initial=initial') (hf : final=final') : Segment initial' final' := by
  cases hi
  cases hf
  exact segment

theorem Segment.retarget_trace {initial final initial' final' : MachineState 130}
    (segment : Segment initial final) (hi : initial=initial') (hf : final=final') :
    (segment.retarget hi hf).trace=segment.trace := by cases hi; cases hf; rfl

def cursorSegment (bit : Bool) (entry : Fin 3) (left digits tail : List Bool) :
    Segment (liftCursor bit entry (PSTRTMThresholdCursor115.state 0 left
      (PSTRTMIncrement009.blocks digits++false::false::tail)))
      (liftCursor bit entry (PSTRTMThresholdCursor115.state 2
        (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail)) where
  trace := (PSTRTMThresholdCursor115.cursorTrace left digits tail).map (liftCursor bit entry)
  head := by simp only [List.head?_map,PSTRTMThresholdCursor115.cursor_head,Option.map_some]
  chain := cursor_chain bit entry _ (PSTRTMThresholdCursor115.cursor_chain _ _ _)
  last := by simp only [List.getLast?_map,PSTRTMThresholdCursor115.cursor_last,Option.map_some]

def rewindSegment (bit : Bool) (entry : Fin 3) (archive digits tail : List Bool) :
    Segment (liftRewind bit entry (PSTRTMMulRewind085.state 0
      (PSTRTMRawNat010.leftBlocks digits.reverse++false::archive) tail))
      (liftRewind bit entry (PSTRTMMulRewind085.state 3 (false::archive)
        (PSTRTMIncrement009.blocks digits++tail))) where
  trace := (PSTRTMPairRewind105.fullTrace archive digits.reverse tail).map (liftRewind bit entry)
  head := by simp only [List.head?_map,PSTRTMPairRewind105.full_head,Option.map_some]
  chain := rewind_chain bit entry _ (PSTRTMPairRewind105.full_chain _ _ _)
  last := by simp only [List.getLast?_map,PSTRTMPairRewind105.full_last,List.reverse_reverse,Option.map_some]

def startSegment (bit : Bool) (left tail : List Bool) :
    Segment (state 34 left (bit::true::tail)) (savedState bit 1 (false::bit::left) tail) where
  trace := PSTRTMThresholdCopyBridges133.startTrace bit left tail
  head := PSTRTMThresholdCopyBridges133.start_head _ _ _
  chain := PSTRTMThresholdCopyBridges133.start_chain _ _ _
  last := PSTRTMThresholdCopyBridges133.start_last _ _ _

def markerSegment (bit target : Bool) (left tail : List Bool) :
    Segment (savedState bit (if target then 9 else 3) left (true::false::tail))
      (savedState bit (if target then 11 else 5) (false::true::left) tail) where
  trace := PSTRTMThresholdCopyBridges133.markerTrace bit target left tail
  head := PSTRTMThresholdCopyBridges133.marker_head _ _ _ _
  chain := PSTRTMThresholdCopyBridges133.marker_chain _ _ _ _
  last := PSTRTMThresholdCopyBridges133.marker_last _ _ _ _

def fourLeftSegment (bit source : Bool) (archive tail : List Bool) :
    Segment (savedState bit (if source then 32 else 20) (false::true::false::false::archive) tail)
      (savedState bit (if source then 36 else 24) archive (false::false::true::false::tail)) where
  trace := PSTRTMThresholdCopyBridges133.fourLeftTrace bit source archive tail
  head := PSTRTMThresholdCopyBridges133.fourLeft_head _ _ _ _
  chain := PSTRTMThresholdCopyBridges133.fourLeft_chain _ _ _ _
  last := PSTRTMThresholdCopyBridges133.fourLeft_last _ _ _ _

def twoLeftSegment (bit : Bool) (archive tail : List Bool) :
    Segment (savedState bit 27 (false::false::archive) tail) (savedState bit 29 archive (false::false::tail)) where
  trace := PSTRTMThresholdCopyBridges133.twoLeftTrace bit archive tail
  head := PSTRTMThresholdCopyBridges133.twoLeft_head _ _ _
  chain := PSTRTMThresholdCopyBridges133.twoLeft_chain _ _ _
  last := PSTRTMThresholdCopyBridges133.twoLeft_last _ _ _

def appendSegment (bit : Bool) (left digits : List Bool) :
    Segment (savedState bit 11 left (PSTRTMIncrement009.blocks digits++[false,false]))
      (savedState bit 17 (PSTRTMRawNat010.leftBlocks (digits++[bit]).reverse++left) []) where
  trace := appendTrace bit left digits
  head := append_head _ _ _
  chain := append_chain _ _ _
  last := append_last _ _ _

theorem savedState_right_zeros (bit : Bool) (q : Fin 40) (left bits : List Bool) :
    savedState bit q left (bits++[false,false])=savedState bit q left bits := by
  have hz : Turing.ListBlank.mk (bits++[false,false])=Turing.ListBlank.mk bits := by
    calc
      _ = Turing.ListBlank.mk ((bits++[false])++[false]) := by rw [List.append_assoc]; rfl
      _ = Turing.ListBlank.mk (bits++[false]) := PSTRTMRawNat010.blank_append_false _
      _ = Turing.ListBlank.mk bits := PSTRTMRawNat010.blank_append_false _
  simp only [savedState,state,Turing.Tape.mk₂,hz]

def appendBlankSegment (bit : Bool) (left digits : List Bool) :
    Segment (savedState bit 11 left (PSTRTMIncrement009.blocks digits))
      (savedState bit 17 (PSTRTMRawNat010.leftBlocks (digits++[bit]).reverse++left) []) :=
  (appendSegment bit left digits).retarget (savedState_right_zeros bit 11 left _) rfl

def restoreSegment (bit : Bool) (left digits tail : List Bool) :
    Segment (savedState bit 36 (PSTRTMRawNat010.leftBlocks digits.reverse++false::left) tail)
      (state 34 (true::left) (PSTRTMIncrement009.blocks digits++tail)) where
  trace := PSTRTMThresholdCopyRestore131.restoreTrace bit left digits.reverse tail
  head := PSTRTMThresholdCopyRestore131.restore_head _ _ _ _
  chain := PSTRTMThresholdCopyRestore131.restore_chain _ _ _ _
  last := by simpa only [List.reverse_reverse] using PSTRTMThresholdCopyRestore131.restore_last bit left digits.reverse tail

theorem cursorSegment_length (bit : Bool) (entry : Fin 3) (left digits tail : List Bool) :
    (cursorSegment bit entry left digits tail).trace.length=2*digits.length+3 := by
  simp only [cursorSegment,List.length_map,PSTRTMThresholdCursor115.cursor_length]

theorem rewindSegment_length (bit : Bool) (entry : Fin 3) (archive digits tail : List Bool) :
    (rewindSegment bit entry archive digits tail).trace.length=2*digits.length+3 := by
  simp only [rewindSegment,List.length_map,PSTRTMPairRewind105.full_length,List.length_reverse]

theorem startSegment_length (bit : Bool) (left tail : List Bool) :
    (startSegment bit left tail).trace.length=4 := rfl

theorem markerSegment_length (bit target : Bool) (left tail : List Bool) :
    (markerSegment bit target left tail).trace.length=3 := rfl

theorem fourLeftSegment_length (bit source : Bool) (archive tail : List Bool) :
    (fourLeftSegment bit source archive tail).trace.length=5 := rfl

theorem twoLeftSegment_length (bit : Bool) (archive tail : List Bool) :
    (twoLeftSegment bit archive tail).trace.length=3 := rfl

theorem appendBlankSegment_length (bit : Bool) (left digits : List Bool) :
    (appendBlankSegment bit left digits).trace.length=2*digits.length+7 := by
  simp only [appendBlankSegment,Segment.retarget_trace,appendSegment,append_length]

theorem restoreSegment_length (bit : Bool) (left digits tail : List Bool) :
    (restoreSegment bit left digits tail).trace.length=2*digits.length+4 := by
  simp only [restoreSegment,PSTRTMThresholdCopyRestore131.restore_length,List.length_reverse]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopySegments134
