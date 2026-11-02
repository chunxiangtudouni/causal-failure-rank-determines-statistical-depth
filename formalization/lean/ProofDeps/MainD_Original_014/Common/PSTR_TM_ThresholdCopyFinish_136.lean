module
public import Common.PSTR_TM_ThresholdCopyRound_135

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyFinish136
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCopyCode126 PSTRTMThresholdCopySegments134

def startLabel (depth : Bool) : Fin 131 := if depth then 126 else 124
def flagLabel (depth : Bool) : Fin 131 := if depth then 127 else 125
def endLabel (depth : Bool) : Fin 131 := if depth then 128 else 126

def scanTrace (depth : Bool) (left : List Bool) : List Bool → List Bool → List (MachineState 130)
  | [],tail => [state (startLabel depth) left (false::false::tail),
      state (flagLabel depth) (false::left) (false::tail),state (endLabel depth) (false::false::left) tail]
  | bit::later,tail => [state (startLabel depth) left (bit::true::(PSTRTMIncrement009.blocks later++false::false::tail)),
      state (flagLabel depth) (bit::left) (true::(PSTRTMIncrement009.blocks later++false::false::tail))] ++
      scanTrace depth (true::bit::left) later tail

theorem scan_head (depth : Bool) (left digits tail : List Bool) : (scanTrace depth left digits tail).head?=some
    (state (startLabel depth) left (PSTRTMIncrement009.blocks digits++false::false::tail)) := by cases digits <;> rfl

theorem scan_last (depth : Bool) (left digits tail : List Bool) : (scanTrace depth left digits tail).getLast?=some
    (state (endLabel depth) (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail) := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have hne : scanTrace depth (true::bit::left) later tail≠[] := by
      intro h
      have hh := scan_head depth (true::bit::left) later tail
      simp [h] at hh
    simp only [scanTrace,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem scan_chain (depth : Bool) (left digits tail : List Bool) :
    (scanTrace depth left digits tail).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  induction digits generalizing left with
  | nil => cases depth <;> simp [scanTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,startLabel,flagLabel,endLabel,state,Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [scanTrace]
    apply List.IsChain.append
    · cases depth <;> simp [List.isChain_cons_cons,Turing.TM0.step,copyMachine,startLabel,flagLabel,state,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [scan_head,Option.mem_some_iff] at ha
      subst before
      subst after
      cases depth <;> simp [Turing.TM0.step,copyMachine,startLabel,flagLabel,state,Turing.Tape.mk₂]

theorem scan_length (depth : Bool) (left digits tail : List Bool) : (scanTrace depth left digits tail).length=2*digits.length+3 := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih => simp only [scanTrace,List.length_append,List.length_cons,List.length_nil,ih]; omega

def scanSegment (depth : Bool) (left digits tail : List Bool) :
    Segment (state (startLabel depth) left (PSTRTMIncrement009.blocks digits++false::false::tail))
      (state (endLabel depth) (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail) where
  trace := scanTrace depth left digits tail
  head := scan_head _ _ _ _
  chain := scan_chain _ _ _ _
  last := scan_last _ _ _ _

/-- Actual34/35 EOF read/branch is charged before120..123 cross0010. -/
def sourceTrace (left tail : List Bool) : List (MachineState 130) :=
  [state 34 left (false::false::true::false::tail),state 35 (false::left) (false::true::false::tail),
    state 120 left (false::false::true::false::tail),state 121 (false::left) (false::true::false::tail),
    state 122 (false::false::left) (true::false::tail),state 123 (true::false::false::left) (false::tail),
    state 124 (false::true::false::false::left) tail]

def sourceSegment (left tail : List Bool) :
    Segment (state 34 left (false::false::true::false::tail))
      (state 124 (false::true::false::false::left) tail) where
  trace := sourceTrace left tail
  head := rfl
  chain := by simp [sourceTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂]
  last := rfl

def targetTrace (left copied : List Bool) : List (MachineState 130) :=
  [state 128 left (true::false::PSTRTMIncrement009.blocks copied),
    state 129 (true::left) (false::PSTRTMIncrement009.blocks copied),
    state 130 (false::true::left) (PSTRTMIncrement009.blocks copied)]

def targetSegment (left copied : List Bool) :
    Segment (state 128 left (true::false::PSTRTMIncrement009.blocks copied))
      (state 130 (false::true::left) (PSTRTMIncrement009.blocks copied)) where
  trace := targetTrace left copied
  head := rfl
  chain := by simp [targetTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂]
  last := rfl

def denLeft (left : List Bool) : List Bool := false::true::false::false::left

def depthLeft (left denominator : List Bool) : List Bool :=
  false::false::(PSTRTMRawNat010.leftBlocks denominator.reverse++denLeft left)

def finishInitial (left denominator depth copied : List Bool) : MachineState 130 :=
  state 34 left (PSTRTMThresholdCopyRound135.middle denominator depth copied)

def finishFinal (left denominator depth copied : List Bool) : MachineState 130 :=
  state 130 (false::true::false::false::(PSTRTMRawNat010.leftBlocks depth.reverse++depthLeft left denominator))
    (PSTRTMIncrement009.blocks copied)

def finishSegment (left denominator depth copied : List Bool) :
    Segment (finishInitial left denominator depth copied) (finishFinal left denominator depth copied) := by
  let start := sourceSegment left (PSTRTMIncrement009.blocks denominator++false::false::
    (PSTRTMIncrement009.blocks depth++false::false::true::false::PSTRTMIncrement009.blocks copied))
  let den := scanSegment false (denLeft left) denominator
    (PSTRTMIncrement009.blocks depth++false::false::true::false::PSTRTMIncrement009.blocks copied)
  let dep := scanSegment true (depthLeft left denominator) depth (true::false::PSTRTMIncrement009.blocks copied)
  let last := targetSegment (false::false::(PSTRTMRawNat010.leftBlocks depth.reverse++depthLeft left denominator)) copied
  exact ((start.join den).join dep).join last

def finishTrace (left denominator depth copied : List Bool) : List (MachineState 130) :=
  (finishSegment left denominator depth copied).trace

theorem finish_runsFrom (left denominator depth copied : List Bool) :
    PSTRTMSeq005.RunsFrom copyMachine (finishInitial left denominator depth copied)
      (finishTrace left denominator depth copied) (finishFinal left denominator depth copied) :=
  ⟨(finishSegment left denominator depth copied).head,(finishSegment left denominator depth copied).chain,
    (finishSegment left denominator depth copied).last,copy_halt _ _⟩

theorem finish_length_le (left denominator depth copied : List Bool) :
    (finishTrace left denominator depth copied).length ≤ 2*denominator.length+2*depth.length+16 := by
  simp only [finishTrace,finishSegment,Segment.join,PSTRTMOverlap132.glue_length,
    scanSegment,scan_length,sourceSegment,targetSegment,sourceTrace,targetTrace,List.length_cons,List.length_nil]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyFinish136
