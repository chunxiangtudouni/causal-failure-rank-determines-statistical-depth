module
public import Common.PSTR_TM_ThresholdCopyLift_127

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyInit128
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCopyCode126 PSTRTMThresholdCopyLift127

/-- An actual forward scan through the EOF flag, omitting only its
following endpoint so the next field scan can take that real transition.
This avoids duplicating a shared configuration as an imaginary self-step. -/
def cursorPrefix (left : List Bool) : List Bool → List Bool → List (MachineState 2)
  | [],tail => [PSTRTMThresholdCursor115.state 0 left (false::false::tail),
      PSTRTMThresholdCursor115.state 1 (false::left) (false::tail)]
  | bit::later,tail => [PSTRTMThresholdCursor115.state 0 left
      (bit::true::(PSTRTMIncrement009.blocks later++false::false::tail)),
      PSTRTMThresholdCursor115.state 1 (bit::left)
        (true::(PSTRTMIncrement009.blocks later++false::false::tail))] ++
      cursorPrefix (true::bit::left) later tail

theorem cursorPrefix_head (left digits tail : List Bool) : (cursorPrefix left digits tail).head?=some
    (PSTRTMThresholdCursor115.state 0 left (PSTRTMIncrement009.blocks digits++false::false::tail)) := by cases digits <;> rfl

theorem cursorPrefix_last (left digits tail : List Bool) : (cursorPrefix left digits tail).getLast?=some
    (PSTRTMThresholdCursor115.state 1 (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (false::tail)) := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have hne : cursorPrefix (true::bit::left) later tail≠[] := by
      intro h
      have hh := cursorPrefix_head (true::bit::left) later tail
      simp [h] at hh
    simp only [cursorPrefix,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem cursorPrefix_length (left digits tail : List Bool) : (cursorPrefix left digits tail).length=2*digits.length+2 := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih => simp only [cursorPrefix,List.length_append,List.length_cons,List.length_nil,ih]; omega

theorem cursorPrefix_chain (left digits tail : List Bool) :
    (cursorPrefix left digits tail).IsChain
      (fun before after => Turing.TM0.step PSTRTMThresholdCursor115.cursorMachine before=some after) := by
  induction digits generalizing left with
  | nil => simp [cursorPrefix,List.isChain_cons_cons,Turing.TM0.step,PSTRTMThresholdCursor115.cursorMachine,
      PSTRTMThresholdCursor115.state,Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [cursorPrefix]
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,Turing.TM0.step,PSTRTMThresholdCursor115.cursorMachine,
        PSTRTMThresholdCursor115.state,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [cursorPrefix_head,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step,PSTRTMThresholdCursor115.cursorMachine,PSTRTMThresholdCursor115.state,Turing.Tape.mk₂]

def numLeft (archive numerator : List Bool) : List Bool :=
  false::false::(PSTRTMRawNat010.leftBlocks numerator.reverse++false::archive)

def markerLeft (archive numerator : List Bool) : List Bool := false::true::numLeft archive numerator

def depthLeft (archive numerator denominator : List Bool) : List Bool :=
  false::false::(PSTRTMRawNat010.leftBlocks denominator.reverse++markerLeft archive numerator)

def endLeft (archive numerator denominator depth : List Bool) : List Bool :=
  false::false::(PSTRTMRawNat010.leftBlocks depth.reverse++depthLeft archive numerator denominator)

def markerTrace (archive numerator denominator depth : List Bool) : List (MachineState 130) :=
  [state 3 (true::numLeft archive numerator)
    (false::(PSTRTMIncrement009.blocks denominator++false::false::PSTRTMIncrement009.blocks depth))]

def allocateTrace (archive numerator denominator depth : List Bool) : List (MachineState 130) :=
  let left := endLeft archive numerator denominator depth
  [state 9 left [true],state 10 (true::left) [],state 11 (true::left) [false],
    state 12 (false::true::left) [],state 13 (true::left) [false],
    state 14 left [true,false],state 15
      (false::(PSTRTMRawNat010.leftBlocks depth.reverse++depthLeft archive numerator denominator)) [false,true,false]]

def denBridge (archive numerator denominator depth : List Bool) : List (MachineState 130) :=
  [state 21 (false::(PSTRTMRawNat010.leftBlocks denominator.reverse++markerLeft archive numerator))
    (false::(PSTRTMIncrement009.blocks depth++[false,false,true,false]))]

def numBridge (archive numerator denominator depth : List Bool) : List (MachineState 130) :=
  let tail := PSTRTMIncrement009.blocks denominator++false::false::(PSTRTMIncrement009.blocks depth++[false,false,true,false])
  [state 27 (true::numLeft archive numerator) (false::tail),
    state 28 (numLeft archive numerator) (true::false::tail),
    state 29 (false::(PSTRTMRawNat010.leftBlocks numerator.reverse++false::archive)) (false::true::false::tail)]

/-- All forward scans, real marker allocation, and all three real
backward shuttles. The source field is not supplied again at the end. -/
def chunks (archive numerator denominator depth : List Bool) : List (List (MachineState 130)) :=
  [(PSTRTMThresholdCursor115.cursorTrace (false::archive) numerator
      (true::false::(PSTRTMIncrement009.blocks denominator++false::false::PSTRTMIncrement009.blocks depth))).map (liftCursor 0),
    markerTrace archive numerator denominator depth,
    (cursorPrefix (markerLeft archive numerator) denominator (PSTRTMIncrement009.blocks depth)).map (liftCursor 1),
    (PSTRTMThresholdCursor115.cursorTrace (depthLeft archive numerator denominator) depth []).map (liftCursor 2),
    allocateTrace archive numerator denominator depth,
    (PSTRTMPairRewind105.fullTrace
      (false::(PSTRTMRawNat010.leftBlocks denominator.reverse++markerLeft archive numerator)) depth.reverse [false,false,true,false]).map (liftRewind 0),
    denBridge archive numerator denominator depth,
    (PSTRTMPairRewind105.fullTrace (true::numLeft archive numerator) denominator.reverse
      (false::false::(PSTRTMIncrement009.blocks depth++[false,false,true,false]))).map (liftRewind 1),
    numBridge archive numerator denominator depth,
    (PSTRTMPairRewind105.fullTrace archive numerator.reverse
      (false::false::true::false::(PSTRTMIncrement009.blocks denominator++false::false::
        (PSTRTMIncrement009.blocks depth++[false,false,true,false])))).map (liftRewind 2)]

def initializeTrace (archive numerator denominator depth : List Bool) : List (MachineState 130) :=
  (chunks archive numerator denominator depth).flatten

def initializeFinal (archive numerator denominator depth : List Bool) : MachineState 130 :=
  state 34 (false::archive) (PSTRTMThresholdRewind124.sourceWord numerator denominator depth++[false,false,true,false])

theorem initialize_head (archive numerator denominator depth : List Bool) :
    (initializeTrace archive numerator denominator depth).head?=some
      (state 0 (false::archive) (PSTRTMThresholdRewind124.sourceWord numerator denominator depth)) := by
  simp only [initializeTrace,chunks,List.flatten_cons,List.flatten_nil,List.head?_append,List.head?_map,
    PSTRTMThresholdCursor115.cursor_head,Option.map_some,Option.some_or]
  simp only [liftCursor,cursorLabel,PSTRTMThresholdCursor115.state,state,PSTRTMThresholdRewind124.sourceWord,
    List.append_assoc,List.cons_append,List.nil_append]
  rfl

theorem initialize_last (archive numerator denominator depth : List Bool) :
    (initializeTrace archive numerator denominator depth).getLast?=some (initializeFinal archive numerator denominator depth) := by
  simp only [initializeTrace,chunks,List.flatten_cons,List.flatten_nil,List.getLast?_append,List.getLast?_nil,
    List.getLast?_map,PSTRTMPairRewind105.full_last,List.reverse_reverse,Option.map_some]
  simp only [initializeFinal,liftRewind,rewindLabel,PSTRTMMulRewind085.state,state,
    PSTRTMThresholdRewind124.sourceWord,List.append_assoc,List.cons_append,List.nil_append]
  rfl

theorem initialize_length (archive numerator denominator depth : List Bool) :
    (initializeTrace archive numerator denominator depth).length=4*(numerator.length+denominator.length+depth.length)+29 := by
  simp only [initializeTrace,chunks,List.flatten_cons,List.flatten_nil,List.length_append,List.length_map,
    PSTRTMThresholdCursor115.cursor_length,cursorPrefix_length,PSTRTMPairRewind105.full_length,List.length_reverse,
    markerTrace,allocateTrace,denBridge,numBridge,List.length_cons,List.length_nil]
  omega

private theorem cursor_nonempty (left digits tail : List Bool) :
    PSTRTMThresholdCursor115.cursorTrace left digits tail≠[] := by
  intro h
  have hh := congrArg List.head? h
  simp only [PSTRTMThresholdCursor115.cursor_head,List.head?_nil,reduceCtorEq] at hh

private theorem cursorPrefix_nonempty (left digits tail : List Bool) : cursorPrefix left digits tail≠[] := by
  intro h
  have hh := congrArg List.head? h
  simp only [cursorPrefix_head,List.head?_nil,reduceCtorEq] at hh

private theorem rewind_nonempty (archive earlier tail : List Bool) : PSTRTMPairRewind105.fullTrace archive earlier tail≠[] := by
  intro h
  have hh := congrArg List.head? h
  simp only [PSTRTMPairRewind105.full_head,List.head?_nil,reduceCtorEq] at hh

private theorem blank_append_two (bits : List Bool) :
    Turing.ListBlank.mk (bits++[false,false])=Turing.ListBlank.mk bits := by
  calc
    _ = Turing.ListBlank.mk ((bits++[false])++[false]) := by rw [List.append_assoc]; rfl
    _ = Turing.ListBlank.mk (bits++[false]) := PSTRTMRawNat010.blank_append_false _
    _ = Turing.ListBlank.mk bits := PSTRTMRawNat010.blank_append_false _

/-- Prefix of the SAME fixed131-label copier. HALT is not asserted at34:
that actual control reads the source bit and starts the subsequent copy loop. -/
theorem initialize_chain (archive numerator denominator depth : List Bool) :
    (initializeTrace archive numerator denominator depth).IsChain
      (fun before after => Turing.TM0.step copyMachine before=some after) := by
  apply (List.isChain_flatten ?_).mpr
  · constructor
    · simp only [chunks,List.forall_mem_cons]
      refine ⟨cursor_chain 0 _ (PSTRTMThresholdCursor115.cursor_chain _ _ _),?_,
        cursor_chain 1 _ (cursorPrefix_chain _ _ _),
        cursor_chain 2 _ (PSTRTMThresholdCursor115.cursor_chain _ _ _),?_,
        rewind_chain 0 _ (PSTRTMPairRewind105.full_chain _ _ _),?_,
        rewind_chain 1 _ (PSTRTMPairRewind105.full_chain _ _ _),?_,
        rewind_chain 2 _ (PSTRTMPairRewind105.full_chain _ _ _),(by simp)⟩
      · simp [markerTrace]
      · simp [allocateTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,endLeft,Turing.Tape.mk₂]
      · simp [denBridge]
      · simp [numBridge,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,numLeft,Turing.Tape.mk₂]
    · simp only [chunks,List.isChain_cons_cons,List.isChain_singleton,List.getLast?_map,List.head?_map,
        PSTRTMThresholdCursor115.cursor_last,PSTRTMThresholdCursor115.cursor_head,cursorPrefix_head,cursorPrefix_last,
        PSTRTMPairRewind105.full_last,PSTRTMPairRewind105.full_head,List.reverse_reverse,Option.map_some,
        markerTrace,allocateTrace,denBridge,numBridge,List.getLast?_cons_cons,List.getLast?_singleton,List.head?_cons,
        and_true]
      repeat' constructor
      all_goals intro before hb after ha
      all_goals simp only [Option.mem_some_iff] at hb ha
      all_goals subst before; subst after
      all_goals simp [Turing.TM0.step,copyMachine,state,liftCursor,cursorLabel,liftRewind,rewindLabel,
        PSTRTMThresholdCursor115.state,PSTRTMMulRewind085.state,numLeft,markerLeft,depthLeft,endLeft,
        Turing.Tape.mk₂,blank_append_two]
  · simp [chunks,cursor_nonempty,cursorPrefix_nonempty,rewind_nonempty,markerTrace,allocateTrace,denBridge,numBridge]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyInit128
