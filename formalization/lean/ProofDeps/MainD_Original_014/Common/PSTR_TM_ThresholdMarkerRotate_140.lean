module
public import Common.PSTR_TM_ThresholdBackup_139

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdMarkerRotate140
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMOverlap132

/-- Move the real marker10 left across an actual00 and then a flagged
field. This is the threshold loader's DEN/DEPTH separator transport,
not a free permutation of fields or an allocation/copy oracle. Each
source bit is held in the finite control for twelve ordinary actions. -/
def rotateMachine : Machine 29 := fun q symbol =>
  match q.val with
  | 0 => some (1,.write false)
  | 1 => some (2,.move .left)
  | 2 => some (3,.move .left)
  | 3 => some (4,.write true)
  | 4 => some (5,.move .left)
  | 5 => some (if symbol then 6 else 29,if symbol then .move .left else .move .right)
  | 6 => some (if symbol then 18 else 8,.write true)
  | 8 => some (9,.move .right)
  | 9 => some (10,.write false)
  | 10 => some (11,.move .right)
  | 11 => some (12,.write false)
  | 12 => some (13,.move .right)
  | 13 => some (14,.write true)
  | 14 => some (15,.move .left)
  | 15 => some (16,.move .left)
  | 16 => some (4,.move .left)
  | 18 => some (19,.move .right)
  | 19 => some (20,.write false)
  | 20 => some (21,.move .right)
  | 21 => some (22,.write true)
  | 22 => some (23,.move .right)
  | 23 => some (24,.write true)
  | 24 => some (25,.move .left)
  | 25 => some (26,.move .left)
  | 26 => some (4,.move .left)
  | _ => none

def state (q : Fin 30) (left right : List Bool) : MachineState 29 := ⟨q,Turing.Tape.mk₂ left right⟩

def phase (bit : Bool) (offset : Fin 9) : Fin 30 :=
  ⟨(if bit then 18 else 8)+offset.val,by split <;> have h := offset.isLt <;> omega⟩

def unitTrace (bit : Bool) (left tail : List Bool) : List (MachineState 29) :=
  [state 4 (true::bit::left) (true::false::tail),
    state 5 (bit::left) (true::true::false::tail),
    state 6 left (bit::true::true::false::tail),
    state (phase bit 0) left (true::true::true::false::tail),
    state (phase bit 1) (true::left) (true::true::false::tail),
    state (phase bit 2) (true::left) (false::true::false::tail),
    state (phase bit 3) (false::true::left) (true::false::tail),
    state (phase bit 4) (false::true::left) (bit::false::tail),
    state (phase bit 5) (bit::false::true::left) (false::tail),
    state (phase bit 6) (bit::false::true::left) (true::tail),
    state (phase bit 7) (false::true::left) (bit::true::tail),
    state (phase bit 8) (true::left) (false::bit::true::tail),
    state 4 left (true::false::bit::true::tail)]

theorem unit_head (bit : Bool) (left tail : List Bool) :
    (unitTrace bit left tail).head?=some (state 4 (true::bit::left) (true::false::tail)) := rfl

theorem unit_last (bit : Bool) (left tail : List Bool) :
    (unitTrace bit left tail).getLast?=some (state 4 left (true::false::bit::true::tail)) := rfl

theorem unit_chain (bit : Bool) (left tail : List Bool) :
    (unitTrace bit left tail).IsChain (fun before after => Turing.TM0.step rotateMachine before=some after) := by
  cases bit <;> simp [unitTrace,List.isChain_cons_cons,Turing.TM0.step,rotateMachine,phase,state,Turing.Tape.mk₂]

def loopTrace (archive : List Bool) : List Bool → List Bool → List (MachineState 29)
  | [],tail => [state 4 (false::archive) (true::false::tail),
      state 5 archive (false::true::false::tail),state 29 (false::archive) (true::false::tail)]
  | bit::later,tail => glue
      (unitTrace bit (PSTRTMRawNat010.leftBlocks later++false::archive) tail)
      (loopTrace archive later (bit::true::tail))

theorem loop_head (archive previous tail : List Bool) :
    (loopTrace archive previous tail).head?=some
      (state 4 (PSTRTMRawNat010.leftBlocks previous++false::archive) (true::false::tail)) := by
  cases previous with
  | nil => rfl
  | cons bit later =>
    exact glue_head _ _ _ _ (unit_head _ _ _) (unit_last _ _ _) (loop_head _ _ _)
termination_by previous.length

theorem loop_last (archive previous tail : List Bool) :
    (loopTrace archive previous tail).getLast?=some
      (state 29 (false::archive) (true::false::(PSTRTMIncrement009.blocks previous.reverse++tail))) := by
  induction previous generalizing tail with
  | nil => rfl
  | cons bit later ih =>
    have h := glue_last (unitTrace bit (PSTRTMRawNat010.leftBlocks later++false::archive) tail)
      (loopTrace archive later (bit::true::tail)) _ (ih _)
    simpa only [loopTrace,List.reverse_cons,PSTRTMIncrement009.blocks,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_assoc,List.cons_append,List.nil_append] using h

theorem loop_chain (archive previous tail : List Bool) :
    (loopTrace archive previous tail).IsChain (fun before after => Turing.TM0.step rotateMachine before=some after) := by
  induction previous generalizing tail with
  | nil => simp [loopTrace,List.isChain_cons_cons,Turing.TM0.step,rotateMachine,state,Turing.Tape.mk₂]
  | cons bit later ih =>
    exact glue_chain rotateMachine _ _ _ (unit_chain _ _ _) (ih _) (unit_last _ _ _) (loop_head _ _ _)

theorem loop_length (archive previous tail : List Bool) :
    (loopTrace archive previous tail).length=12*previous.length+3 := by
  induction previous generalizing tail with
  | nil => rfl
  | cons bit later ih =>
    simp only [loopTrace,glue_length,unitTrace,List.length_cons,List.length_nil,ih]
    omega

def initializeTrace (archive previous suffix : List Bool) : List (MachineState 29) :=
  let left := PSTRTMRawNat010.leftBlocks previous++false::archive
  [state 0 (false::false::left) (true::false::suffix),
    state 1 (false::false::left) (false::false::suffix),
    state 2 (false::left) (false::false::false::suffix),
    state 3 left (false::false::false::false::suffix),
    state 4 left (true::false::false::false::suffix)]

theorem initialize_head (archive previous suffix : List Bool) :
    (initializeTrace archive previous suffix).head?=some
      (state 0 (false::false::(PSTRTMRawNat010.leftBlocks previous++false::archive)) (true::false::suffix)) := rfl

theorem initialize_last (archive previous suffix : List Bool) :
    (initializeTrace archive previous suffix).getLast?=some
      (state 4 (PSTRTMRawNat010.leftBlocks previous++false::archive) (true::false::false::false::suffix)) := rfl

theorem initialize_chain (archive previous suffix : List Bool) :
    (initializeTrace archive previous suffix).IsChain
      (fun before after => Turing.TM0.step rotateMachine before=some after) := by
  simp [initializeTrace,List.isChain_cons_cons,Turing.TM0.step,rotateMachine,state,Turing.Tape.mk₂]

def rotateTrace (archive digits suffix : List Bool) : List (MachineState 29) :=
  glue (initializeTrace archive digits.reverse suffix) (loopTrace archive digits.reverse (false::false::suffix))

def initial (archive digits suffix : List Bool) : MachineState 29 :=
  state 0 (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) (true::false::suffix)

def final (archive digits suffix : List Bool) : MachineState 29 :=
  state 29 (false::archive) (true::false::(PSTRTMIncrement009.blocks digits++false::false::suffix))

theorem rotate_runsFrom (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom rotateMachine (initial archive digits suffix)
      (rotateTrace archive digits suffix) (final archive digits suffix) := by
  refine ⟨glue_head _ _ _ _ (initialize_head _ _ _) (initialize_last _ _ _) (loop_head _ _ _),
    glue_chain rotateMachine _ _ _ (initialize_chain _ _ _) (loop_chain _ _ _) (initialize_last _ _ _) (loop_head _ _ _),?_,?_⟩
  · simpa only [rotateTrace,final,List.reverse_reverse] using
      glue_last (initializeTrace archive digits.reverse suffix)
        (loopTrace archive digits.reverse (false::false::suffix)) _ (loop_last _ _ _)
  · simp [final,Turing.TM0.step,rotateMachine,state]

theorem rotate_length (archive digits suffix : List Bool) :
    (rotateTrace archive digits suffix).length=12*digits.length+7 := by
  simp only [rotateTrace,glue_length,initializeTrace,List.length_cons,List.length_nil,loop_length,List.length_reverse]
  omega

/-- Same real trace, original visitedSpace. The charged initial cells
include every real archive/suffix cell; the machine never reads a cost
certificate, source length or externally supplied workzone. -/
theorem rotate_visitedSpace_le (archive digits suffix : List Bool) :
    visitedSpace rotateMachine (archive.length+suffix.length+2*digits.length+5)
      (rotateTrace archive digits suffix)≤archive.length+suffix.length+26*digits.length+20 := by
  have h := PSTRTMTrace002.visitedSpace_le rotateMachine
    (archive.length+suffix.length+2*digits.length+5) (rotateTrace archive digits suffix)
  rw [rotate_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdMarkerRotate140
