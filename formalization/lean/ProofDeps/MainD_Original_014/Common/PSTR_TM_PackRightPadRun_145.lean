module
public import Common.PSTR_TM_PackRightPadCode_144

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackRightPadRun145
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackRightPadCode144 PSTRTMOverlap132

def scanTrace (left : List Bool) : List Bool → List (MachineState 40)
  | [] => [state 2 left [false,false],state 3 (false::left) [false],state 4 left [false,false]]
  | bit::later => [state 2 left (bit::true::(PSTRTMIncrement009.blocks later++[false,false])),
      state 3 (bit::left) (true::(PSTRTMIncrement009.blocks later++[false,false]))]++scanTrace (true::bit::left) later

theorem scan_head (left digits : List Bool) : (scanTrace left digits).head?=some
    (state 2 left (PSTRTMIncrement009.blocks digits++[false,false])) := by cases digits <;> rfl

theorem scan_last (left digits : List Bool) : (scanTrace left digits).getLast?=some
    (state 4 (PSTRTMRawNat010.leftBlocks digits.reverse++left) [false,false]) := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have hne : scanTrace (true::bit::left) later≠[] := by
      intro h
      have hh := scan_head (true::bit::left) later
      simp [h] at hh
    simp only [scanTrace,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem scan_chain (left digits : List Bool) :
    (scanTrace left digits).IsChain (fun before after => Turing.TM0.step padMachine before=some after) := by
  induction digits generalizing left with
  | nil => simp [scanTrace,List.isChain_cons_cons,Turing.TM0.step,padMachine,state,Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [scanTrace]
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,Turing.TM0.step,padMachine,state,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [scan_head,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step,padMachine,state,Turing.Tape.mk₂]

theorem scan_length (left digits : List Bool) : (scanTrace left digits).length=2*digits.length+3 := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih => simp only [scanTrace,List.length_append,List.length_cons,List.length_nil,ih]; omega

def copyTrace (left : List Bool) : List Bool → Bool → Bool → List Bool → List (MachineState 40)
  | [],first,second,tail => finishTrace first second left tail
  | bit::earlier,first,second,tail => glue
      (unitTrace bit first second (PSTRTMRawNat010.leftBlocks earlier++false::true::left) tail)
      (copyTrace left earlier bit true (bit::true::tail))

theorem copy_head (left previous : List Bool) (first second : Bool) (tail : List Bool) :
    (copyTrace left previous first second tail).head?=some
      (state 4 (PSTRTMRawNat010.leftBlocks previous++false::true::left) (first::second::tail)) := by
  cases previous with
  | nil => rfl
  | cons bit earlier => exact glue_head _ _ _ _ (unit_head _ _ _ _ _) (unit_last _ _ _ _ _) (copy_head _ _ _ _ _)
termination_by previous.length

theorem copy_last (left previous : List Bool) (first second : Bool) (tail : List Bool) :
    (copyTrace left previous first second tail).getLast?=some
      (state 40 left (false::false::true::false::(PSTRTMIncrement009.blocks previous.reverse++tail))) := by
  induction previous generalizing first second tail with
  | nil => rfl
  | cons bit earlier ih =>
    have h := glue_last
      (unitTrace bit first second (PSTRTMRawNat010.leftBlocks earlier++false::true::left) tail)
      (copyTrace left earlier bit true (bit::true::tail)) _ (ih _ _ _)
    simpa only [copyTrace,List.reverse_cons,PSTRTMIncrement009.blocks,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_assoc,List.cons_append,List.nil_append] using h

theorem copy_chain (left previous : List Bool) (first second : Bool) (tail : List Bool) :
    (copyTrace left previous first second tail).IsChain (fun before after => Turing.TM0.step padMachine before=some after) := by
  induction previous generalizing first second tail with
  | nil => exact finish_chain _ _ _ _
  | cons bit earlier ih => exact glue_chain padMachine _ _ _ (unit_chain _ _ _ _ _) (ih _ _ _) (unit_last _ _ _ _ _) (copy_head _ _ _ _ _)

theorem copy_length (left previous : List Bool) (first second : Bool) (tail : List Bool) :
    (copyTrace left previous first second tail).length=10*previous.length+13 := by
  induction previous generalizing first second tail with
  | nil => rfl
  | cons bit earlier ih =>
    simp only [copyTrace,glue_length,unitTrace,List.length_cons,List.length_nil,ih]
    omega

def preparePrefix (left digits : List Bool) : List (MachineState 40) :=
  [state 0 left (true::false::(PSTRTMIncrement009.blocks digits++[false,false])),
    state 1 (true::left) (false::(PSTRTMIncrement009.blocks digits++[false,false])),
    state 2 (false::true::left) (PSTRTMIncrement009.blocks digits++[false,false])]

theorem preparePrefix_chain (left digits : List Bool) :
    (preparePrefix left digits).IsChain (fun before after => Turing.TM0.step padMachine before=some after) := by
  simp [preparePrefix,List.isChain_cons_cons,Turing.TM0.step,padMachine,state,Turing.Tape.mk₂]

def prepareTrace (left digits : List Bool) : List (MachineState 40) :=
  glue (preparePrefix left digits) (scanTrace (false::true::left) digits)

theorem prepare_head (left digits : List Bool) : (prepareTrace left digits).head?=some
    (state 0 left (true::false::(PSTRTMIncrement009.blocks digits++[false,false]))) :=
  glue_head _ _ _ _ rfl rfl (scan_head _ _)

theorem prepare_last (left digits : List Bool) : (prepareTrace left digits).getLast?=some
    (state 4 (PSTRTMRawNat010.leftBlocks digits.reverse++false::true::left) [false,false]) :=
  glue_last _ _ _ (scan_last _ _)

theorem prepare_chain (left digits : List Bool) :
    (prepareTrace left digits).IsChain (fun before after => Turing.TM0.step padMachine before=some after) :=
  glue_chain padMachine _ _ _ (preparePrefix_chain _ _) (scan_chain _ _) rfl (scan_head _ _)

theorem prepare_length (left digits : List Bool) : (prepareTrace left digits).length=2*digits.length+5 := by
  simp only [prepareTrace,glue_length,preparePrefix,List.length_cons,List.length_nil,scan_length]
  omega

def padTrace (left digits : List Bool) : List (MachineState 40) :=
  glue (prepareTrace left digits) (copyTrace left digits.reverse false false [])

theorem state_right_zeros (q : Fin 41) (left right : List Bool) :
    state q left (right++[false,false])=state q left right := by
  have hz : Turing.ListBlank.mk (right++[false,false])=Turing.ListBlank.mk right := by
    simpa only [List.replicate_succ,List.replicate_zero] using PSTRTMPackFinish039.blank_false_suffix right 2
  simp only [state,Turing.Tape.mk₂,hz]

theorem pad_runsFrom (left digits : List Bool) :
    PSTRTMSeq005.RunsFrom padMachine (state 0 left (true::false::PSTRTMIncrement009.blocks digits))
      (padTrace left digits) (state 40 left (false::false::true::false::PSTRTMIncrement009.blocks digits)) := by
  refine ⟨?_,glue_chain padMachine _ _ _ (prepare_chain _ _) (copy_chain _ _ _ _ _) (prepare_last _ _) (copy_head _ _ _ _ _),?_,pad_halt _ _⟩
  · have h := glue_head (prepareTrace left digits) (copyTrace left digits.reverse false false []) _ _
      (prepare_head _ _) (prepare_last _ _) (copy_head _ _ _ _ _)
    have hz : state 0 left (true::false::(PSTRTMIncrement009.blocks digits++[false,false]))=
        state 0 left (true::false::PSTRTMIncrement009.blocks digits) :=
      state_right_zeros 0 left (true::false::PSTRTMIncrement009.blocks digits)
    rw [hz] at h
    exact h
  · simpa only [padTrace,List.reverse_reverse,List.append_nil] using
      glue_last (prepareTrace left digits) (copyTrace left digits.reverse false false []) _ (copy_last _ _ _ _ _)

theorem pad_length (left digits : List Bool) : (padTrace left digits).length=12*digits.length+17 := by
  simp only [padTrace,glue_length,prepare_length,copy_length,List.length_reverse]
  omega

/-- ENTIRE tape, actual original head position and ALL arbitrary left
cells. This right insertion uses real blank tape, not a supplied spacer. -/
theorem pad_final_tape (left digits : List Bool) :
    (state 40 left (false::false::true::false::PSTRTMIncrement009.blocks digits)).Tape=
      Turing.Tape.mk₂ left (false::false::true::false::PSTRTMIncrement009.blocks digits) := rfl

theorem pad_visitedSpace_le (left digits : List Bool) :
    visitedSpace padMachine (left.length+2+2*digits.length) (padTrace left digits)≤
      left.length+26*digits.length+37 := by
  have h := PSTRTMTrace002.visitedSpace_le padMachine (left.length+2+2*digits.length) (padTrace left digits)
  rw [pad_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackRightPadRun145
