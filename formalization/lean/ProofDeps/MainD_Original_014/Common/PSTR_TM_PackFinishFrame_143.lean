module
public import Common.PSTR_TM_ThresholdDenBackup_142
public import Common.PSTR_TM_PackFinish_039

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFinishFrame143
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036

/-- SAME194-label packer: the existing physical finish/rewind stops at
a real false guard and retains every cell behind it. No right suffix is
promised: the actual packer finish reads real blanks to its right. -/
def rewindInitial (archive : List Bool) : List Bool → List Bool → MachineState 193
  | [],right => state 190 archive (false::right)
  | bit::previous,right => state 190 (bit::(PSTRTMRawNat010.leftBlocks previous++false::archive)) (true::right)

def rewindTrace (archive : List Bool) : List Bool → List Bool → List (MachineState 193)
  | [],right => [state 190 archive (false::right),state 192 (false::archive) right]
  | bit::previous,right =>
    state 190 (bit::(PSTRTMRawNat010.leftBlocks previous++false::archive)) (true::right)::
      state 191 (PSTRTMRawNat010.leftBlocks previous++false::archive) (bit::true::right)::
        rewindTrace archive previous (bit::true::right)

theorem rewind_head (archive previous right : List Bool) :
    (rewindTrace archive previous right).head?=some (rewindInitial archive previous right) := by cases previous <;> rfl

theorem rewind_length (archive previous right : List Bool) :
    (rewindTrace archive previous right).length=2*previous.length+2 := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih => simp only [rewindTrace,List.length_cons,ih]; omega

theorem rewind_chain (archive previous right : List Bool) :
    (rewindTrace archive previous right).IsChain (fun before after => Turing.TM0.step packMachine before=some after) := by
  induction previous generalizing right with
  | nil => simp [rewindTrace,List.isChain_cons_cons,Turing.TM0.step,packMachine,state,Turing.Tape.mk₂]
  | cons bit previous ih =>
    rw [rewindTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step,packMachine,state,Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [rewind_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      cases previous <;> simp [rewindInitial,PSTRTMRawNat010.leftBlocks,Turing.TM0.step,packMachine,state,Turing.Tape.mk₂]
    · exact ih _

theorem rewind_last (archive previous right : List Bool) :
    (rewindTrace archive previous right).getLast?=some
      (state 192 (false::archive) (PSTRTMIncrement009.blocks previous.reverse++right)) := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have hne : rewindTrace archive previous (bit::true::right)≠[] := by
      intro h
      have hl := rewind_length archive previous (bit::true::right)
      simp [h] at hl
    simp only [rewindTrace,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMIncrement009.blocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

def clearFront (left : List Bool) : List (MachineState 193) :=
  [state 0 left [false,false,true,false],state 1 (false::left) [false,true,false],
    state 3 (false::false::left) [true,false],state 4 (true::false::false::left) [false],
    state 5 (false::true::false::false::left) [],state 6 (false::false::true::false::false::left) [],
    state 8 (false::true::false::false::left) [false]]

def clearBack (left : List Bool) : List (MachineState 193) :=
  [state 8 (false::true::false::false::left) [false],state 9 (true::false::false::left) [false,false],
    state 186 (false::false::left) [true,false,false],state 187 (false::false::left) [false,false,false],
    state 188 (false::left) [false,false,false,false],state 189 left [false,false,false,false,false]]

theorem clearFront_chain (left : List Bool) :
    (clearFront left).IsChain (fun before after => Turing.TM0.step packMachine before=some after) := by
  simp [clearFront,List.isChain_cons_cons,Turing.TM0.step,packMachine,state,Turing.Tape.mk₂]

theorem clearBack_chain (left : List Bool) :
    (clearBack left).IsChain (fun before after => Turing.TM0.step packMachine before=some after) := by
  simp [clearBack,List.isChain_cons_cons,Turing.TM0.step,packMachine,state,Turing.Tape.mk₂]

def clearTrace (left : List Bool) : List (MachineState 193) := PSTRTMOverlap132.glue (clearFront left) (clearBack left)

theorem clear_head (left : List Bool) :
    (clearTrace left).head?=some (state 0 left [false,false,true,false]) := rfl

theorem clear_last (left : List Bool) :
    (clearTrace left).getLast?=some (state 189 left [false,false,false,false,false]) := rfl

theorem clear_length (left : List Bool) : (clearTrace left).length=12 := rfl

theorem clear_chain (left : List Bool) :
    (clearTrace left).IsChain (fun before after => Turing.TM0.step packMachine before=some after) :=
  PSTRTMOverlap132.glue_chain packMachine _ _ _ (clearFront_chain left) (clearBack_chain left) rfl rfl

theorem clear_advance (archive previous : List Bool) :
    Turing.TM0.step packMachine
      (state 189 (PSTRTMRawNat010.leftBlocks previous++false::archive) [false,false,false,false,false])=
      some (rewindInitial archive previous [false,false,false,false,false]) := by
  cases previous <;> simp [rewindInitial,PSTRTMRawNat010.leftBlocks,Turing.TM0.step,packMachine,state,Turing.Tape.mk₂]

def finishTrace (archive previous : List Bool) : List (MachineState 193) :=
  clearTrace (PSTRTMRawNat010.leftBlocks previous++false::archive)++
    rewindTrace archive previous [false,false,false,false,false]

theorem finish_head (archive previous : List Bool) :
    (finishTrace archive previous).head?=some
      (state 0 (PSTRTMRawNat010.leftBlocks previous++false::archive) [false,false,true,false]) := by
  simp only [finishTrace,List.head?_append,clear_head,Option.some_or]

theorem finish_last (archive previous : List Bool) :
    (finishTrace archive previous).getLast?=some
      (state 192 (false::archive) (PSTRTMIncrement009.blocks previous.reverse++[false,false,false,false,false])) := by
  simp only [finishTrace,List.getLast?_append,rewind_last,Option.some_or]

theorem finish_length (archive previous : List Bool) :
    (finishTrace archive previous).length=2*previous.length+14 := by
  simp only [finishTrace,List.length_append,clear_length,rewind_length]
  omega

theorem finish_chain (archive previous : List Bool) :
    (finishTrace archive previous).IsChain (fun before after => Turing.TM0.step packMachine before=some after) := by
  apply (clear_chain _).append (rewind_chain archive previous _)
  intro before hb after ha
  simp only [clear_last,Option.mem_some_iff] at hb
  simp only [rewind_head,Option.mem_some_iff] at ha
  subst before
  subst after
  exact clear_advance archive previous

theorem finish_runsFrom (archive previous : List Bool) :
    PSTRTMSeq005.RunsFrom packMachine
      (state 0 (PSTRTMRawNat010.leftBlocks previous++false::archive) [false,false,true,false])
      (finishTrace archive previous)
      (state 192 (false::archive) (PSTRTMIncrement009.blocks previous.reverse++[false,false,false,false,false])) :=
  ⟨finish_head _ _,finish_chain _ _,finish_last _ _,pack_halt _ _⟩

theorem finish_final_tape (archive previous : List Bool) :
    (state 192 (false::archive) (PSTRTMIncrement009.blocks previous.reverse++[false,false,false,false,false])).Tape=
      Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks previous.reverse) := by
  have hr : Turing.ListBlank.mk
      (PSTRTMIncrement009.blocks previous.reverse++[false,false,false,false,false])=
      Turing.ListBlank.mk (PSTRTMIncrement009.blocks previous.reverse) := by
    simpa only [List.replicate_succ,List.replicate_zero] using
      PSTRTMPackFinish039.blank_false_suffix (PSTRTMIncrement009.blocks previous.reverse) 5
  simp only [state,Turing.Tape.mk₂,hr]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFinishFrame143
