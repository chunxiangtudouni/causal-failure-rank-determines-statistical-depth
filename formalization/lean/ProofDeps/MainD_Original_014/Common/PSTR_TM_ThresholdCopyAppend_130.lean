module
public import Common.PSTR_TM_ThresholdCopyRoundLift_129

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyAppend130
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCopyCode126 PSTRTMThresholdCopyRoundLift129

def savedState (bit : Bool) (q : Fin 40) (left right : List Bool) : MachineState 130 :=
  state (phaseLabel bit q) left right

/-- Actual target flag scan returns LEFT onto the true blank data cell,
so the saved source bit is physically appended; this is not a list update. -/
def seekTrace (bit : Bool) (left : List Bool) : List Bool → List (MachineState 130)
  | [] => [savedState bit 11 left [false,false],savedState bit 12 (false::left) [false],savedState bit 13 left [false,false]]
  | digit::later => [savedState bit 11 left (digit::true::(PSTRTMIncrement009.blocks later++[false,false])),
      savedState bit 12 (digit::left) (true::(PSTRTMIncrement009.blocks later++[false,false]))] ++
      seekTrace bit (true::digit::left) later

theorem seek_head (bit : Bool) (left digits : List Bool) : (seekTrace bit left digits).head?=some
    (savedState bit 11 left (PSTRTMIncrement009.blocks digits++[false,false])) := by cases digits <;> rfl

theorem seek_last (bit : Bool) (left digits : List Bool) : (seekTrace bit left digits).getLast?=some
    (savedState bit 13 (PSTRTMRawNat010.leftBlocks digits.reverse++left) [false,false]) := by
  induction digits generalizing left with
  | nil => rfl
  | cons digit later ih =>
    have hne : seekTrace bit (true::digit::left) later≠[] := by
      intro h
      have hh := seek_head bit (true::digit::left) later
      simp [h] at hh
    simp only [seekTrace,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem seek_length (bit : Bool) (left digits : List Bool) : (seekTrace bit left digits).length=2*digits.length+3 := by
  induction digits generalizing left with
  | nil => rfl
  | cons digit later ih => simp only [seekTrace,List.length_append,List.length_cons,List.length_nil,ih]; omega

theorem seek_chain (bit : Bool) (left digits : List Bool) :
    (seekTrace bit left digits).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  induction digits generalizing left with
  | nil => cases bit <;> simp [seekTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,savedState,phaseLabel,state,Turing.Tape.mk₂]
  | cons digit later ih =>
    rw [seekTrace]
    apply List.IsChain.append
    · cases bit <;> simp [List.isChain_cons_cons,Turing.TM0.step,copyMachine,savedState,phaseLabel,state,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [seek_head,Option.mem_some_iff] at ha
      subst before
      subst after
      cases bit <;> simp [Turing.TM0.step,copyMachine,savedState,phaseLabel,state,Turing.Tape.mk₂]

def writeTrace (bit : Bool) (left : List Bool) : List (MachineState 130) :=
  [savedState bit 14 left [bit,false],savedState bit 15 (bit::left) [false],
    savedState bit 16 (bit::left) [true],savedState bit 17 (true::bit::left) []]

theorem write_chain (bit : Bool) (left : List Bool) :
    (writeTrace bit left).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  cases bit <;> simp [writeTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,savedState,phaseLabel,state,Turing.Tape.mk₂]

def appendTrace (bit : Bool) (left digits : List Bool) : List (MachineState 130) :=
  seekTrace bit left digits++writeTrace bit (PSTRTMRawNat010.leftBlocks digits.reverse++left)

theorem append_head (bit : Bool) (left digits : List Bool) : (appendTrace bit left digits).head?=some
    (savedState bit 11 left (PSTRTMIncrement009.blocks digits++[false,false])) := by
  simp only [appendTrace,List.head?_append,seek_head,Option.some_or]

theorem append_last (bit : Bool) (left digits : List Bool) : (appendTrace bit left digits).getLast?=some
    (savedState bit 17 (PSTRTMRawNat010.leftBlocks (digits++[bit]).reverse++left) []) := by
  simp [appendTrace,writeTrace,PSTRTMRawNat010.leftBlocks,List.reverse_append]

theorem append_length (bit : Bool) (left digits : List Bool) : (appendTrace bit left digits).length=2*digits.length+7 := by
  simp only [appendTrace,List.length_append,seek_length,writeTrace,List.length_cons,List.length_nil]

theorem append_chain (bit : Bool) (left digits : List Bool) :
    (appendTrace bit left digits).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  apply List.IsChain.append (seek_chain bit left digits) (write_chain bit _)
  intro before hb after ha
  rw [seek_last] at hb
  simp only [writeTrace,List.head?_cons,Option.mem_some_iff] at ha
  have he := Option.mem_some_iff.mp hb
  subst before
  subst after
  cases bit <;> simp [Turing.TM0.step,copyMachine,savedState,phaseLabel,state,Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyAppend130
