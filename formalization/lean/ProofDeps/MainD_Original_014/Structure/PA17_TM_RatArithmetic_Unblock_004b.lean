module
public import Structure.PA17_TM_RatArithmetic_Unblock_004a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticUnblock004
open PSTRTMUnblock018


/-- The suffix is arbitrary, not assumed blank. The actual left guard is
read and crossed back; no byte beyond it is consumed or overwritten. -/
def doneTrace (archive suffix tail : List Bool) : List (MachineState 19) :=
  [state 2 (false::archive) (PSTRTMUnblockTrace019.rawWord tail ++ suffix),
   state 3 archive (false::(PSTRTMUnblockTrace019.rawWord tail ++ suffix)),
   state 19 (false::archive) (PSTRTMUnblockTrace019.rawWord tail ++ suffix)]

theorem done_chain (archive suffix tail : List Bool) :
    (doneTrace archive suffix tail).IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
  simp [doneTrace,List.isChain_cons_cons,Turing.TM0.step,unblockMachine,state,Turing.Tape.mk₂]

def undoTrace (archive suffix : List Bool) : List Bool → List Bool → List (MachineState 19)
  | [], tail => doneTrace archive suffix tail
  | bit::previous, tail =>
    inverseUnit bit tail.length (PSTRTMRawNat010.leftBlocks previous ++ false::archive) (tail ++ suffix) ++
      undoTrace archive suffix previous (bit::tail)

theorem undo_head (archive suffix previous tail : List Bool) :
    (undoTrace archive suffix previous tail).head? = some
      (state 2 (PSTRTMRawNat010.leftBlocks previous ++ false::archive) (PSTRTMUnblockTrace019.rawWord tail ++ suffix)) := by
  cases previous with
  | nil => rfl
  | cons bit previous =>
    simp [undoTrace,List.head?_append,inverseUnit_head,PSTRTMUnblockTrace019.rawWord,PSTRTMRawNat010.leftBlocks,List.append_assoc]

theorem undo_length (archive suffix previous tail : List Bool) :
    (undoTrace archive suffix previous tail).length =
      previous.length^2+2*tail.length*previous.length+9*previous.length+3 := by
  induction previous generalizing tail with
  | nil => rfl
  | cons bit previous ih =>
    simp only [undoTrace,List.length_append,inverseUnit_length,ih,List.length_cons]
    ring

theorem undo_last (archive suffix previous tail : List Bool) :
    (undoTrace archive suffix previous tail).getLast? = some
      (state 19 (false::archive) (PSTRTMUnblockTrace019.rawWord (previous.reverse ++ tail) ++ suffix)) := by
  induction previous generalizing tail with
  | nil => rfl
  | cons bit previous ih =>
    simp [undoTrace,List.getLast?_append,ih,List.reverse_cons,List.append_assoc]

theorem undo_chain (archive suffix previous tail : List Bool) :
    (undoTrace archive suffix previous tail).IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
  induction previous generalizing tail with
  | nil => exact done_chain archive suffix tail
  | cons bit previous ih =>
    rw [undoTrace]
    apply append_link _ _ _ _ (inverseUnit_chain bit tail.length _ _) (ih (bit::tail))
      (inverseUnit_last bit tail.length _ _) (undo_head archive suffix previous (bit::tail))
    simp [Turing.TM0.step,unblockMachine,state,Turing.Tape.mk₂,PSTRTMUnblockTrace019.rawWord,List.replicate_succ,List.append_assoc]

def seekTrace (archive suffix previous : List Bool) : List Bool → List (MachineState 19)
  | [] =>
    [state 0 (PSTRTMRawNat010.leftBlocks previous ++ false::archive) (false::false::suffix),
     state 1 (false::(PSTRTMRawNat010.leftBlocks previous ++ false::archive)) (false::suffix)]
  | bit::later =>
    state 0 (PSTRTMRawNat010.leftBlocks previous ++ false::archive)
      (PSTRTMIncrement009.blocks (bit::later) ++ false::false::suffix) ::
    state 1 (bit::(PSTRTMRawNat010.leftBlocks previous ++ false::archive))
      (true::(PSTRTMIncrement009.blocks later ++ false::false::suffix)) ::
    seekTrace archive suffix (bit::previous) later

theorem seek_head (archive suffix previous digits : List Bool) :
    (seekTrace archive suffix previous digits).head? = some
      (state 0 (PSTRTMRawNat010.leftBlocks previous ++ false::archive)
        (PSTRTMIncrement009.blocks digits ++ false::false::suffix)) := by
  cases digits <;> rfl

theorem seek_length (archive suffix previous digits : List Bool) :
    (seekTrace archive suffix previous digits).length = 2*digits.length+2 := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih => simp only [seekTrace,List.length_cons,ih]; omega

theorem seek_last (archive suffix previous digits : List Bool) :
    (seekTrace archive suffix previous digits).getLast? = some
      (state 1 (false::(PSTRTMRawNat010.leftBlocks (digits.reverse ++ previous) ++ false::archive)) (false::suffix)) := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih =>
    have hne : seekTrace archive suffix (bit::previous) later ≠ [] := by
      have hh := seek_head archive suffix (bit::previous) later
      intro h
      simp [h] at hh
    simp only [seekTrace,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem seek_chain (archive suffix previous digits : List Bool) :
    (seekTrace archive suffix previous digits).IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
  induction digits generalizing previous with
  | nil => simp [seekTrace,List.isChain_cons_cons,Turing.TM0.step,unblockMachine,state,Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [seekTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step,unblockMachine,state,Turing.Tape.mk₂,PSTRTMIncrement009.blocks]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [seek_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      simp [Turing.TM0.step,unblockMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks]
    · exact ih _

def framedTrace (archive digits suffix : List Bool) : List (MachineState 19) :=
  seekTrace archive suffix [] digits ++ undoTrace archive (false::suffix) digits.reverse []

theorem framed_length (archive digits suffix : List Bool) :
    (framedTrace archive digits suffix).length = digits.length^2+11*digits.length+5 := by
  simp only [framedTrace,List.length_append,seek_length,undo_length,List.length_reverse,List.length_nil]
  ring

theorem framed_chain (archive digits suffix : List Bool) :
    (framedTrace archive digits suffix).IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
  apply append_link _ _ _ _ (seek_chain archive suffix [] digits)
    (undo_chain archive (false::suffix) digits.reverse [])
    (seek_last archive suffix [] digits) (undo_head archive (false::suffix) digits.reverse [])
  simp [Turing.TM0.step,unblockMachine,state,Turing.Tape.mk₂,PSTRTMUnblockTrace019.rawWord]

theorem framed_runsFrom (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom unblockMachine
      (state 0 (false::archive) (PSTRTMIncrement009.blocks digits ++ false::false::suffix))
      (framedTrace archive digits suffix)
      (state 19 (false::archive) (PSTRTMUnblockTrace019.rawWord digits ++ false::suffix)) := by
  refine ⟨?_,framed_chain archive digits suffix,?_,PSTRTMUnblockTrace019.unblock_halt _ _⟩
  · simp [framedTrace,List.head?_append,seek_head,PSTRTMRawNat010.leftBlocks]
  · simp [framedTrace,List.getLast?_append,undo_last]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticUnblock004
