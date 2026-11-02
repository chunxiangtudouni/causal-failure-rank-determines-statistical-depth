module
public import Structure.PA17_TM_Division_Codec_003b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
open PaperProofs.Common.Native.RationalControllerComputation

/-- A real marker seeker. The zero count in the trace is a proof index;
the fixed machine scans until it actually reads the allocated true marker. -/
def seekMarkerMachine : Machine 2 := fun q symbol =>
  match q.val with
  | 0 => if symbol then some (1, .write false) else some (0, .move .right)
  | 1 => some (2, .move .right)
  | _ => none

def seekMarkerState (q : Fin 3) (left right : List Bool) : MachineState 2 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

def seekMarkerTrace (left : List Bool) : Nat → List Bool → List (MachineState 2)
  | 0, tail =>
      [seekMarkerState 0 left (true :: tail),
       seekMarkerState 1 left (false :: tail),
       seekMarkerState 2 (false :: left) tail]
  | count + 1, tail =>
      seekMarkerState 0 left (false :: (List.replicate count false ++ true :: tail)) ::
        seekMarkerTrace (false :: left) count tail

theorem seekMarkerTrace_head (left : List Bool) (count : Nat) (tail : List Bool) :
    (seekMarkerTrace left count tail).head? =
      some (seekMarkerState 0 left (List.replicate count false ++ true :: tail)) := by
  cases count <;> rfl

theorem seekMarkerTrace_last (left : List Bool) (count : Nat) (tail : List Bool) :
    (seekMarkerTrace left count tail).getLast? =
      some (seekMarkerState 2 (false :: (List.replicate count false ++ left)) tail) := by
  induction count generalizing left with
  | zero => rfl
  | succ count ih =>
      have hn : seekMarkerTrace (false :: left) count tail ≠ [] := by
        intro h
        have hh := seekMarkerTrace_head (false :: left) count tail
        simp [h] at hh
      rw [seekMarkerTrace, List.getLast?_cons_of_ne_nil hn, ih]
      have he : List.replicate count false ++ false :: left =
          List.replicate (count + 1) false ++ left := by
        rw [List.replicate_add]
        simp only [List.replicate_one, List.append_assoc, List.singleton_append]
      rw [he]

theorem seekMarkerTrace_length (left : List Bool) (count : Nat) (tail : List Bool) :
    (seekMarkerTrace left count tail).length = count + 3 := by
  induction count generalizing left with
  | zero => rfl
  | succ count ih => simp only [seekMarkerTrace, List.length_cons, ih]

theorem seekMarkerTrace_chain (left : List Bool) (count : Nat) (tail : List Bool) :
    (seekMarkerTrace left count tail).IsChain
      (fun before after => Turing.TM0.step seekMarkerMachine before = some after) := by
  induction count generalizing left with
  | zero =>
      simp [seekMarkerTrace, List.isChain_cons_cons, Turing.TM0.step,
        seekMarkerMachine, seekMarkerState, Turing.Tape.mk₂]
  | succ count ih =>
      apply List.isChain_cons.mpr
      constructor
      · intro after ha
        rw [seekMarkerTrace_head] at ha
        have he := Option.mem_some_iff.mp ha
        subst after
        simp [Turing.TM0.step, seekMarkerMachine, seekMarkerState, Turing.Tape.mk₂]
      · exact ih _

theorem seekMarker_runsFrom (left : List Bool) (count : Nat) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom seekMarkerMachine
      (seekMarkerState 0 left (List.replicate count false ++ true :: tail))
      (seekMarkerTrace left count tail)
      (seekMarkerState 2 (false :: (List.replicate count false ++ left)) tail) := by
  refine ⟨seekMarkerTrace_head left count tail, seekMarkerTrace_chain left count tail,
    seekMarkerTrace_last left count tail, ?_⟩
  simp [Turing.TM0.step, seekMarkerMachine, seekMarkerState]

/-- Mark the separator cell immediately left of the resident start, then
really move to the first cell of its three-zero separator. -/
def markResidentMachine : Machine 4 := fun q _ =>
  match q.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .write true)
  | 2 => some (3, .move .left)
  | 3 => some (4, .move .left)
  | _ => none

def markResidentState (q : Fin 5) (left right : List Bool) : MachineState 4 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

def markResidentTrace (left right : List Bool) : List (MachineState 4) :=
  [markResidentState 0 (false :: false :: false :: left) right,
   markResidentState 1 (false :: false :: left) (false :: right),
   markResidentState 2 (false :: false :: left) (true :: right),
   markResidentState 3 (false :: left) (false :: true :: right),
   markResidentState 4 left (false :: false :: true :: right)]

theorem markResident_runsFrom (left right : List Bool) :
    PSTRTMSeq005.RunsFrom markResidentMachine
      (markResidentState 0 (false :: false :: false :: left) right)
      (markResidentTrace left right)
      (markResidentState 4 left (false :: false :: true :: right)) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [markResidentTrace, List.isChain_cons_cons, Turing.TM0.step,
      markResidentMachine, markResidentState, Turing.Tape.mk₂]
  · simp [Turing.TM0.step, markResidentMachine, markResidentState]

def markedEraseMachine : Machine 10 :=
  PSTRTMSeq005.seqMachine markResidentMachine eraseMachine

/-- Fixed14-label actual left-archive disposal. It allocates a separator
marker, erases every old archive flag/data cell, scans those real cleared
cells, erases the marker and returns to the unchanged resident start. -/
def dropArchiveMachine : Machine 13 :=
  PSTRTMSeq005.seqMachine markedEraseMachine seekMarkerMachine

def markedEraseTrace (digits right : List Bool) : List (MachineState 10) :=
  (markResidentTrace (PSTRTMRawNat010.leftBlocks digits.reverse ++ [false]) right).map
      (PSTRTMSeq005.leftCfg (b := 5)) ++
    (eraseFullTrace [] digits (false :: false :: true :: right)).map
      (PSTRTMSeq005.rightCfg (a := 4))

def dropArchiveTrace (digits right : List Bool) : List (MachineState 13) :=
  (markedEraseTrace digits right).map (PSTRTMSeq005.leftCfg (b := 2)) ++
    (seekMarkerTrace [false] (2 * digits.length + 2) right).map
      (PSTRTMSeq005.rightCfg (a := 10))

theorem markedErase_runsFrom (digits right : List Bool) :
    PSTRTMSeq005.RunsFrom markedEraseMachine
      (PSTRTMSeq005.leftCfg (b := 5)
        (markResidentState 0
          (false :: false :: false :: (PSTRTMRawNat010.leftBlocks digits.reverse ++ [false])) right))
      (markedEraseTrace digits right)
      (PSTRTMSeq005.rightCfg (a := 4)
        (eraseState 5 [false]
          (List.replicate (2 * digits.length) false ++ false :: false :: true :: right))) := by
  apply PSTRTMSeq005.seq_runsFrom markResidentMachine eraseMachine
    _ _ _ _ _ (markResident_runsFrom _ _)
  exact erase_runsFrom [] digits (false :: false :: true :: right)

theorem dropArchive_runsFrom (digits right : List Bool) :
    PSTRTMSeq005.RunsFrom dropArchiveMachine
      (PSTRTMSeq005.leftCfg (b := 2)
        (PSTRTMSeq005.leftCfg (b := 5)
          (markResidentState 0
            (false :: false :: false :: (PSTRTMRawNat010.leftBlocks digits.reverse ++ [false])) right)))
      (dropArchiveTrace digits right)
      (PSTRTMSeq005.rightCfg (a := 10)
        (seekMarkerState 2
          (false :: (List.replicate (2 * digits.length + 2) false ++ [false])) right)) := by
  apply PSTRTMSeq005.seq_runsFrom markedEraseMachine seekMarkerMachine
    _ _ _ _ _ (markedErase_runsFrom digits right)
  change PSTRTMSeq005.RunsFrom seekMarkerMachine
    (seekMarkerState 0 [false]
      (List.replicate (2 * digits.length) false ++ false :: false :: true :: right))
    _ _
  have he : List.replicate (2 * digits.length + 2) false ++ true :: right =
      List.replicate (2 * digits.length) false ++ false :: false :: true :: right := by
    rw [List.replicate_add]
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, List.append_assoc]
  rw [← he]
  exact seekMarker_runsFrom [false] (2 * digits.length + 2) right

theorem dropArchive_final_tape (digits right : List Bool) :
    (PSTRTMSeq005.rightCfg (a := 10)
      (seekMarkerState 2
        (false :: (List.replicate (2 * digits.length + 2) false ++ [false])) right)).Tape =
      Turing.Tape.mk₁ right := by
  simp only [PSTRTMSeq005.rightCfg, seekMarkerState, Turing.Tape.mk₁, Turing.Tape.mk₂]
  have he : false :: (List.replicate (2 * digits.length + 2) false ++ [false]) =
      List.replicate (2 * digits.length + 4) false := by
    rw [← List.cons_append, ← List.replicate_succ]
    change List.replicate (2 * digits.length + 3) false ++ List.replicate 1 false = _
    rw [← List.replicate_add]
  rw [he]
  rw [show Turing.ListBlank.mk (List.replicate (2 * digits.length + 4) false) =
      Turing.ListBlank.mk ([] : List Bool) by
    simpa only [List.nil_append] using
      PSTRTMPackFinish039.blank_false_suffix [] (2 * digits.length + 4)]

theorem dropArchiveTrace_length (digits right : List Bool) :
    (dropArchiveTrace digits right).length = 6 * digits.length + 13 := by
  simp only [dropArchiveTrace, markedEraseTrace, List.length_append, List.length_map,
    markResidentTrace, List.length_cons, List.length_nil, eraseFullTrace_length,
    seekMarkerTrace_length]
  omega

theorem dropArchiveTrace_visitedSpace_le (inputLength : Nat) (digits right : List Bool) :
    visitedSpace dropArchiveMachine inputLength (dropArchiveTrace digits right) ≤
      inputLength + 12 * digits.length + 27 := by
  have hs := PSTRTMTrace002.visitedSpace_le dropArchiveMachine inputLength (dropArchiveTrace digits right)
  rw [dropArchiveTrace_length] at hs
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
