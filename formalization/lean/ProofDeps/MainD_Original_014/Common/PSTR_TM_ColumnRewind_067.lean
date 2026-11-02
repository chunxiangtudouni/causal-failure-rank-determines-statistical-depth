module
public import Common.PSTR_TM_ShiftColumnTrace_066

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMColumnRewind067
open PaperProofs.Common.Native.RationalControllerComputation

def rewindMachine : Machine 5 := fun q symbol =>
  match q.val with
  | 0 => some (1, .move .left)
  | 1 => some (if symbol then 2 else 5, if symbol then .move .left else .move .right)
  | 2 => some (3, .move .left)
  | 3 => some (4, .move .left)
  | 4 => some (1, .move .left)
  | _ => none

def state (q : Fin 6) (left right : List Bool) : MachineState 5 := ⟨q, Turing.Tape.mk₂ left right⟩

def initial (archive : List Bool) : List (Bool × Bool) → List Bool → MachineState 5
  | [], tail => state 1 archive (false :: tail)
  | (a,b) :: previous, tail =>
    state 1 (b :: true :: a :: (PSTRTMCompareCode054.leftColumns previous ++ false :: archive)) (true :: tail)

def rewindTrace (archive : List Bool) : List (Bool × Bool) → List Bool → List (MachineState 5)
  | [], tail => [state 1 archive (false :: tail), state 5 (false :: archive) tail]
  | (a,b) :: previous, tail =>
    state 1 (b :: true :: a :: (PSTRTMCompareCode054.leftColumns previous ++ false :: archive)) (true :: tail) ::
    state 2 (true :: a :: (PSTRTMCompareCode054.leftColumns previous ++ false :: archive)) (b :: true :: tail) ::
    state 3 (a :: (PSTRTMCompareCode054.leftColumns previous ++ false :: archive)) (true :: b :: true :: tail) ::
    state 4 (PSTRTMCompareCode054.leftColumns previous ++ false :: archive) (a :: true :: b :: true :: tail) ::
      rewindTrace archive previous (a :: true :: b :: true :: tail)

theorem rewind_head (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (rewindTrace archive previous tail).head? = some (initial archive previous tail) := by
  cases previous <;> rfl

theorem rewind_length (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (rewindTrace archive previous tail).length = 4 * previous.length + 2 := by
  induction previous generalizing tail with
  | nil => rfl
  | cons pair previous ih => obtain ⟨a,b⟩ := pair; simp only [rewindTrace, List.length_cons, ih]; omega

theorem rewind_last (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (rewindTrace archive previous tail).getLast? = some
      (state 5 (false :: archive) (PSTRTMBinaryAdd024.operandColumns previous.reverse ++ tail)) := by
  induction previous generalizing tail with
  | nil => rfl
  | cons pair previous ih =>
    obtain ⟨a,b⟩ := pair
    have hne : rewindTrace archive previous (a :: true :: b :: true :: tail) ≠ [] := by
      intro h
      have hl := rewind_length archive previous (a :: true :: b :: true :: tail)
      simp [h] at hl
    simp only [rewindTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [PSTRTMBinaryAdd024.operandColumns, List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem rewind_chain (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (rewindTrace archive previous tail).IsChain (fun a b => Turing.TM0.step rewindMachine a = some b) := by
  induction previous generalizing tail with
  | nil => simp [rewindTrace, List.isChain_cons_cons, Turing.TM0.step, rewindMachine, state, Turing.Tape.mk₂]
  | cons pair previous ih =>
    obtain ⟨a,b⟩ := pair
    simp only [rewindTrace, List.isChain_cons_cons]
    refine ⟨by simp [Turing.TM0.step, rewindMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, rewindMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, rewindMachine, state, Turing.Tape.mk₂], ?_⟩
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [rewind_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      cases previous <;> simp [initial, Turing.TM0.step, rewindMachine, state,
        PSTRTMCompareCode054.leftColumns, Turing.Tape.mk₂]
    · exact ih _

def fullTrace (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) : List (MachineState 5) :=
  state 0 (PSTRTMCompareCode054.leftColumns previous ++ false :: archive) tail :: rewindTrace archive previous tail

theorem full_head (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (fullTrace archive previous tail).head? = some
      (state 0 (PSTRTMCompareCode054.leftColumns previous ++ false :: archive) tail) := rfl

theorem full_length (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (fullTrace archive previous tail).length = 4 * previous.length + 3 := by
  simp only [fullTrace, List.length_cons, rewind_length]

theorem full_last (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (fullTrace archive previous tail).getLast? = some
      (state 5 (false :: archive) (PSTRTMBinaryAdd024.operandColumns previous.reverse ++ tail)) := by
  have hne : rewindTrace archive previous tail ≠ [] := by
    intro h
    have hl := rewind_length archive previous tail
    simp [h] at hl
  rw [fullTrace, List.getLast?_cons_of_ne_nil hne, rewind_last]

theorem full_chain (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (fullTrace archive previous tail).IsChain (fun a b => Turing.TM0.step rewindMachine a = some b) := by
  apply List.isChain_cons.mpr
  constructor
  · intro after ha
    rw [rewind_head] at ha
    have he := Option.mem_some_iff.mp ha
    subst after
    cases previous <;> simp [initial, Turing.TM0.step, rewindMachine, state,
      PSTRTMCompareCode054.leftColumns, Turing.Tape.mk₂]
  · exact rewind_chain archive previous tail

/-- The B1 loop's real EOF-to-start transport. No head reset: every
left move and the final right move across its actual false guard is charged.
All column bits, archive cells, and arbitrary tail cells remain intact. -/
theorem rewind_runsFrom (archive : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom rewindMachine
      (state 0 (PSTRTMCompareCode054.leftColumns pairs.reverse ++ false :: archive) tail)
      (fullTrace archive pairs.reverse tail)
      (state 5 (false :: archive) (PSTRTMBinaryAdd024.operandColumns pairs ++ tail)) := by
  refine ⟨full_head _ _ _, full_chain _ _ _, ?_, ?_⟩
  · simpa only [List.reverse_reverse] using full_last archive pairs.reverse tail
  · simp [Turing.TM0.step, rewindMachine, state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMColumnRewind067
