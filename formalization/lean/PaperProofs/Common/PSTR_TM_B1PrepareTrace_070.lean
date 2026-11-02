module
public import PaperProofs.Common.PSTR_TM_B1PrepareCode_069

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1PrepareTrace070
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMB1PrepareCode069

def allocateTrace (left : List Bool) : List (MachineState 31) :=
  [state 2 left [],
    state 3 left [false],
    state 4 ([false] ++ left) [],
    state 5 ([false] ++ left) [true],
    state 6 ([true,false] ++ left) [],
    state 7 ([true,false] ++ left) [false],
    state 8 ([false,true,false] ++ left) [],
    state 9 ([false,true,false] ++ left) [true],
    state 10 ([true,false,true,false] ++ left) [],
    state 11 ([true,false,true,false] ++ left) [false],
    state 12 ([false,true,false,true,false] ++ left) [],
    state 13 ([false,true,false,true,false] ++ left) [false],
    state 14 ([false,false,true,false,true,false] ++ left) [],
    state 15 ([false,false,true,false,true,false] ++ left) [true],
    state 16 ([true,false,false,true,false,true,false] ++ left) [],
    state 17 ([true,false,false,true,false,true,false] ++ left) [false],
    state 18 ([false,true,false,false,true,false,true,false] ++ left) [],
    state 19 ([false,true,false,false,true,false,true,false] ++ left) [false],
    state 20 ([false,false,true,false,false,true,false,true,false] ++ left) [],
    state 21 ([false,false,true,false,false,true,false,true,false] ++ left) [true],
    state 22 ([false,true,false,false,true,false,true,false] ++ left) [false,true],
    state 23 ([true,false,false,true,false,true,false] ++ left) [false,false,true],
    state 24 ([false,false,true,false,true,false] ++ left) [true,false,false,true],
    state 25 ([false,true,false,true,false] ++ left) [false,true,false,false,true]]

theorem allocate_head (left : List Bool) : (allocateTrace left).head? = some (state 2 left []) := rfl

theorem allocate_last (left : List Bool) : (allocateTrace left).getLast? = some
    (state 25 ([false,true,false,true,false] ++ left) [false,true,false,false,true]) := rfl

theorem allocate_length (left : List Bool) : (allocateTrace left).length = 24 := rfl

theorem allocate_chain (left : List Bool) :
    (allocateTrace left).IsChain (fun a b => Turing.TM0.step prepareMachine a = some b) := by
  simp [allocateTrace, List.isChain_cons_cons, Turing.TM0.step, prepareMachine, state, Turing.Tape.mk₂]

def seekTrace (left : List Bool) : List (Bool × Bool) → List (MachineState 31)
  | [] => [state 0 left [], state 1 (false :: left) []]
  | (a,b) :: later =>
    [state 0 left (a :: true :: b :: true :: PSTRTMBinaryAdd024.operandColumns later),
      state 1 (a :: left) (true :: b :: true :: PSTRTMBinaryAdd024.operandColumns later),
      state 0 (true :: a :: left) (b :: true :: PSTRTMBinaryAdd024.operandColumns later),
      state 1 (b :: true :: a :: left) (true :: PSTRTMBinaryAdd024.operandColumns later)] ++
        seekTrace (true :: b :: true :: a :: left) later

theorem seek_head (left : List Bool) (pairs : List (Bool × Bool)) :
    (seekTrace left pairs).head? = some (state 0 left (PSTRTMBinaryAdd024.operandColumns pairs)) := by
  cases pairs with
  | nil => rfl
  | cons pair later => obtain ⟨a,b⟩ := pair; rfl

theorem seek_last (left : List Bool) (pairs : List (Bool × Bool)) :
    (seekTrace left pairs).getLast? = some
      (state 1 (false :: (PSTRTMCompareCode054.leftColumns pairs.reverse ++ left)) []) := by
  induction pairs generalizing left with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    have hne : seekTrace (true :: b :: true :: a :: left) later ≠ [] := by
      intro h
      have hh := seek_head (true :: b :: true :: a :: left) later
      simp [h] at hh
    simp only [seekTrace, List.cons_append, List.nil_append, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [PSTRTMCompareCode054.leftColumns,
      List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem seek_length (left : List Bool) (pairs : List (Bool × Bool)) : (seekTrace left pairs).length = 4 * pairs.length + 2 := by
  induction pairs generalizing left with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [seekTrace, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem seek_chain (left : List Bool) (pairs : List (Bool × Bool)) :
    (seekTrace left pairs).IsChain (fun a b => Turing.TM0.step prepareMachine a = some b) := by
  induction pairs generalizing left with
  | nil => simp [seekTrace, List.isChain_cons_cons, Turing.TM0.step, prepareMachine, state, Turing.Tape.mk₂]
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [seekTrace]
    apply List.IsChain.append
    · simp [List.isChain_cons_cons, Turing.TM0.step, prepareMachine, state, Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at hb
      simp only [seek_head, Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step, prepareMachine, state, Turing.Tape.mk₂]

theorem seek_advance (left : List Bool) :
    Turing.TM0.step prepareMachine (state 1 (false :: left) []) = some (state 2 left []) := by
  simp [Turing.TM0.step, prepareMachine, state, Turing.Tape.mk₂, PSTRTMRawNat010.blank_single_false]

private theorem state_left_false (q : Fin 32) (left right : List Bool) :
    state q (left ++ [false]) right = state q left right := by
  simp only [state, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_append_false]

theorem allocate_advance (pairs : List (Bool × Bool)) :
    Turing.TM0.step prepareMachine
      (state 25 ([false,true,false,true,false] ++ PSTRTMCompareCode054.leftColumns pairs.reverse)
        [false,true,false,false,true]) =
      some (liftRewind (PSTRTMColumnRewind067.state 0
        (PSTRTMCompareCode054.leftColumns (paddedPairs pairs).reverse ++ [false]) suffix)) := by
  have hl : PSTRTMCompareCode054.leftColumns (paddedPairs pairs).reverse =
      [true,false,true,false] ++ PSTRTMCompareCode054.leftColumns pairs.reverse := by
    simp [paddedPairs, List.reverse_append, PSTRTMCompareCode054.leftColumns]
  rw [hl]
  change _ = some (state 26 (([true,false,true,false] ++ PSTRTMCompareCode054.leftColumns pairs.reverse) ++ [false]) suffix)
  rw [state_left_false]
  simp [Turing.TM0.step, prepareMachine, state, suffix, Turing.Tape.mk₂]

private theorem append_link (xs ys : List (MachineState 31)) (last first : MachineState 31)
    (hx : xs.IsChain (fun a b => Turing.TM0.step prepareMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step prepareMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step prepareMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step prepareMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def prepareTrace (pairs : List (Bool × Bool)) : List (MachineState 31) :=
  seekTrace [] pairs ++ allocateTrace (PSTRTMCompareCode054.leftColumns pairs.reverse) ++
    (PSTRTMColumnRewind067.fullTrace [] (paddedPairs pairs).reverse suffix).map liftRewind

def prepareFinal (pairs : List (Bool × Bool)) : MachineState 31 := state 31 [false] (preparedWord pairs)

theorem prepare_head (pairs : List (Bool × Bool)) :
    (prepareTrace pairs).head? = some (state 0 [] (PSTRTMBinaryAdd024.operandColumns pairs)) := by
  simp only [prepareTrace, List.head?_append, seek_head, Option.some_or]

theorem prepare_last (pairs : List (Bool × Bool)) :
    (prepareTrace pairs).getLast? = some (prepareFinal pairs) := by
  simp only [prepareTrace, List.getLast?_append, List.getLast?_map, PSTRTMColumnRewind067.full_last,
    List.reverse_reverse, Option.map_some, Option.some_or]
  rfl

theorem prepare_length (pairs : List (Bool × Bool)) : (prepareTrace pairs).length = 8 * pairs.length + 33 := by
  simp only [prepareTrace, List.length_append, List.length_map, seek_length, allocate_length,
    PSTRTMColumnRewind067.full_length, List.length_reverse, paddedPairs, List.length_append,
    List.length_cons, List.length_nil]
  omega

theorem prepare_chain (pairs : List (Bool × Bool)) :
    (prepareTrace pairs).IsChain (fun a b => Turing.TM0.step prepareMachine a = some b) := by
  unfold prepareTrace
  refine append_link _ _
    (state 25 ([false,true,false,true,false] ++ PSTRTMCompareCode054.leftColumns pairs.reverse)
      [false,true,false,false,true])
    (liftRewind (PSTRTMColumnRewind067.state 0
      (PSTRTMCompareCode054.leftColumns (paddedPairs pairs).reverse ++ [false]) suffix)) ?_ ?_ ?_ ?_ (allocate_advance pairs)
  · exact append_link _ _ _ _ (seek_chain [] pairs) (allocate_chain _)
      (by simpa only [List.append_nil] using seek_last [] pairs) (allocate_head _) (seek_advance _)
  · exact rewind_chain _ (PSTRTMColumnRewind067.full_chain [] (paddedPairs pairs).reverse suffix)
  · simp only [List.getLast?_append, allocate_last, Option.some_or]
  · simp only [List.head?_map, PSTRTMColumnRewind067.full_head, Option.map_some]

theorem prepare_runs (pairs : List (Bool × Bool)) :
    Runs prepareMachine (PSTRTMBinaryAdd024.operandColumns pairs) (prepareTrace pairs) (prepareFinal pairs) := by
  apply PSTRTMTrace002.runs_of_chain
  · simpa [Turing.TM0.init, state, Turing.Tape.mk₁] using prepare_head pairs
  · exact prepare_chain pairs
  · exact prepare_last pairs
  · exact prepare_halt _ _

theorem prepare_final_tape (pairs : List (Bool × Bool)) :
    (prepareFinal pairs).Tape = Turing.Tape.mk₁ (preparedWord pairs) := by
  simp only [prepareFinal, state, Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]

/-- Every extra high digit, delimiter, marker and counter cell is actually
written/allocated by the fixed32-label program; actual EOF rewind is charged. -/
theorem prepare_computes (pairs : List (Bool × Bool)) :
    computes prepareMachine (PSTRTMBinaryAdd024.operandColumns pairs) (preparedWord pairs)
      (8*pairs.length+33) (20*pairs.length+67) := by
  refine ⟨prepareTrace pairs, prepareFinal pairs, prepare_runs pairs, ?_, (prepare_length pairs).le, ?_⟩
  · rw [prepare_final_tape]
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
  · have hs := PSTRTMTrace002.visitedSpace_le prepareMachine
      (PSTRTMBinaryAdd024.operandColumns pairs).length (prepareTrace pairs)
    rw [PSTRTMBinaryAdd024.operandColumns_length, prepare_length] at hs
    rw [PSTRTMBinaryAdd024.operandColumns_length]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1PrepareTrace070

