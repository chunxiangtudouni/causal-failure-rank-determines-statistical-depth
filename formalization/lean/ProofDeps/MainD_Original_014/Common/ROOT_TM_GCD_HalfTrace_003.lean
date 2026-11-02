module
public import Common.ROOT_TM_GCD_HalfValue_002

set_option autoImplicit false
set_option warningAsError true
@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDHalf001
open PaperProofs.Common.Native.RationalControllerComputation
local notation "cols" => PSTRTMBinaryAdd024.operandColumns
local notation "leftCols" => PSTRTMCompareCode054.leftColumns

def initial (r : Fin 4) (archive : List Bool) : List Pair → List Bool → MachineState 24
  | [], tail => state (backward 3 r) archive (false :: tail)
  | (a,b) :: earlier, tail =>
    state (backward 3 r) (b :: true :: a :: (leftCols earlier ++ false :: archive)) (true :: tail)

private theorem commands (r : Fin 4) (b : Bool) :
    halfMachine (backward 3 r) true = some (readB r, .move .left) ∧
    halfMachine (readB r) b = some (backward 0 (nextCarry r b), .write (higherBit r)) ∧
    halfMachine (backward 0 (nextCarry r b)) (higherBit r) = some (backward 1 (nextCarry r b), .move .left) ∧
    halfMachine (backward 1 (nextCarry r b)) true = some (backward 2 (nextCarry r b), .move .left) := by
  fin_cases r <;> cases b <;> exact ⟨rfl, rfl, rfl, rfl⟩

def unitTrace (r : Fin 4) (archive : List Bool) (a b : Bool)
    (earlier : List Pair) (tail : List Bool) : List (MachineState 24) :=
  let left := leftCols earlier ++ false :: archive
  let next := nextCarry r b
  [initial r archive ((a,b) :: earlier) tail,
    state (readB r) (true :: a :: left) (b :: true :: tail),
    state (backward 0 next) (true :: a :: left) (higherBit r :: true :: tail),
    state (backward 1 next) (a :: left) (true :: higherBit r :: true :: tail),
    state (backward 2 next) left (a :: true :: higherBit r :: true :: tail)]

theorem unit_head (r : Fin 4) (archive : List Bool) (a b : Bool)
    (earlier : List Pair) (tail : List Bool) :
    (unitTrace r archive a b earlier tail).head? = some (initial r archive ((a,b) :: earlier) tail) := rfl

theorem unit_last (r : Fin 4) (archive : List Bool) (a b : Bool)
    (earlier : List Pair) (tail : List Bool) :
    (unitTrace r archive a b earlier tail).getLast? = some
      (state (backward 2 (nextCarry r b)) (leftCols earlier ++ false :: archive)
        (a :: true :: higherBit r :: true :: tail)) := rfl

theorem unit_length (r : Fin 4) (archive : List Bool) (a b : Bool)
    (earlier : List Pair) (tail : List Bool) : (unitTrace r archive a b earlier tail).length = 5 := rfl

theorem unit_chain (r : Fin 4) (archive : List Bool) (a b : Bool)
    (earlier : List Pair) (tail : List Bool) :
    (unitTrace r archive a b earlier tail).IsChain (fun before after => Turing.TM0.step halfMachine before = some after) := by
  obtain ⟨h1,h2,h3,h4⟩ := commands r b
  simp [unitTrace, initial, List.isChain_cons_cons, Turing.TM0.step, state, Turing.Tape.mk₂, h1,h2,h3,h4]

theorem unit_advance (r : Fin 4) (archive : List Bool) (earlier : List Pair) (tail : List Bool) :
    Turing.TM0.step halfMachine (state (backward 2 r) (leftCols earlier ++ false :: archive) tail) =
      some (initial r archive earlier tail) := by
  have hm (symbol : Bool) : halfMachine (backward 2 r) symbol = some (backward 3 r, .move .left) := by
    fin_cases r <;> rfl
  cases earlier with
  | nil => simp [initial, PSTRTMCompareCode054.leftColumns, Turing.TM0.step, state, Turing.Tape.mk₂, hm]
  | cons pair earlier =>
    obtain ⟨a,b⟩ := pair
    simp [initial, PSTRTMCompareCode054.leftColumns, Turing.TM0.step, state, Turing.Tape.mk₂, hm]

private theorem empty_command (r : Fin 4) :
    halfMachine (backward 3 r) false = some (haltLabel r, .move .right) := by
  fin_cases r <;> rfl

def loopTrace (r : Fin 4) (archive : List Bool) : List Pair → List Bool → List (MachineState 24)
  | [], tail => [initial r archive [] tail, state (haltLabel r) (false :: archive) tail]
  | (a,b) :: earlier, tail => unitTrace r archive a b earlier tail ++
      loopTrace (nextCarry r b) archive earlier (a :: true :: higherBit r :: true :: tail)

theorem loop_head (r : Fin 4) (archive : List Bool) (previous : List Pair) (tail : List Bool) :
    (loopTrace r archive previous tail).head? = some (initial r archive previous tail) := by
  cases previous with
  | nil => rfl
  | cons pair earlier => obtain ⟨a,b⟩ := pair; simp only [loopTrace, List.head?_append, unit_head, Option.some_or]

theorem loop_last (r : Fin 4) (archive : List Bool) (previous : List Pair) (tail : List Bool) :
    (loopTrace r archive previous tail).getLast? = some
      (state (haltLabel (finalControl r previous)) (false :: archive)
        (cols (resultReverse r previous).reverse ++ tail)) := by
  induction previous generalizing r tail with
  | nil => rfl
  | cons pair earlier ih =>
    obtain ⟨a,b⟩ := pair
    simp [loopTrace, List.getLast?_append, ih, resultReverse, finalControl, List.reverse_cons,
      PSTRTMBinaryAdd024.operandColumns, List.flatMap_append, List.append_assoc]

theorem loop_length (r : Fin 4) (archive : List Bool) (previous : List Pair) (tail : List Bool) :
    (loopTrace r archive previous tail).length = 5 * previous.length + 2 := by
  induction previous generalizing r tail with
  | nil => rfl
  | cons pair earlier ih =>
    obtain ⟨a,b⟩ := pair
    simp only [loopTrace, List.length_append, unit_length, ih, List.length_cons]
    omega

theorem loop_chain (r : Fin 4) (archive : List Bool) (previous : List Pair) (tail : List Bool) :
    (loopTrace r archive previous tail).IsChain (fun before after => Turing.TM0.step halfMachine before = some after) := by
  induction previous generalizing r tail with
  | nil => simp [loopTrace, initial, List.isChain_cons_cons, Turing.TM0.step, state, Turing.Tape.mk₂, empty_command r]
  | cons pair earlier ih =>
    obtain ⟨a,b⟩ := pair
    rw [loopTrace]
    apply (unit_chain r archive a b earlier tail).append (ih (nextCarry r b) _)
    intro before hb after ha
    simp only [unit_last, Option.mem_some_iff] at hb
    simp only [loop_head, Option.mem_some_iff] at ha
    subst before
    subst after
    exact unit_advance (nextCarry r b) archive earlier _

def fullTrace (archive : List Bool) (previous : List Pair) (tail : List Bool) : List (MachineState 24) :=
  state 0 (leftCols previous ++ false :: archive) tail :: loopTrace (carryControl false false) archive previous tail

theorem full_head (archive : List Bool) (previous : List Pair) (tail : List Bool) :
    (fullTrace archive previous tail).head? = some (state 0 (leftCols previous ++ false :: archive) tail) := rfl

theorem full_length (archive : List Bool) (previous : List Pair) (tail : List Bool) :
    (fullTrace archive previous tail).length = 5 * previous.length + 3 := by
  simp only [fullTrace, List.length_cons, loop_length]

theorem full_last (archive : List Bool) (previous : List Pair) (tail : List Bool) :
    (fullTrace archive previous tail).getLast? = some
      (state (haltLabel (finalControl (carryControl false false) previous)) (false :: archive)
        (cols (resultReverse (carryControl false false) previous).reverse ++ tail)) := by
  have hne : loopTrace (carryControl false false) archive previous tail ≠ [] := by
    intro h
    have hh := loop_head (carryControl false false) archive previous tail
    simp [h] at hh
  rw [fullTrace, List.getLast?_cons_of_ne_nil hne, loop_last]

theorem full_chain (archive : List Bool) (previous : List Pair) (tail : List Bool) :
    (fullTrace archive previous tail).IsChain (fun before after => Turing.TM0.step halfMachine before = some after) := by
  apply List.isChain_cons.mpr
  constructor
  · intro after ha
    rw [loop_head] at ha
    have he := Option.mem_some_iff.mp ha
    subst after
    cases previous with
    | nil => simp [initial, PSTRTMCompareCode054.leftColumns, Turing.TM0.step, halfMachine, state, Turing.Tape.mk₂]
    | cons pair earlier =>
      obtain ⟨a,b⟩ := pair
      simp [initial, PSTRTMCompareCode054.leftColumns, Turing.TM0.step, halfMachine, state, Turing.Tape.mk₂]
  · exact loop_chain (carryControl false false) archive previous tail

/-- Actual EOF-to-start halving. Every A bit/flag, the entire arbitrary
archive beyond the visited false guard, and ALL tail cells are retained.
Real low-bit/new-nonzero HALT carryControl and exact 5*N+3 trace, including HALT. -/
theorem half_runsFrom (archive : List Bool) (pairs : List Pair) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom halfMachine (state 0 (leftCols pairs.reverse ++ false :: archive) tail)
      (fullTrace archive pairs.reverse tail)
      (state (haltLabel (finalControl (carryControl false false) pairs.reverse)) (false :: archive)
        (cols (halfPairs pairs) ++ tail)) :=
  ⟨full_head _ _ _, full_chain _ _ _, full_last _ _ _, half_halt _ _ _⟩

theorem half_visitedSpace_le (archive : List Bool) (pairs : List Pair) (tail : List Bool) (inputLength : Nat) :
    visitedSpace halfMachine inputLength (fullTrace archive pairs.reverse tail) ≤
      inputLength + 10 * pairs.length + 7 := by
  have h := PSTRTMTrace002.visitedSpace_le halfMachine inputLength (fullTrace archive pairs.reverse tail)
  rw [full_length, List.length_reverse] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDHalf001
