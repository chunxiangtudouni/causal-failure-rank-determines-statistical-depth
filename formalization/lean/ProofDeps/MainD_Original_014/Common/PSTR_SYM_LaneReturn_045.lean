module

public import Common.PSTR_SYM_LaneArchive_044

/-! Complete same-code lane walks followed by actual first-triple HALT.
The logical prefix's safety/reset facts are internal obligations supplied
by044 and the real marker layout. No root/cursor position is an input ROM. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLaneReturn

open Turing PSTRTMSeq005 PSTRSymbolicLaneScan PSTRSymbolicLaneArchive

def rightScanTrace (seen : Fin 3) (left : List Bool) (pairs : List (Bool × Bool))
    (first second : Bool) (suffix : List Bool) : List (MachineState 6) :=
  rightWalkTrace seen left pairs (true :: first :: true :: second :: true :: suffix) ++
    (tripleRightTrace ((navigationCells pairs).reverse ++ left) first second suffix).tail

theorem right_scan_runsFrom (seen : Fin 3) (left : List Bool) (pairs : List (Bool × Bool))
    (first second : Bool) (suffix : List Bool) (safe : safeNavigation seen pairs)
    (reset : seenAfter seen pairs = 0) :
    RunsFrom (flagWalkMachine true)
      (scanState (readLabel seen) left
        (navigationCells pairs ++ true :: first :: true :: second :: true :: suffix))
      (rightScanTrace seen left pairs first second suffix)
      (scanState 6 (second :: true :: first :: true :: ((navigationCells pairs).reverse ++ left))
        (true :: suffix)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [rightScanTrace, List.head?_append, rightWalk_head, Option.some_or]
  · apply List.IsChain.append
    · exact rightWalk_chain _ _ _ _ safe
    · simp [tripleRightTrace, List.isChain_cons_cons, TM0.step, flagWalkMachine, scanState, Tape.mk₂]
    · intro before beforeLast after afterHead
      simp only [rightWalk_last, reset, Option.mem_some_iff] at beforeLast
      simp only [tripleRightTrace, List.tail_cons, List.head?_cons, Option.mem_some_iff] at afterHead
      subst before
      subst after
      simp [TM0.step, flagWalkMachine, scanState, readLabel, Tape.mk₂]
  · simp only [rightScanTrace, List.getLast?_append, tripleRightTrace, List.tail_cons,
      List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or]
  · simp [TM0.step, flagWalkMachine, scanState]

theorem right_scan_length (seen : Fin 3) (left : List Bool) (pairs : List (Bool × Bool))
    (first second : Bool) (suffix : List Bool) :
    (rightScanTrace seen left pairs first second suffix).length = 2 * pairs.length + 6 := by
  simp only [rightScanTrace, List.length_append, rightWalk_length, tripleRightTrace,
    List.tail_cons, List.length_cons, List.length_nil]

def leftScanTrace (seen : Fin 3) (older : List Bool) (pairs : List (Bool × Bool))
    (first second : Bool) (suffix : List Bool) : List (MachineState 6) :=
  leftWalkTrace seen (true :: first :: true :: second :: true :: older) pairs suffix ++
    (tripleLeftTrace older first second ((navigationCells pairs).reverse ++ suffix)).tail

theorem left_scan_runsFrom (seen : Fin 3) (older : List Bool) (pairs : List (Bool × Bool))
    (first second : Bool) (suffix : List Bool) (safe : safeNavigation seen pairs)
    (reset : seenAfter seen pairs = 0) :
    RunsFrom (flagWalkMachine false)
      (leftFront seen (navigationCells pairs ++ true :: first :: true :: second :: true :: older) suffix)
      (leftScanTrace seen older pairs first second suffix)
      (scanState 6 older (true :: second :: true :: first :: true ::
        ((navigationCells pairs).reverse ++ suffix))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [leftScanTrace, List.head?_append, leftWalk_head, Option.some_or]
  · apply List.IsChain.append
    · exact leftWalk_chain _ _ _ _ safe
    · simp [tripleLeftTrace, List.isChain_cons_cons, TM0.step, flagWalkMachine, scanState, Tape.mk₂]
    · intro before beforeLast after afterHead
      simp only [leftWalk_last, reset, Option.mem_some_iff] at beforeLast
      simp only [tripleLeftTrace, List.tail_cons, List.head?_cons, Option.mem_some_iff] at afterHead
      subst before
      subst after
      simp [leftFront, TM0.step, flagWalkMachine, scanState, readLabel, Tape.mk₂]
  · simp only [leftScanTrace, List.getLast?_append, tripleLeftTrace, List.tail_cons,
      List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or]
  · simp [TM0.step, flagWalkMachine, scanState]

theorem left_scan_length (seen : Fin 3) (older : List Bool) (pairs : List (Bool × Bool))
    (first second : Bool) (suffix : List Bool) :
    (leftScanTrace seen older pairs first second suffix).length = 2 * pairs.length + 6 := by
  simp only [leftScanTrace, List.length_append, leftWalk_length, tripleLeftTrace,
    List.tail_cons, List.length_cons, List.length_nil]

theorem right_scan_prefix_space (seen : Fin 3) (left : List Bool) (pairs : List (Bool × Bool))
    (first second : Bool) (suffix : List Bool) (inputLength clock : Nat) :
    visitedSpace (flagWalkMachine true) inputLength
      ((rightScanTrace seen left pairs first second suffix).take clock) ≤
        inputLength + 4 * pairs.length + 13 := by
  have cells := PSTRTMTrace002.visitedSpace_le (flagWalkMachine true) inputLength
    ((rightScanTrace seen left pairs first second suffix).take clock)
  have count : ((rightScanTrace seen left pairs first second suffix).take clock).length ≤
      2 * pairs.length + 6 := by
    simp only [List.length_take, right_scan_length]
    omega
  omega

theorem left_scan_prefix_space (seen : Fin 3) (older : List Bool) (pairs : List (Bool × Bool))
    (first second : Bool) (suffix : List Bool) (inputLength clock : Nat) :
    visitedSpace (flagWalkMachine false) inputLength
      ((leftScanTrace seen older pairs first second suffix).take clock) ≤
        inputLength + 4 * pairs.length + 13 := by
  have cells := PSTRTMTrace002.visitedSpace_le (flagWalkMachine false) inputLength
    ((leftScanTrace seen older pairs first second suffix).take clock)
  have count : ((leftScanTrace seen older pairs first second suffix).take clock).length ≤
      2 * pairs.length + 6 := by
    simp only [List.length_take, left_scan_length]
    omega
  omega

/-! The physical intervening payload cells differ between the two scan
directions. A flag-preserving re-pairing has exactly the same finite
reader history; payloads are never mistaken for navigation cells. -/

theorem navigation_flags_congr (seen : Fin 3) (first second : List (Bool × Bool))
    (same : first.map Prod.fst = second.map Prod.fst) :
    safeNavigation seen first = safeNavigation seen second ∧ seenAfter seen first = seenAfter seen second := by
  induction first generalizing seen second with
  | nil =>
    cases second with
    | nil => exact ⟨rfl,rfl⟩
    | cons pair later => simp at same
  | cons pair later ih =>
    obtain ⟨flag,bit⟩ := pair
    cases second with
    | nil => simp at same
    | cons pair rest =>
      obtain ⟨otherFlag,otherBit⟩ := pair
      simp only [List.map_cons, List.cons.injEq] at same
      obtain ⟨rfl, same⟩ := same
      obtain ⟨valid, final⟩ := ih (afterSeen seen flag) rest same
      exact ⟨congrArg (fun predicate : Prop => safeFlag seen flag ∧ predicate) valid, final⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLaneReturn
