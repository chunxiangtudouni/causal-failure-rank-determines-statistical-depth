module

public import Common.PSTR_SYM_Carry_042
public import Mathlib.Tactic.FinCases

/-! Actual two-cell-stride scanner. The finite reader remembers zero, one,
or two preceding TRUE lane cells. Its first triple is accepted by a real
WRITE-current-TRUE and HALT. Validity below is an internal physical-word
condition; the original paired-archive producer must still discharge it. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLaneScan

open Turing PSTRTMSeq005

def readLabel (seen : Fin 3) : Fin 7 := ⟨seen.val, by omega⟩
def moveLabel (seen : Fin 3) : Fin 7 := ⟨3 + seen.val, by omega⟩

def afterSeen (seen : Fin 3) (flag : Bool) : Fin 3 :=
  if flag then if seen.val = 0 then 1 else 2 else 0

def safeFlag (seen : Fin 3) (flag : Bool) : Prop := flag = false ∨ seen.val < 2

def navigationCells (pairs : List (Bool × Bool)) : List Bool :=
  pairs.flatMap (fun pair => [pair.1,pair.2])

theorem navigationCells_cons (flag bit : Bool) (later : List (Bool × Bool)) :
    navigationCells ((flag,bit) :: later) = flag :: bit :: navigationCells later := by
  simp only [navigationCells, List.flatMap_cons, List.cons_append, List.nil_append]

def safeNavigation : Fin 3 → List (Bool × Bool) → Prop
  | _, [] => True
  | seen, (flag,_) :: later => safeFlag seen flag ∧ safeNavigation (afterSeen seen flag) later

def seenAfter : Fin 3 → List (Bool × Bool) → Fin 3
  | seen, [] => seen
  | seen, (flag,_) :: later => seenAfter (afterSeen seen flag) later

def flagWalkMachine (rightward : Bool) : Machine 6 := fun label symbol =>
  match label.val with
  | 0 => some ((if symbol then 4 else 3), .move (if rightward then .right else .left))
  | 1 => some ((if symbol then 5 else 3), .move (if rightward then .right else .left))
  | 2 => if symbol then some (6, .write true) else
      some (3, .move (if rightward then .right else .left))
  | 3 => some (0, .move (if rightward then .right else .left))
  | 4 => some (1, .move (if rightward then .right else .left))
  | 5 => some (2, .move (if rightward then .right else .left))
  | _ => none

def scanState (label : Fin 7) (left right : List Bool) : MachineState 6 :=
  ⟨label,Tape.mk₂ left right⟩

theorem pair_read_right (seen : Fin 3) (flag bit : Bool) (left tail : List Bool)
    (safe : safeFlag seen flag) :
    TM0.step (flagWalkMachine true) (scanState (readLabel seen) left (flag :: bit :: tail)) =
      some (scanState (moveLabel (afterSeen seen flag)) (flag :: left) (bit :: tail)) := by
  fin_cases seen <;> cases flag <;>
    simp_all [safeFlag, TM0.step, flagWalkMachine, scanState, readLabel, moveLabel, afterSeen, Tape.mk₂]

theorem pair_finish_right (seen : Fin 3) (flag bit : Bool) (left tail : List Bool) :
    TM0.step (flagWalkMachine true) (scanState (moveLabel seen) (flag :: left) (bit :: tail)) =
      some (scanState (readLabel seen) (bit :: flag :: left) tail) := by
  fin_cases seen <;>
    simp [TM0.step, flagWalkMachine, scanState, readLabel, moveLabel, Tape.mk₂]

theorem pair_read_left (seen : Fin 3) (flag bit : Bool) (left tail : List Bool)
    (safe : safeFlag seen flag) :
    TM0.step (flagWalkMachine false) (scanState (readLabel seen) (bit :: left) (flag :: tail)) =
      some (scanState (moveLabel (afterSeen seen flag)) left (bit :: flag :: tail)) := by
  fin_cases seen <;> cases flag <;>
    simp_all [safeFlag, TM0.step, flagWalkMachine, scanState, readLabel, moveLabel, afterSeen, Tape.mk₂]

theorem pair_finish_left (seen : Fin 3) (flag bit next : Bool) (left tail : List Bool) :
    TM0.step (flagWalkMachine false) (scanState (moveLabel seen) (next :: left) (bit :: flag :: tail)) =
      some (scanState (readLabel seen) left (next :: bit :: flag :: tail)) := by
  fin_cases seen <;>
    simp [TM0.step, flagWalkMachine, scanState, readLabel, moveLabel, Tape.mk₂]

def rightWalkTrace (seen : Fin 3) (left : List Bool) :
    List (Bool × Bool) → List Bool → List (MachineState 6)
  | [], suffix => [scanState (readLabel seen) left suffix]
  | (flag,bit) :: later, suffix =>
      [scanState (readLabel seen) left (flag :: bit :: (navigationCells later ++ suffix)),
        scanState (moveLabel (afterSeen seen flag)) (flag :: left)
          (bit :: (navigationCells later ++ suffix))] ++
        rightWalkTrace (afterSeen seen flag) (bit :: flag :: left) later suffix

theorem rightWalk_head (seen : Fin 3) (left : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (rightWalkTrace seen left pairs suffix).head? =
      some (scanState (readLabel seen) left (navigationCells pairs ++ suffix)) := by
  cases pairs with
  | nil => rfl
  | cons pair later =>
    obtain ⟨flag,bit⟩ := pair
    simp only [rightWalkTrace, navigationCells_cons, List.cons_append, List.head?_cons]

theorem rightWalk_last (seen : Fin 3) (left : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (rightWalkTrace seen left pairs suffix).getLast? =
      some (scanState (readLabel (seenAfter seen pairs)) ((navigationCells pairs).reverse ++ left) suffix) := by
  induction pairs generalizing seen left with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨flag,bit⟩ := pair
    simp only [rightWalkTrace, List.cons_append, List.nil_append, List.getLast?_cons,
      ih, Option.getD_some, seenAfter, navigationCells_cons, List.reverse_cons, List.append_assoc]

theorem rightWalk_chain (seen : Fin 3) (left : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool)
    (safe : safeNavigation seen pairs) :
    (rightWalkTrace seen left pairs suffix).IsChain
      (fun before after => TM0.step (flagWalkMachine true) before = some after) := by
  induction pairs generalizing seen left with
  | nil => exact .singleton _
  | cons pair later ih =>
    obtain ⟨flag,bit⟩ := pair
    change safeFlag seen flag ∧ safeNavigation (afterSeen seen flag) later at safe
    apply List.IsChain.append
    · simp [List.isChain_cons_cons, pair_read_right seen flag bit left _ safe.1]
    · exact ih _ _ safe.2
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      rw [rightWalk_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      exact pair_finish_right _ _ _ _ _

theorem rightWalk_length (seen : Fin 3) (left : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (rightWalkTrace seen left pairs suffix).length = 2 * pairs.length + 1 := by
  induction pairs generalizing seen left with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨flag,bit⟩ := pair
    simp only [rightWalkTrace, List.length_append, List.length_cons, List.length_nil, ih]
    omega

def tripleRightTrace (left : List Bool) (first second : Bool) (suffix : List Bool) :
    List (MachineState 6) :=
  [scanState 0 left (true :: first :: true :: second :: true :: suffix),
    scanState 4 (true :: left) (first :: true :: second :: true :: suffix),
    scanState 1 (first :: true :: left) (true :: second :: true :: suffix),
    scanState 5 (true :: first :: true :: left) (second :: true :: suffix),
    scanState 2 (second :: true :: first :: true :: left) (true :: suffix),
    scanState 6 (second :: true :: first :: true :: left) (true :: suffix)]

theorem triple_right_runsFrom (left : List Bool) (first second : Bool) (suffix : List Bool) :
    RunsFrom (flagWalkMachine true)
      (scanState 0 left (true :: first :: true :: second :: true :: suffix))
      (tripleRightTrace left first second suffix)
      (scanState 6 (second :: true :: first :: true :: left) (true :: suffix)) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [tripleRightTrace, List.isChain_cons_cons, TM0.step, flagWalkMachine, scanState, Tape.mk₂]
  · simp [TM0.step, flagWalkMachine, scanState]

theorem triple_right_length (left : List Bool) (first second : Bool) (suffix : List Bool) :
    (tripleRightTrace left first second suffix).length = 6 := rfl

theorem rightWalk_space (seen : Fin 3) (left : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool)
    (inputLength clock : Nat) :
    visitedSpace (flagWalkMachine true) inputLength ((rightWalkTrace seen left pairs suffix).take clock) ≤
      inputLength + 4 * pairs.length + 3 := by
  have cells := PSTRTMTrace002.visitedSpace_le (flagWalkMachine true) inputLength
    ((rightWalkTrace seen left pairs suffix).take clock)
  have count : ((rightWalkTrace seen left pairs suffix).take clock).length ≤ 2 * pairs.length + 1 := by
    simp only [List.length_take, rightWalk_length]
    omega
  omega

/-! The opposite physical direction uses the same fixed seven-label
transition table with LEFT chosen statically. Empty left tails are handled
by the real blank cell, rather than by deleting/resetting the tape. -/

def leftFront (seen : Fin 3) (stream right : List Bool) : MachineState 6 :=
  scanState (readLabel seen) stream.tail (stream.headD false :: right)

theorem pair_finish_left_stream (seen : Fin 3) (flag bit : Bool) (stream right : List Bool) :
    TM0.step (flagWalkMachine false) (scanState (moveLabel seen) stream (bit :: flag :: right)) =
      some (leftFront seen stream (bit :: flag :: right)) := by
  fin_cases seen <;> cases stream <;>
    simp [leftFront, TM0.step, flagWalkMachine, scanState, readLabel, moveLabel, Tape.mk₂]

def leftWalkTrace (seen : Fin 3) (older : List Bool) :
    List (Bool × Bool) → List Bool → List (MachineState 6)
  | [], suffix => [leftFront seen older suffix]
  | (flag,bit) :: later, suffix =>
      [scanState (readLabel seen) (bit :: (navigationCells later ++ older)) (flag :: suffix),
        scanState (moveLabel (afterSeen seen flag)) (navigationCells later ++ older) (bit :: flag :: suffix)] ++
        leftWalkTrace (afterSeen seen flag) older later (bit :: flag :: suffix)

theorem leftWalk_head (seen : Fin 3) (older : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (leftWalkTrace seen older pairs suffix).head? =
      some (leftFront seen (navigationCells pairs ++ older) suffix) := by
  cases pairs with
  | nil => rfl
  | cons pair later =>
    obtain ⟨flag,bit⟩ := pair
    simp only [leftWalkTrace, navigationCells_cons, List.cons_append, List.head?_cons, leftFront,
      List.tail_cons, List.headD_cons]

theorem leftWalk_last (seen : Fin 3) (older : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (leftWalkTrace seen older pairs suffix).getLast? =
      some (leftFront (seenAfter seen pairs) older ((navigationCells pairs).reverse ++ suffix)) := by
  induction pairs generalizing seen suffix with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨flag,bit⟩ := pair
    simp only [leftWalkTrace, List.cons_append, List.nil_append, List.getLast?_cons,
      ih, Option.getD_some, seenAfter, navigationCells_cons, List.reverse_cons, List.append_assoc]

theorem leftWalk_chain (seen : Fin 3) (older : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool)
    (safe : safeNavigation seen pairs) :
    (leftWalkTrace seen older pairs suffix).IsChain
      (fun before after => TM0.step (flagWalkMachine false) before = some after) := by
  induction pairs generalizing seen suffix with
  | nil => exact .singleton _
  | cons pair later ih =>
    obtain ⟨flag,bit⟩ := pair
    change safeFlag seen flag ∧ safeNavigation (afterSeen seen flag) later at safe
    apply List.IsChain.append
    · simp [List.isChain_cons_cons, pair_read_left seen flag bit _ suffix safe.1]
    · exact ih _ _ safe.2
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      rw [leftWalk_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      exact pair_finish_left_stream _ _ _ _ _

theorem leftWalk_length (seen : Fin 3) (older : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (leftWalkTrace seen older pairs suffix).length = 2 * pairs.length + 1 := by
  induction pairs generalizing seen suffix with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨flag,bit⟩ := pair
    simp only [leftWalkTrace, List.length_append, List.length_cons, List.length_nil, ih]
    omega

def tripleLeftTrace (older : List Bool) (first second : Bool) (suffix : List Bool) :
    List (MachineState 6) :=
  [scanState 0 (first :: true :: second :: true :: older) (true :: suffix),
    scanState 4 (true :: second :: true :: older) (first :: true :: suffix),
    scanState 1 (second :: true :: older) (true :: first :: true :: suffix),
    scanState 5 (true :: older) (second :: true :: first :: true :: suffix),
    scanState 2 older (true :: second :: true :: first :: true :: suffix),
    scanState 6 older (true :: second :: true :: first :: true :: suffix)]

theorem triple_left_runsFrom (older : List Bool) (first second : Bool) (suffix : List Bool) :
    RunsFrom (flagWalkMachine false)
      (scanState 0 (first :: true :: second :: true :: older) (true :: suffix))
      (tripleLeftTrace older first second suffix)
      (scanState 6 older (true :: second :: true :: first :: true :: suffix)) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [tripleLeftTrace, List.isChain_cons_cons, TM0.step, flagWalkMachine, scanState, Tape.mk₂]
  · simp [TM0.step, flagWalkMachine, scanState]

theorem triple_left_length (older : List Bool) (first second : Bool) (suffix : List Bool) :
    (tripleLeftTrace older first second suffix).length = 6 := rfl

theorem leftWalk_space (seen : Fin 3) (older : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool)
    (inputLength clock : Nat) :
    visitedSpace (flagWalkMachine false) inputLength ((leftWalkTrace seen older pairs suffix).take clock) ≤
      inputLength + 4 * pairs.length + 3 := by
  have cells := PSTRTMTrace002.visitedSpace_le (flagWalkMachine false) inputLength
    ((leftWalkTrace seen older pairs suffix).take clock)
  have count : ((leftWalkTrace seen older pairs suffix).take clock).length ≤ 2 * pairs.length + 1 := by
    simp only [List.length_take, leftWalk_length]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLaneScan
