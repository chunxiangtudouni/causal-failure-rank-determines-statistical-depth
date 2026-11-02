module

public import Common.PSTR_SYM_PairedNaturalBackward_037

/-! Candidate in-place Rat record compactor, reusing the original A17
parsed fields. This changes only internal flag storage, not the original
input/output codec. The complete parsed-entry/backward proof is still a
next dependency; the actual forward and sign phases are proved locally. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive

open Turing PSTRTMSeq005

def zeroPairs (digits : List Bool) : List Bool := digits.flatMap (fun bit => [false,bit])

theorem zeroPairs_cons (bit : Bool) (later : List Bool) :
    zeroPairs (bit :: later) = false :: bit :: zeroPairs later := by
  simp only [zeroPairs, List.flatMap_cons, List.cons_append, List.nil_append]

def rationalWord (negative : Bool) (numerator : List Bool) (firstDen : Bool)
    (laterDen : List Bool) : List Bool :=
  false :: negative :: (zeroPairs numerator ++ true :: firstDen :: (zeroPairs laterDen ++ [true,true]))

def rationalCompactMachine : Machine 31 := fun label symbol =>
  match label.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .write true)
  | 2 => some (3, .move .left)
  | 3 => some (4, .move .left)
  | 4 => some (5, .move .left)
  | 5 => if symbol then some (6, .write false) else some (8, .write true)
  | 6 => some (7, .move .left)
  | 7 => some (5, .move .left)
  | 8 => some (9, .move .left)
  | 9 => if symbol then some (10, .move .left) else some (17, .move .left)
  | 10 => some ((if symbol then 12 else 11), .write false)
  | 11 => some (13, .move .right)
  | 12 => some (14, .move .right)
  | 13 => some (15, .write false)
  | 14 => some (15, .write true)
  | 15 => some (16, .move .left)
  | 16 => some (9, .move .left)
  | 17 => some ((if symbol then 19 else 18), .write false)
  | 18 => some (20, .move .right)
  | 19 => some (21, .move .right)
  | 20 => some (22, .write false)
  | 21 => some (22, .write true)
  | 22 => some (23, .move .left)
  | 23 => some (24, .move .right)
  | 24 => some (25, .move .right)
  | 25 => if symbol then some (27, .move .right) else some (26, .move .right)
  | 26 => some (25, .move .right)
  | 27 => some (28, .move .right)
  | 28 => if symbol then some (30, .move .right) else some (29, .move .right)
  | 29 => some (28, .move .right)
  | 30 => some (31, .move .right)
  | _ => none

def ratState (label : Fin 32) (left right : List Bool) : MachineState 31 :=
  ⟨label,Tape.mk₂ left right⟩

theorem rationalCompact_halt (left right : List Bool) :
    TM0.step rationalCompactMachine (ratState 31 left right) = none := by
  simp [TM0.step, rationalCompactMachine, ratState]

def denReturnTrace (left : List Bool) : List Bool → List Bool → List (MachineState 31)
  | [], suffix => [ratState 28 left (true :: true :: suffix),
      ratState 30 (true :: left) (true :: suffix), ratState 31 (true :: true :: left) suffix]
  | bit :: later, suffix =>
      [ratState 28 left (false :: bit :: (zeroPairs later ++ true :: true :: suffix)),
        ratState 29 (false :: left) (bit :: (zeroPairs later ++ true :: true :: suffix))] ++
        denReturnTrace (bit :: false :: left) later suffix

def denReturnFinal (left digits suffix : List Bool) : MachineState 31 :=
  ratState 31 (true :: true :: ((zeroPairs digits).reverse ++ left)) suffix

theorem denReturn_head (left digits suffix : List Bool) :
    (denReturnTrace left digits suffix).head? =
      some (ratState 28 left (zeroPairs digits ++ true :: true :: suffix)) := by
  cases digits with
  | nil => rfl
  | cons bit later =>
    simp only [denReturnTrace, zeroPairs_cons, List.cons_append, List.head?_cons]

theorem denReturn_last (left digits suffix : List Bool) :
    (denReturnTrace left digits suffix).getLast? = some (denReturnFinal left digits suffix) := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [denReturnTrace, List.getLast?_cons, ih, Option.getD_some, denReturnFinal,
      zeroPairs_cons, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem denReturn_chain (left digits suffix : List Bool) :
    (denReturnTrace left digits suffix).IsChain
      (fun before after => TM0.step rationalCompactMachine before = some after) := by
  induction digits generalizing left with
  | nil =>
    simp [denReturnTrace, List.isChain_cons_cons, TM0.step, rationalCompactMachine, ratState, Tape.mk₂]
  | cons bit later ih =>
    apply List.IsChain.append
    · simp [List.isChain_cons_cons, TM0.step, rationalCompactMachine, ratState, Tape.mk₂]
    · exact ih _
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      rw [denReturn_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      simp [TM0.step, rationalCompactMachine, ratState, Tape.mk₂]

theorem denReturn_runsFrom (left digits suffix : List Bool) :
    RunsFrom rationalCompactMachine (ratState 28 left (zeroPairs digits ++ true :: true :: suffix))
      (denReturnTrace left digits suffix) (denReturnFinal left digits suffix) :=
  ⟨denReturn_head _ _ _, denReturn_chain _ _ _, denReturn_last _ _ _, rationalCompact_halt _ _⟩

theorem denReturn_length (left digits suffix : List Bool) :
    (denReturnTrace left digits suffix).length = 2 * digits.length + 3 := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [denReturnTrace, List.length_append, List.length_cons, List.length_nil, ih]
    omega

def numReturnTrace (left : List Bool) :
    List Bool → Bool → List Bool → List Bool → List (MachineState 31)
  | [], firstDen, laterDen, suffix =>
      [ratState 25 left (true :: firstDen :: (zeroPairs laterDen ++ true :: true :: suffix)),
        ratState 27 (true :: left) (firstDen :: (zeroPairs laterDen ++ true :: true :: suffix))] ++
        denReturnTrace (firstDen :: true :: left) laterDen suffix
  | bit :: later, firstDen, laterDen, suffix =>
      [ratState 25 left (false :: bit :: (zeroPairs later ++ true :: firstDen ::
        (zeroPairs laterDen ++ true :: true :: suffix))),
        ratState 26 (false :: left) (bit :: (zeroPairs later ++ true :: firstDen ::
          (zeroPairs laterDen ++ true :: true :: suffix)))] ++
        numReturnTrace (bit :: false :: left) later firstDen laterDen suffix

def numReturnFinal (left numerator : List Bool) (firstDen : Bool) (laterDen suffix : List Bool) :
    MachineState 31 :=
  denReturnFinal (firstDen :: true :: ((zeroPairs numerator).reverse ++ left)) laterDen suffix

theorem numReturn_head (left numerator : List Bool) (firstDen : Bool) (laterDen suffix : List Bool) :
    (numReturnTrace left numerator firstDen laterDen suffix).head? =
      some (ratState 25 left (zeroPairs numerator ++ true :: firstDen ::
        (zeroPairs laterDen ++ true :: true :: suffix))) := by
  cases numerator with
  | nil => rfl
  | cons bit later =>
    simp only [numReturnTrace, zeroPairs_cons, List.cons_append, List.head?_cons]

theorem numReturn_last (left numerator : List Bool) (firstDen : Bool) (laterDen suffix : List Bool) :
    (numReturnTrace left numerator firstDen laterDen suffix).getLast? =
      some (numReturnFinal left numerator firstDen laterDen suffix) := by
  induction numerator generalizing left with
  | nil =>
    simp only [numReturnTrace, List.getLast?_append, denReturn_last, Option.some_or,
      numReturnFinal, zeroPairs, List.flatMap_nil, List.reverse_nil, List.nil_append]
  | cons bit later ih =>
    simp only [numReturnTrace, List.getLast?_cons, ih, Option.getD_some, numReturnFinal,
      zeroPairs_cons, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem numReturn_chain (left numerator : List Bool) (firstDen : Bool) (laterDen suffix : List Bool) :
    (numReturnTrace left numerator firstDen laterDen suffix).IsChain
      (fun before after => TM0.step rationalCompactMachine before = some after) := by
  induction numerator generalizing left with
  | nil =>
    apply List.IsChain.append
    · simp [List.isChain_cons_cons, TM0.step, rationalCompactMachine, ratState, Tape.mk₂]
    · exact denReturn_chain _ _ _
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      rw [denReturn_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      simp [TM0.step, rationalCompactMachine, ratState, Tape.mk₂]
  | cons bit later ih =>
    apply List.IsChain.append
    · simp [List.isChain_cons_cons, TM0.step, rationalCompactMachine, ratState, Tape.mk₂]
    · exact ih _
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      rw [numReturn_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      simp [TM0.step, rationalCompactMachine, ratState, Tape.mk₂]

theorem numReturn_runsFrom (left numerator : List Bool) (firstDen : Bool) (laterDen suffix : List Bool) :
    RunsFrom rationalCompactMachine (ratState 25 left (zeroPairs numerator ++ true :: firstDen ::
      (zeroPairs laterDen ++ true :: true :: suffix)))
      (numReturnTrace left numerator firstDen laterDen suffix)
      (numReturnFinal left numerator firstDen laterDen suffix) :=
  ⟨numReturn_head _ _ _ _ _, numReturn_chain _ _ _ _ _, numReturn_last _ _ _ _ _, rationalCompact_halt _ _⟩

theorem numReturn_length (left numerator : List Bool) (firstDen : Bool) (laterDen suffix : List Bool) :
    (numReturnTrace left numerator firstDen laterDen suffix).length =
      2 * (numerator.length + laterDen.length) + 5 := by
  induction numerator generalizing left with
  | nil =>
    simp only [numReturnTrace, List.length_append, List.length_cons, List.length_nil, denReturn_length]
    omega
  | cons bit later ih =>
    simp only [numReturnTrace, List.length_append, List.length_cons, List.length_nil, ih]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive
